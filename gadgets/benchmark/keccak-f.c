#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include "gadgets.h"

extern uint8_t *__jasmin_syscall_randombytes__(uint8_t *buf, size_t len);

#ifndef USE_JASMIN

uint32_t bg_reconstruct(const lm_share_t shares) {
    uint32_t acc = shares[0];
    for (int i = 1; i < LM_N; i++) acc ^= shares[i];
    return acc;
}

void bg_xor(lm_share_t c, const lm_share_t a, const lm_share_t b) {
    for (int i = 0; i < LM_N; i++) c[i] = a[i] ^ b[i];
}

void bg_xor_inplace(lm_share_t c, const lm_share_t a) {
    for (int i = 0; i < LM_N; i++) c[i] ^= a[i];
}

void bg_and(lm_share_t c, const lm_share_t a, const lm_share_t b) {
    uint32_t rand[LM_RAND_AND];
    __jasmin_syscall_randombytes__((uint8_t *)rand, sizeof(rand));
    int r = 0;
    for (int i = 0; i < LM_N; i++) c[i] = a[i] & b[i];
    for (int i = 0; i < LM_N; i++)
        for (int j = i + 1; j < LM_N; j++) {
            uint32_t r_ij = rand[r++];
            c[i] ^= r_ij ^ (a[i] & b[j]) ^ (a[j] & b[i]);
            c[j] ^= r_ij;
        }
}

void bg_ref(lm_share_t c, const lm_share_t a) {
    lm_share_t one = {0};
    one[0] = 0xFFFFFFFFu;
    bg_and(c, a, one);
}

void bg_share(lm_share_t c, uint32_t x) {
    __jasmin_syscall_randombytes__((uint8_t *)c, (LM_N - 1) * sizeof(uint32_t));
    for (int i = 0; i < LM_N - 1; i++) x ^= c[i];
    c[LM_N - 1] = x;
}

typedef struct { lm_share_t upper; lm_share_t lower; } lane_t;
typedef lane_t state_t[25];

static void lane_xor(lane_t *z, const lane_t *a, const lane_t *b) {
    bg_xor(z->upper, a->upper, b->upper);
    bg_xor(z->lower, a->lower, b->lower);
}

static void lane_xor_inplace(lane_t *z, const lane_t *a) {
    bg_xor_inplace(z->upper, a->upper);
    bg_xor_inplace(z->lower, a->lower);
}

static void lane_and(lane_t *z, const lane_t *a, const lane_t *b) {
    bg_and(z->upper, a->upper, b->upper);
    bg_and(z->lower, a->lower, b->lower);
}

static void lane_not_inplace(lane_t *x) {
    x->upper[0] = ~x->upper[0];
    x->lower[0] = ~x->lower[0];
}

#define rotl(x, s) (((x) << (s)) | ((x) >> (64 - (s))))

static void lane_rol(lane_t *r, const lane_t *c, int n) {
    for (int i = 0; i < LM_N; i++) {
        uint64_t g = (uint64_t)c->upper[i] << 32 | c->lower[i];
        g = rotl(g, n);
        r->upper[i] = g >> 32;
        r->lower[i] = g & 0xFFFFFFFF;
    }
}

static const uint8_t KECCAK_RHO[24] = {
     1,  3,  6, 10, 15, 21, 28, 36, 45, 55,  2, 14,
    27, 41, 56,  8, 25, 43, 62, 18, 39, 61, 20, 44,
};
static const uint8_t KECCAK_PI[24] = {
    10,  7, 11, 17, 18,  3,  5, 16,  8, 21, 24,  4,
    15, 23, 19, 13, 12,  2, 20, 14, 22,  9,  6,  1,
};
static const uint64_t KECCAK_RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL,
};

static void keccak1600_round(lane_t *a, int i) {
    lane_t b[5], buf;
    int x, y;

    memset(b, 0, sizeof(b));
    for (x = 0; x < 5; x++)
        for (y = 0; y < 5; y++)
            lane_xor_inplace(&b[x], &a[x + y*5]);

    for (x = 0; x < 5; x++) {
        lane_rol(&buf, &b[(x + 1) % 5], 1);
        lane_xor_inplace(&buf, &b[(x + 4) % 5]);
        for (y = 0; y < 5; y++)
            lane_xor_inplace(&a[x + y*5], &buf);
    }

    memcpy(&buf, &a[1], sizeof(lane_t));
    for (x = 0; x < 24; x++) {
        memcpy(&b[0], &a[KECCAK_PI[x]], sizeof(lane_t));
        lane_rol(&a[KECCAK_PI[x]], &buf, KECCAK_RHO[x]);
        memcpy(&buf, &b[0], sizeof(lane_t));
    }

    for (y = 0; y < 5; y++) {
        for (x = 0; x < 5; x++)
            memcpy(&b[x], &a[x + y*5], sizeof(lane_t));
        for (x = 0; x < 5; x++) {
            lane_not_inplace(&b[(x + 1) % 5]);
            lane_and(&a[x + y*5], &b[(x + 1) % 5], &b[(x + 2) % 5]);
            lane_xor_inplace(&a[x + y*5], &b[x]);
            lane_not_inplace(&b[(x + 1) % 5]);
        }
    }

    a[0].upper[0] ^= KECCAK_RC[i] >> 32;
    a[0].lower[0] ^= KECCAK_RC[i] & 0xFFFFFFFF;
}

void c_keccak_f1600(void *state) {
    lane_t *a = (lane_t *)state;
    for (int i = 0; i < 24; i++)
        keccak1600_round(a, i);
}

#endif
