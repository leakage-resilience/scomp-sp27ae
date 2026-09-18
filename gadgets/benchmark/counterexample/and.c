#include <stdint.h>

#ifndef LM_ORDER
#define LM_ORDER 1
#endif
#define LM_N        (LM_ORDER + 1)
#define LM_RAND_AND (LM_N * (LM_N - 1) / 2)

typedef uint32_t lm_share_t[LM_N];

#define N (LM_N)

// All counterexamples found using
//   gcc (Arm GNU Toolchain 15.2.Rel1 (Build arm-15.86)) 15.2.1 20251203
// and
//   scVerif   51527c9a1e6e037fc2a61e800a0352e5c2c7498c
//   maskverif d25612bfe788c45affa4091f51a81634d14f1a17

// Secure at -O1..-O3
/*
void bg_and_derand(
    uint32_t c[restrict 2],
    const uint32_t a[2],
    const uint32_t b[2],
    const uint32_t rand[restrict 1]
) {
    const uint32_t r = *rand;
    c[0] = a[0] & b[0];
    c[1] = a[1] & b[1];
    c[0] ^= r;
    c[1] ^= (a[0] & b[1]) ^ r;
    c[1] ^= a[1] & b[0];
}
*/

// Breaks t-probing security at -O1..-O3!!
/*
void bg_and_derand(
    uint32_t c[restrict 2],
    const uint32_t a[2],
    const uint32_t b[2],
    const uint32_t rand[restrict 1]
) {
    c[0] = a[0] & b[0];
    c[1] = a[1] & b[1];
    const uint32_t r = *rand;
    c[0] ^= r;
    c[1] ^= (a[0] & b[1]) ^ r;
    c[1] ^= a[1] & b[0];
}
*/

// Breaks t-probing security -O3!!
// Ok at -O0 and -O2, not parsable by scverif at -O1.
/*
void bg_and_derand(
    uint32_t c[restrict N],
    const uint32_t a[N],
    const uint32_t b[N],
    const uint32_t rand[N * (N - 1) / 2]
) {
    for (int i = 0; i < N; i++)
        c[i] = a[i] & b[i];

    for (int i = 0; i < N; i++) {
        for (int j = i + 1; j < N; j++) {
            const uint32_t r = *rand++;
            c[i] ^= r;
            c[j] ^= (a[i] & b[j]) ^ r;
            c[j] ^= a[j] & b[i];
        }
    }
}
*/


// Breaks t-SNI on -O1, -O2, -O3 (at N=2)
void bg_and_derand(
    lm_share_t c,
    const lm_share_t a,
    const lm_share_t b,
    const uint32_t rand[LM_RAND_AND]
) {
    uint32_t x, y, r_ij, tmp;
    int rc = 0;

    for (int i = 0; i < LM_N; i++) {
        x = a[i];
        y = b[i];
        x = x & y;
        c[i] = x;
    }

    for (int i = 0; i < LM_N; i++) {
        for (int j = i + 1; j < LM_N; j++) {
            r_ij = rand[rc];
            rc++;

            x = c[i];
            x = x ^ r_ij;
            c[i] = x;

            x = a[i];
            y = b[j];
            x = x & y;
            x = x ^ r_ij;

            y = a[j];
            tmp = b[i];
            y = y & tmp;

            x = x ^ y;

            y = c[j];
            x = x ^ y;

            c[j] = x;
        }
    }
}

// Breaks t-SNI on -O1
// Ok on -O0 and -O2
// Breaks t-probing on -O3
// (at N=2)
/*
void bg_and_derand(
    uint32_t c[restrict N],
    const uint32_t a[N],
    const uint32_t b[N],
    const uint32_t rand[restrict N * (N - 1) / 2]
) {
    uint32_t x, y, r_ij, tmp;
    int rc = 0;

    for (int i = 0; i < LM_N; i++) {
        x = a[i];
        y = b[i];
        x = x & y;
        c[i] = x;
    }

    for (int i = 0; i < LM_N; i++) {
        for (int j = i + 1; j < LM_N; j++) {
            r_ij = rand[rc];
            rc++;

            x = c[i];
            x = x ^ r_ij;
            c[i] = x;

            x = a[i];
            y = b[j];
            x = x & y;
            x = x ^ r_ij;

            y = a[j];
            tmp = b[i];
            y = y & tmp;

            x = x ^ y;

            y = c[j];
            x = x ^ y;

            c[j] = x;
        }
    }
}
*/

void bg_ref_derand(
    lm_share_t c,
    const lm_share_t a,
    const uint32_t rand[LM_RAND_AND]
) {
    const lm_share_t one = {
        [0] = 0xFFFFFFFF,
    };
    
    bg_and_derand(c, a, one, rand);
}

void bg_xor(
    lm_share_t c,
    const lm_share_t a,
    const lm_share_t b
) {
    uint32_t x, y;
    for (int i = 0; i < LM_N; i++) {
        x = a[i];
        y = b[i];
        x = x ^ y;
        c[i] = x;
    }
}

// void bg_xor_trans(
//     lm_share_t c,
//     const lm_share_t a,
//     const lm_share_t b
// ) {
//     volatile uint32_t x, y;
//     for (int i = 0; i < LM_N; i++) {
//         x = a[i];
//         y = b[i];
//         x = x ^ y;
//         c[i] = x;
//         x = x ^ y;
//         x = 0;
//         y = 0;
//     }
// }
