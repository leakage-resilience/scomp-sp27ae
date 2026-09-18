#ifndef _GADGETS_H
#define _GADGETS_H

#ifndef LM_ORDER
#define LM_ORDER 1
#endif

#define LM_N (LM_ORDER + 1)

#define __LM_LOG_1(n) (((n) >= 2) ? 1 : 0)
#define __LM_LOG_2(n) (((n) >= 1<<2) ? (2 + __LM_LOG_1((n)>>2)) : __LM_LOG_1(n))
#define __LM_LOG_4(n) (((n) >= 1<<4) ? (4 + __LM_LOG_2((n)>>4)) : __LM_LOG_2(n))
#define __LM_LOG_8(n) (((n) >= 1<<8) ? (8 + __LM_LOG_4((n)>>8)) : __LM_LOG_4(n))
#define __LM_LOG(n)   (((n) >= 1<<16) ? (16 + __LM_LOG_8((n)>>16)) : __LM_LOG_8(n))

#define __LM_LOGN (__LM_LOG(LM_N))

#define LM_RAND_AND (LM_N * (LM_N - 1) / 2)
#define LM_RAND_REF (LM_RAND_AND)
#define LM_RAND_LOGREF (LM_N * __LM_LOGN)
#define LM_RAND_SHARE (LM_N - 1)

#include <stdint.h>

typedef uint32_t lm_share_t [LM_N];

uint32_t lm_reconstruct(const lm_share_t in);

void lm_xor         (lm_share_t out, const lm_share_t l, const lm_share_t r);
void lm_xor_inplace (lm_share_t l, const lm_share_t r);

void lm_not         (lm_share_t out, const lm_share_t x);
void lm_not_inplace (lm_share_t x);

void lm_shl         (lm_share_t out, const lm_share_t x, uint32_t a);
void lm_shl_inplace (lm_share_t x, uint32_t a);

void lm_shr         (lm_share_t out, const lm_share_t x, uint32_t a);
void lm_shr_inplace (lm_share_t x, uint32_t a);

void lm_rol64_1     (lm_share_t out_hi, lm_share_t out_lo,
                     const lm_share_t in_hi, const lm_share_t in_lo);

uint32_t lm_get_order();

#define LM_ASSERT_CORRECT_ORDER (lm_get_order() == LM_ORDER)

#define __LM_RAND_GADGET(fn, randomness, ...) \
    void fn(__VA_ARGS__); \
    void fn##_derand(__VA_ARGS__, const uint32_t rand[randomness]);

__LM_RAND_GADGET(lm_and,    LM_RAND_AND,    lm_share_t out, const lm_share_t l, const lm_share_t r)
__LM_RAND_GADGET(lm_ref,    LM_RAND_REF,    lm_share_t out, const lm_share_t x)
// __LM_RAND_GADGET(lm_logref, LM_RAND_LOGREF, lm_share_t out, const lm_share_t x)
__LM_RAND_GADGET(lm_share,  LM_RAND_SHARE,  lm_share_t out, uint32_t in)

#define LM_KECCAKF_STATE_WORDS (50 * LM_N)
uint32_t *lm_keccakf1600(uint32_t state[LM_KECCAKF_STATE_WORDS]);

// Output sizes in masked u32 words
#define LM_SHA3_224_WORDS   7
#define LM_SHA3_256_WORDS   8
#define LM_SHA3_384_WORDS  12
#define LM_SHA3_512_WORDS  16
#define LM_SHAKE128_WORDS   8 // 256-bits
#define LM_SHAKE256_WORDS  16 // 512-bits

void lm_sha3_224(lm_share_t output[LM_SHA3_224_WORDS], const lm_share_t *txt, uint32_t len);
void lm_sha3_256(lm_share_t output[LM_SHA3_256_WORDS], const lm_share_t *txt, uint32_t len);
void lm_sha3_384(lm_share_t output[LM_SHA3_384_WORDS], const lm_share_t *txt, uint32_t len);
void lm_sha3_512(lm_share_t output[LM_SHA3_512_WORDS], const lm_share_t *txt, uint32_t len);
void lm_shake128(lm_share_t output[LM_SHAKE128_WORDS], const lm_share_t *txt, uint32_t len);
void lm_shake256(lm_share_t output[LM_SHAKE256_WORDS], const lm_share_t *txt, uint32_t len);

#endif