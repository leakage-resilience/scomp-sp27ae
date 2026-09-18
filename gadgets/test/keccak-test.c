#include "gadgets.h"
// #include "crypto.h"

#define N LM_N

#include "uart.h"
#include "stdint.h"
#include "random.h"
#include "lib.h"


void keccak_share_state(uint32_t AS[25 * 2 * N], const uint32_t A[25 * 2]) {
    for(int i = 0; i < 25 * 2; i ++) {
        lm_share(AS + (i * N), A[i]);
    }
}

void keccak_empty_state(uint32_t A[25 * 2 * N]) {
    for(int i = 0; i < 25 * 2; i ++) {
        lm_share(A + (i * N), 0);
    }
}

void keccac_rec_state(uint32_t res[25 * 2], const uint32_t A[25 * 2 * N]) {
    for(int i = 0; i < 25 * 2; i++) {
        res[i] = lm_reconstruct(A + (i * N));
    }
}

void keccac_print_state(const uint32_t rec[25 * 2]) {
    for(int y = 0; y < 5; y++) {
        for(int x = 0; x < 5; x++) {
            print_hex(rec[2 * (x + 5 * y)]);
            print_hex(rec[2 * (x + 5 * y) + 1]);
            print(" ");
        }
        println("");
    }
}

void keccac_print_shared_state(const uint32_t A[25 * 2 * N]) {
    uint32_t rec[25 * 2];
    keccac_rec_state(rec, A);
    keccac_print_state(rec);
}

// Test-vectors are taken from the public-domain "XKCP" Keccak implementation.
// https://github.com/XKCP/XKCP/blob/master/tests/TestVectors/KeccakF-1600-IntermediateValues.txt
// Ref: https://github.com/XKCP/XKCP/blob/716f007dd73ef28d357b8162173646be574ad1b7/LICENSE
const uint32_t sa_initial[25 * 2] = {
    0x80305000, 0x01E0840C, 0x38CA9830, 0x82300106, 0x08B03400, 0x41C14101, 0x20027830, 0x81A00483, 0x10488C00, 0x40D14100,
    0x00049840, 0xD3042220, 0x11932210, 0xB0700202, 0x40038E20, 0x070020F0, 0x31953040, 0xD0600010, 0x60030C30, 0x241400C2,
    0x0000A504, 0x34031950, 0x003E0038, 0x090A8080, 0xC400828E, 0x0C100043, 0x00222630, 0x21081812, 0xC41C018A, 0x18108081,
    0x01840C58, 0x0E382590, 0x3E085050, 0x01060000, 0x040C0061, 0x063A6584, 0x39801C48, 0x09030010, 0x0A084021, 0x00074184,
    0x80859C80, 0x08192199, 0xC7000800, 0x80E020E2, 0x00858480, 0x4017321C, 0x41001800, 0x08E801A1, 0x06000C00, 0xC0063266,
};

const uint32_t sa_theta[25 * 2] = {
    0x98B0590A, 0xC86D7060, 0x298A1D32, 0x7B0ED626, 0x0AB50258, 0x192BD807, 0xD8875F48, 0xF4F557EA, 0x7B161D31, 0xF07F2ADA,
    0x1884914A, 0x1A89D64C, 0x00D3A712, 0x494ED522, 0x4206B878, 0x5FEAB9F6, 0xC9101738, 0xA5355379, 0x0B5D9D01, 0x94BA6B18,
    0x1880AC0E, 0xFD8EED3C, 0x117E853A, 0xF03457A0, 0xC605B4D6, 0x54FA9945, 0xF8A70148, 0x545D4B7B, 0xAF4290BB, 0xA8BEEB5B,
    0x19040552, 0xC7B5D1FC, 0x2F48D552, 0xF838D720, 0x06093639, 0x5ED0FC82, 0xC1053B30, 0x7C565379, 0x6156D110, 0xB0A92A5E,
    0x9805958A, 0xC194D5F5, 0xD6408D02, 0x79DEF7C2, 0x0280B2D8, 0x18FDAB1A, 0xB9853F78, 0x7DBD52C8, 0x6D5E9D31, 0x70A859BC,
};

const uint32_t sa_rho[25 * 2] = {
    0x98B0590A, 0xC86D7060, 0x53143A64, 0xF61DAC4C, 0xC2AD4096, 0x064AF601, 0x8F4F557E, 0xAD8875F4, 0x8F83F956, 0xD3D8B0E9,
    0xA89D64C1, 0x884914A1, 0xED52200D, 0x3A712494, 0x81AE1E17, 0xFAAE7D90, 0xBCE4880B, 0x9C529AA9, 0xD0194BA6, 0xB180B5D9,
    0xC4056077, 0xEC7769E0, 0xFA14EBC0, 0xD15E8045, 0xD4CA2E30, 0x2DA6B2A7, 0x90A8BA96, 0xF7F14E02, 0x5F75ADD7, 0xA1485DD4,
    0x6BA3F832, 0x080AA58F, 0x1AE405E9, 0x1AAA5F07, 0x9B1CAF68, 0x7E410304, 0x660F8ACA, 0x6F3820A7, 0x56D110B0, 0xA92A5E61,
    0x562B0653, 0x57D66016, 0x59023409, 0xE77BDF0B, 0x4050165B, 0x031FB563, 0xC8B9853F, 0x787DBD52, 0xA74C5C2A, 0x166F1B57,
};

const uint32_t sa_pi[25 * 2] = {
    0x98B0590A, 0xC86D7060, 0xED52200D, 0x3A712494, 0xD4CA2E30, 0x2DA6B2A7, 0x660F8ACA, 0x6F3820A7, 0xA74C5C2A, 0x166F1B57,
    0x8F4F557E, 0xAD8875F4, 0xD0194BA6, 0xB180B5D9, 0xC4056077, 0xEC7769E0, 0x1AE405E9, 0x1AAA5F07, 0x4050165B, 0x031FB563,
    0x53143A64, 0xF61DAC4C, 0x81AE1E17, 0xFAAE7D90, 0x90A8BA96, 0xF7F14E02, 0x56D110B0, 0xA92A5E61, 0x562B0653, 0x57D66016,
    0x8F83F956, 0xD3D8B0E9, 0xA89D64C1, 0x884914A1, 0xFA14EBC0, 0xD15E8045, 0x9B1CAF68, 0x7E410304, 0xC8B9853F, 0x787DBD52,
    0xC2AD4096, 0x064AF601, 0xBCE4880B, 0x9C529AA9, 0x5F75ADD7, 0xA1485DD4, 0x6BA3F832, 0x080AA58F, 0x59023409, 0xE77BDF0B,
};

const uint32_t sa_chi[25 * 2] = {
    0x8838573A, 0xCDEBE243, 0xCF57A0C7, 0x78692494, 0x558A7A10, 0x3DE1A9F7, 0x7EBF8BCA, 0xA7384087, 0xC20E7C2F, 0x247F1FC3,
    0x8B4B752F, 0xE1FF3DD4, 0xCAF94E2E, 0xA308A3DE, 0x84157265, 0xED62C980, 0x95EB44CD, 0xB62A1F93, 0x10401CDB, 0x131F356A,
    0x43149AE4, 0xF34CAE4E, 0xC7FF1E37, 0xF2A46DF1, 0x9082BCD5, 0xA1256E14, 0x57C52894, 0x0923D229, 0xD6810240, 0x5F743186,
    0xDD837256, 0x82CE30AD, 0xA99560E9, 0xA64817A1, 0xBAB5EBD7, 0xD1623C17, 0x9C1ED728, 0xFDC103AD, 0xE8A581BE, 0x707CB952,
    0x81BC6542, 0x2742B355, 0x9C66D82B, 0x94503AA2, 0x4F75A9DE, 0x463907D4, 0xE90EB8A4, 0x080A858F, 0x6542BC00, 0x7F6BD7A3,
};

const uint32_t sa_iota[25 * 2] = {
    0x0838573A, 0x4DEB6243, 0xCF57A0C7, 0x78692494, 0x558A7A10, 0x3DE1A9F7, 0x7EBF8BCA, 0xA7384087, 0xC20E7C2F, 0x247F1FC3,
    0x8B4B752F, 0xE1FF3DD4, 0xCAF94E2E, 0xA308A3DE, 0x84157265, 0xED62C980, 0x95EB44CD, 0xB62A1F93, 0x10401CDB, 0x131F356A,
    0x43149AE4, 0xF34CAE4E, 0xC7FF1E37, 0xF2A46DF1, 0x9082BCD5, 0xA1256E14, 0x57C52894, 0x0923D229, 0xD6810240, 0x5F743186,
    0xDD837256, 0x82CE30AD, 0xA99560E9, 0xA64817A1, 0xBAB5EBD7, 0xD1623C17, 0x9C1ED728, 0xFDC103AD, 0xE8A581BE, 0x707CB952,
    0x81BC6542, 0x2742B355, 0x9C66D82B, 0x94503AA2, 0x4F75A9DE, 0x463907D4, 0xE90EB8A4, 0x080A858F, 0x6542BC00, 0x7F6BD7A3,   
};

const uint32_t sa_final[25 * 2] = {
    0xF1258F79, 0x40E1DDE7, 0x84D5CCF9, 0x33C0478A, 0xD598261E, 0xA65AA9EE, 0xBD154730, 0x6F80494D, 0x8B284E05, 0x6253D057,
    0xFF97A42D, 0x7F8E6FD4, 0x90FEE5A0, 0xA44647C4, 0x8C5BDA0C, 0xD6192E76, 0xAD30A6F7, 0x1B19059C, 0x30935AB7, 0xD08FFC64,
    0xEB5AA93F, 0x2317D635, 0xA9A6E626, 0x0D712103, 0x81A57C16, 0xDBCF555F, 0x43B831CD, 0x0347C826, 0x01F22F1A, 0x11A5569F,
    0x05E5635A, 0x21D9AE61, 0x64BEFEF2, 0x8CC970F2, 0x61367095, 0x7BC46611, 0xB87C5A55, 0x4FD00ECB, 0x8C3EE88A, 0x1CCF32C8,
    0x940C7922, 0xAE3A2614, 0x1841F924, 0xA2C509E4, 0x16F53526, 0xE70465C2, 0x75F644E9, 0x7F30A13B, 0xEAF1FF7B, 0x5CECA249,
};

const uint32_t empty[25 * 2] = { 0 };
const uint32_t sa_iota_zero[25 * 2] = { 0, 1 };


void lm_theta1600(uint32_t A[50 * N]);
void lm_rho_pi1600(uint32_t A[50 * N]);
void lm_chi1600(uint32_t A[50 * N]);
void lm_iota1600(uint32_t A[50 * N], uint32_t round);
void lm_rnd1600(uint32_t A[50 * N], uint32_t round);
// void lm_keccakf1600(uint32_t A[50 * N]);


void iota_round_0(uint32_t A[50 * N]) {
    lm_iota1600(A, 0);
}

void iota_round_3(uint32_t A[50 * N]) {
    lm_iota1600(A, 3);
}

void rnd_round_3(uint32_t A[50 * N]) {
    lm_rnd1600(A, 3);
}

#define TEST_BEFORE_AFTER(before, after, tfn) \
    { do { \
        uint32_t res[25 * 2]; \
        uint32_t s0[25 * 2 * N]; \
        keccak_share_state(s0, before); \
        tfn(s0); \
        keccac_rec_state(res, s0); \
        int errno = memcmp(res, after, sizeof(uint32_t) * 25 * 2); \
        if (errno) { \
            println("\nError: expected state"); \
            keccac_print_state(after); \
            println("\nbut got"); \
            keccac_print_state(res); \
            return 0; \
        } \
        return 1; \
    } while (0); }


__MASKING_TEST(test_theta_regression) TEST_BEFORE_AFTER(
    sa_initial,
    sa_theta,
    lm_theta1600
)

__MASKING_TEST(test_rho_pi_regression) TEST_BEFORE_AFTER(
    sa_theta,
    sa_pi,
    lm_rho_pi1600
)

__MASKING_TEST(test_chi_regression) TEST_BEFORE_AFTER(
    sa_pi,
    sa_chi,
    lm_chi1600
)

__MASKING_TEST(test_iota_regression_zero) TEST_BEFORE_AFTER(
    empty,
    sa_iota_zero,
    iota_round_0
)

__MASKING_TEST(test_iota_regression) TEST_BEFORE_AFTER(
    sa_chi,
    sa_iota,
    iota_round_3
)

__MASKING_TEST(test_rnd_regression) TEST_BEFORE_AFTER(
    sa_initial,
    sa_iota,
    rnd_round_3
)

#define DEFINE_CHECK_SHA3(BITS, OUT_WORDS) \
int check_sha3_##BITS(const uint8_t *msg, uint32_t len_words) { \
    uint8_t ref[OUT_WORDS * 4]; \
    sha3_##BITS(ref, sizeof(ref), msg, len_words * 4); \
    uint32_t shared_msg[len_words * N + 1]; \
    const uint32_t *words = (const uint32_t *)msg; \
    for (uint32_t i = 0; i < len_words; i++) lm_share(shared_msg + i * N, words[i]); \
    uint32_t output[OUT_WORDS * N]; \
    lm_sha3_##BITS((lm_share_t *)output, (lm_share_t *)shared_msg, len_words); \
    for (int i = 0; i < OUT_WORDS; i++) { \
        uint32_t word = lm_reconstruct(output + i * N); \
        if ((uint8_t)(word >>  0) != ref[4*i + 0]) return 0; \
        if ((uint8_t)(word >>  8) != ref[4*i + 1]) return 0; \
        if ((uint8_t)(word >> 16) != ref[4*i + 2]) return 0; \
        if ((uint8_t)(word >> 24) != ref[4*i + 3]) return 0; \
    } \
    return 1; \
}

DEFINE_CHECK_SHA3(224, 7)
DEFINE_CHECK_SHA3(256, 8)
DEFINE_CHECK_SHA3(384, 12)
DEFINE_CHECK_SHA3(512, 16)

__MASKING_TEST(test_sha3_224_empty)        { return check_sha3_224(NULL, 0); }
__MASKING_TEST(test_sha3_224_single_block) {
    const uint8_t msg[16] = "abcdefghijklmnop";
    return check_sha3_224(msg, 4);
}
__MASKING_TEST(test_sha3_224_multi_block)  {
    uint8_t msg[40 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_sha3_224(msg, 40);
}

__MASKING_TEST(test_sha3_256_empty)        { return check_sha3_256(NULL, 0); }
__MASKING_TEST(test_sha3_256_single_block) {
    const uint8_t msg[16] = "abcdefghijklmnop";
    return check_sha3_256(msg, 4);
}
__MASKING_TEST(test_sha3_256_multi_block)  {
    uint8_t msg[38 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_sha3_256(msg, 38);
}

__MASKING_TEST(test_sha3_384_empty)        { return check_sha3_384(NULL, 0); }
__MASKING_TEST(test_sha3_384_single_block) {
    const uint8_t msg[16] = "abcdefghijklmnop";
    return check_sha3_384(msg, 4);
}
__MASKING_TEST(test_sha3_384_multi_block)  {
    uint8_t msg[30 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_sha3_384(msg, 30);
}

__MASKING_TEST(test_sha3_512_empty)        { return check_sha3_512(NULL, 0); }
__MASKING_TEST(test_sha3_512_single_block) {
    const uint8_t msg[8] = "abcdefgh";
    return check_sha3_512(msg, 2);
}
__MASKING_TEST(test_sha3_512_multi_block)  {
    uint8_t msg[20 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_sha3_512(msg, 20);
}

#define DEFINE_CHECK_SHAKE(BITS, OUT_WORDS) \
int check_shake##BITS(const uint8_t *msg, uint32_t len_words) { \
    uint8_t ref[OUT_WORDS * 4]; \
    shake##BITS(ref, sizeof(ref), msg, len_words * 4); \
    uint32_t shared_msg[len_words * N + 1]; \
    const uint32_t *words = (const uint32_t *)msg; \
    for (uint32_t i = 0; i < len_words; i++) lm_share(shared_msg + i * N, words[i]); \
    uint32_t output[OUT_WORDS * N]; \
    lm_shake##BITS((lm_share_t *)output, (lm_share_t *)shared_msg, len_words); \
    for (int i = 0; i < OUT_WORDS; i++) { \
        uint32_t word = lm_reconstruct(output + i * N); \
        if ((uint8_t)(word >>  0) != ref[4*i + 0]) return 0; \
        if ((uint8_t)(word >>  8) != ref[4*i + 1]) return 0; \
        if ((uint8_t)(word >> 16) != ref[4*i + 2]) return 0; \
        if ((uint8_t)(word >> 24) != ref[4*i + 3]) return 0; \
    } \
    return 1; \
}

DEFINE_CHECK_SHAKE(128, 8)
DEFINE_CHECK_SHAKE(256, 16)

__MASKING_TEST(test_shake128_empty)        { return check_shake128(NULL, 0); }
__MASKING_TEST(test_shake128_single_block) {
    const uint8_t msg[16] = "abcdefghijklmnop";
    return check_shake128(msg, 4);
}
__MASKING_TEST(test_shake128_multi_block)  {
    uint8_t msg[46 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_shake128(msg, 46);
}

__MASKING_TEST(test_shake256_empty)        { return check_shake256(NULL, 0); }
__MASKING_TEST(test_shake256_single_block) {
    const uint8_t msg[16] = "abcdefghijklmnop";
    return check_shake256(msg, 4);
}
__MASKING_TEST(test_shake256_multi_block)  {
    uint8_t msg[38 * 4];
    for (int i = 0; i < (int)sizeof(msg); i++) msg[i] = (uint8_t)i;
    return check_shake256(msg, 38);
}

__MASKING_TEST(test_keccakf1600_testvector) TEST_BEFORE_AFTER (
    empty,
    sa_final,
    lm_keccakf1600
)

void keccakf(void* state);
__MASKING_TEST(test_keccakf1600) {
    uint32_t pre[50] = { 0xABCDE };
    uint32_t res[50] = { 0xABCDE };
    keccakf(res);

    TEST_BEFORE_AFTER(
        pre, res, lm_keccakf1600
    )
}

int keccac_tests(void) {
    return 0
        + !test_theta_regression()
        // + !test_rho_regression()
        // + !test_pi_regression()
        + !test_chi_regression()
        + !test_iota_regression_zero()
        + !test_iota_regression()
        + !test_rnd_regression()
        + !test_keccakf1600_testvector()
        + !test_keccakf1600()
        + !test_sha3_224_empty()
        + !test_sha3_224_single_block()
        + !test_sha3_224_multi_block()
        + !test_sha3_256_empty()
        + !test_sha3_256_single_block()
        + !test_sha3_256_multi_block()
        + !test_sha3_384_empty()
        + !test_sha3_384_single_block()
        + !test_sha3_384_multi_block()
        + !test_sha3_512_empty()
        + !test_sha3_512_single_block()
        + !test_sha3_512_multi_block()
        + !test_shake128_empty()
        + !test_shake128_single_block()
        + !test_shake128_multi_block()
        + !test_shake256_empty()
        + !test_shake256_single_block()
        + !test_shake256_multi_block();
}
