#include "gadgets.h"

#include "uart.h"
#include "stdint.h"
#include "random.h"
#include "lib.h"

#define N LM_N

void fillbuff(uint32_t buffer[], uint32_t len)
{
    randombytes((uint8_t *)buffer, len * sizeof(uint32_t));
}

__MASKING_TEST(test_sharing)
{
    uint32_t mr = rand();
    lm_share_t shared;
    uint32_t randomness[LM_RAND_SHARE];
    fillbuff(randomness, LM_RAND_SHARE);
    lm_share(shared, mr);
    int res1 = lm_reconstruct(shared) == mr;
    lm_share_derand(shared, mr, randomness);
    int res2 = lm_reconstruct(shared) == mr;
    return res1 && res2;
}

__MASKING_TEST(test_refresh)
{
    uint32_t mr = rand();
    lm_share_t shared, sharedref, sharedref2, logref;
    uint32_t rand[LM_RAND_REF];
    fillbuff(rand, LM_RAND_REF);

    lm_share(shared, mr);
    lm_ref_derand(sharedref, shared, rand);
    lm_ref(sharedref2, shared);

    // lm_logref(logref, shared);
    lm_ref(logref, shared);

    return lm_reconstruct(sharedref) == mr 
        && lm_reconstruct(sharedref2) == mr
        && lm_reconstruct(logref) == mr;
}

__MASKING_TEST(test_secand)
{
    uint32_t r[LM_RAND_AND];
    fillbuff(r, LM_RAND_AND);
    uint32_t a, b, c;
    a = rand();
    b = rand();
    c = a & b;

    lm_share_t sa, sb, sc1, sc2;
    lm_share(sa, a);
    lm_share(sb, b);

    lm_and(sc1, sa, sb);
    lm_and_derand(sc2, sa, sb, r);

    return lm_reconstruct(sc1) == c && lm_reconstruct(sc2) == c;
}

/*
__MASKING_TEST(test_secadd)
{
    uint32_t a, b, c;
    lm_share_t sa, sb, sc;
    a = rand();
    b = rand();
    lm_share(sa, a);
    lm_share(sb, b);

    lm_share_t scres;
    lm_share(scres, a + b);
    lm_share(scres, a + b);

    lm_seca(sc, sa, sb);
    c = lm_reconstruct(sc);
    return c == a + b;
}
*/

int keccac_tests(void);
uint32_t get_bytes_of_randomness_used();
int tests(void)
{
    uint32_t failures = 0;
    print("Running tests: (");
    print_uint(__TEST_RERUNS);
    print(" iterations at order ");
    print_uint(LM_N - 1);
    print(")\n");
    failures =
        !test_sharing()
      + !test_secand()
      + !test_refresh()
      + keccac_tests();
      // + !test_secadd()

    if (failures == 1) {
        print("There is 1 failed test!\n");
    } else if (failures) {
        print("There are ");
        print_uint(failures);
        print(" failed tests!\n");
    } else {
        print("All tests succeeded :)\n");
    }
    print("In total, we used ~");
    print_uint(get_bytes_of_randomness_used());
    print(" Bytes of randomness.\n");
    return failures ? EXIT_FAILURE : EXIT_SUCCESS;
}


int test_main(void)
{
    if(!LM_ASSERT_CORRECT_ORDER) {
        print("Error: Gadgets were compiled with order ");
        print_uint(lm_get_order());
        print(" while test suite was compiled with order ");
        print_uint(LM_N - 1);
        println(".");
        return -1;
    }
    const int res = tests();
    println("");
    return res;
}
