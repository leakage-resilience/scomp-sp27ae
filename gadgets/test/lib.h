#ifndef _LIB_H
#define _LIB_H

#include <stddef.h>
#include <stdint.h>

void print(const char *s);
void println(const char *s);
void print_uint(uint32_t n);

void hex(char out[9], uint32_t x);
void print_hex(uint32_t x);

void *memcpy(void *dest, const void *src, size_t n);
void *memset(void *s, int c, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);

void qemu_exit(int retcode);

#define EXIT_SUCCESS (0)
#define EXIT_FAILURE (1)


#ifndef __TEST_RERUNS
#define __TEST_RERUNS 10
#endif

int __masking_test_run_test(int (*tf)(void), const char* tname);

#define __MASKING_TEST(TEST_FUNCTION) \
    int __masking_test_inner_##TEST_FUNCTION(void);               \
    int TEST_FUNCTION(void) {                                     \
        return __masking_test_run_test(                           \
            __masking_test_inner_##TEST_FUNCTION,                 \
            #TEST_FUNCTION                                        \
        );                                                        \
    }                                                             \
    int __masking_test_inner_##TEST_FUNCTION(void)

#endif
