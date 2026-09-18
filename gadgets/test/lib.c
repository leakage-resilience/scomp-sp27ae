#include "lib.h"
#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t n) {
    char *d = dest;
    const char *s = src;
    while (n--) {
        *d++ = *s++;
    }
    return dest;
}

void *memset(void *s, int c, size_t n) {
    unsigned char *p = s;
    while (n--) {
        *p++ = (unsigned char)c;
    }
    return s;
}

int memcmp(const void *s1, const void *s2, size_t n) {
    const uint8_t *a = s1;
    const uint8_t *b = s2;
    while(n--) {
        if(*a != *b) {
            return *a - *b;
        };
        a++; b++;
    }
    return 0;
}

int __masking_test_run_test(int (*const tf)(void), const char* tname) {
    print("    Running test ");
    print(tname);
    print("...");
    int res = 1;     
    for(int i = 0; res && i < __TEST_RERUNS; i++) {     
        res &= tf();   
    }     
    println(res ? " OK" : " FAILURE");
    return res;     

}
