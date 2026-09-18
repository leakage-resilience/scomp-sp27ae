#include "uart.h"
#include "lib.h"

void print(const char *s)
{
    while(*s != '\0') {
        uart_write(*s++);
    }
}

void println(const char *s) {
    print(s);
    uart_write('\n');
}

void print_uint(uint32_t n)
{
    char buf[16];
    uint32_t r;

    buf[15] = '\0';
    char *ptr = buf+14;
    
    if (!n)
        *ptr-- = '0';

    while (n) {
        r = n % 10;
        n = n / 10;
        *ptr-- = r + '0';
    }
    print(ptr + 1);
}

void hex(char out[9], uint32_t x) {
    const char *const hc = "0123456789ABCDEF";
    for(int i = 0; i < 8; i++) {
        out[7 - i] = *(hc + (x & 0xF));
        x >>= 4;
    }
    out[8] = '\0';
}

void print_hex(uint32_t x) {
    char buf[9];
    hex(buf, x);
    print(buf);
}