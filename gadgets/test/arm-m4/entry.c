#include "stdint.h"

volatile unsigned int *uart = (volatile unsigned int *)0x09000000;
void uart_write(uint8_t c) {
    while (*uart & (1 << 31)) {}
    *uart = c;
}


__attribute__((noreturn)) 
extern void qemu_exit(int retcode);

int test_main(void);
void entry()
{
    int retcode = test_main();
    qemu_exit(retcode);
    __builtin_unreachable();
}
