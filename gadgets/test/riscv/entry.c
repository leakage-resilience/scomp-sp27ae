#include "stdint.h"

static volatile int *uart = (int *)(void *)0x10000000;

void uart_write(char c) {
    while (uart[0] & (1 << 31)) {}
    uart[0] = c;
}

__attribute__((noreturn)) 
extern void qemu_exit(int);

int test_main(void);
void entry()
{
    int retcode = test_main();
    qemu_exit(retcode);
    __builtin_unreachable();
}