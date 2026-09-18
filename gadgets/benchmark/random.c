#include <stdint.h>
#include <stddef.h>
#include <string.h>

uint8_t *__jasmin_syscall_randombytes__(uint8_t *buf, size_t len) {
    memset(buf, 0, len);
    return buf;
}
