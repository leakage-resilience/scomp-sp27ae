#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "pico/stdlib.h"
#include "pico/time.h"
#include "pico/bootrom.h"
#include "gadgets.h"

#ifdef USE_JASMIN
#  define IMPL "jasmin"
   static inline void benchmark_iteration(void *s) { lm_keccakf1600(s); }
#else
#  define IMPL "c"
   void c_keccak_f1600(void *state);
   static inline void benchmark_iteration(void *s) { c_keccak_f1600(s); }
#endif

#define ITERATIONS 1000

int main() {
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
    stdio_init_all();

    for (int i = 0; i < 4; i++) {
        gpio_put(PICO_DEFAULT_LED_PIN, i & 1);
        sleep_ms(250);
    }

    if(! LM_ASSERT_CORRECT_ORDER) {
        sleep_ms(1000);
        printf("Error: Libmasking compiled with incorrect order!");
        sleep_ms(100);
        rom_reset_usb_boot(0, 0);
        return 1;
    }

    uint32_t state[50 * LM_N];
    memset(state, 0, sizeof(state));

    const absolute_time_t start = get_absolute_time();
    for (int i = 0; i < ITERATIONS; i++)
        benchmark_iteration(state);
    const absolute_time_t end = get_absolute_time();

    const int64_t elapsed = absolute_time_diff_us(start, end);
    printf(IMPL " order=%d  n=%d  total=%lld us  avg=%.1f us\n",
           LM_ORDER, ITERATIONS, elapsed, (double)elapsed / ITERATIONS);

    gpio_put(PICO_DEFAULT_LED_PIN, 0);
    sleep_ms(100);
    rom_reset_usb_boot(0, 0);
}
