ARM_GCC_PREFIX ?= arm-none-eabi-
CC      = $(ARM_GCC_PREFIX)gcc
OBJDUMP = $(ARM_GCC_PREFIX)objdump

OPT ?= -O1

CFLAGS = $(OPT) -mcpu=cortex-m4 -mthumb -mlittle-endian \
		-ffreestanding -fno-builtin -nostartfiles -DLM_ORDER=1 \
		-Wall -Wpedantic

VERIFY      = ../../verify
POSTPROCESS = ../../postprocess-objdump.py

.PHONY: *

all: and.lst

and.o: and.c
	$(CC) $(CFLAGS) -c $< -o $@

and.lst: and.o
	$(OBJDUMP) -dS $< | python3 $(POSTPROCESS) > $@

check: and.lst
	scverif \
		-v 0 \
		--il $(VERIFY)/arm-m4-isa.il \
		--il $(VERIFY)/arm-m4-leakage.il \
		--asm and.lst \
		--il and.il

clean:
	-rm -f and.o and.lst
