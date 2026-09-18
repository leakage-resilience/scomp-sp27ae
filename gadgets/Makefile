ORDER ?= 1
ARCH ?= arm-m4

BUILD ?= ../_build/$(ARCH)/order$(ORDER)

ARM_GCC_PREFIX ?= arm-none-eabi-
RISCV_GCC_PREFIX ?= riscv32-none-elf-

JASMINCFLAGS += -wall

CFLAGS += \
	-Wall \
	-Wpedantic \
	-O2 \
	-fno-builtin \
	-nostartfiles

N = $(shell echo $$(( $(ORDER) + 1 )))
LOG_N = $(shell python -c "print(int(__import__('math').log2(${N})))")

ifeq ($(ARCH), arm-m4)
	GCC_PREFIX ?= $(ARM_GCC_PREFIX)
	JASMINCFLAGS += -arch $(ARCH)
	MCPU ?= cortex-a15
	ASFLAGS += -mcpu=${MCPU}
	CFLAGS += -ffreestanding \
		-fno-builtin -nostartfiles \
		-mcpu=${MCPU} -mlittle-endian -mthumb
	LDFLAGS += -nostdlib
else ifeq ($(ARCH), riscv)
	GCC_PREFIX ?= $(RISCV_GCC_PREFIX)
	JASMINCFLAGS += -arch $(ARCH) -call-conv linux
	ASFLAGS += -mabi=ilp32
	CFLAGS += -mabi=ilp32 -mcmodel=medany -static -fvisibility=hidden
	LDFLAGS +=
else
	$(error unsupported ARCH)
endif

JASMINC ?= jasminc

CC = $(GCC_PREFIX)gcc
AS = $(GCC_PREFIX)as
LD = $(GCC_PREFIX)ld
OBJCOPY = $(GCC_PREFIX)objcopy
OBJDUMP = $(GCC_PREFIX)objdump

SRC = ./src
SRC_FILES = $(wildcard $(SRC)/*.jinc) $(wildcard $(SRC)/*.jazz)
LM_GADGETS_SRC = $(SRC)/libmasking-gadgets.jazz
LM_GADGETS_O = $(BUILD)/libmasking-gadgets.jazz.s.o
LM_GADGETS_LST = $(BUILD)/libmasking-gadgets.jazz.s.o.lst
LM_OBJS = $(LM_GADGETS_O) $(BUILD)/libmasking-sha3.jazz.s.o

TEST = ./test

LM_CONSTANTS = $(BUILD)/libmasking_constants/constants.jinc

JASMIN_INCLUDES = \
	-I libmasking_constants=$(BUILD)/libmasking_constants \
	-I libmasking_arch=$(SRC)/$(ARCH)

JASMINCFLAGS +=  -auto-spill $(JASMIN_INCLUDES)

.PHONY: all
all: libmasking # libmasking-check scverif-check

.PHONY: clean
clean:
	@echo "Cleaning"
	-rm -rf $(BUILD)/libmasking_constants
	-rm -rf $(BUILD)/test
	-rm $(BUILD)/*
	-rmdir $(BUILD)

.PHONY: cleanall
cleanall: clean
	-rm -rf ../_build

# ------------------------------------------------------------------------------
#                                Gadget Libaray
# ------------------------------------------------------------------------------

.PHONY: libmasking
libmasking: $(BUILD)/libmasking.a
	@echo "Output at $<"

.PHONY: libmasking-check
libmasking-check: $(LM_CONSTANTS) $(LM_GADGETS_SRC)
	$(JASMINC) $(JASMINCFLAGS) -checksafety $(LM_GADGETS_SRC)

logref : $(BUILD)/logref.jazz.s

.PHONY: $(LM_CONSTANTS)
$(LM_CONSTANTS):
	@mkdir -p $(@D)
	> $@
	echo "param int ORDER = ${ORDER}; " >> $@
	echo "param int N = ${ORDER} + 1; " >> $@
	echo "param int LOG_N = ${LOG_N}; " >> $@

$(BUILD)/%.jazz.s: src/%.jazz $(SRC_FILES) $(LM_CONSTANTS)
	@mkdir -p $(@D)
	$(JASMINC) $(JASMINCFLAGS) $< -o $@

%.s.o: %.s
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) $< -o $@

$(BUILD)/libmasking.a: $(LM_OBJS)
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

# ScVerif export
%.o.lst: %.o
	$(OBJDUMP) -dS $< \
	| python postprocess-objdump.py \
	> $@

# ------------------------------------------------------------------------------
#                                   ScVerif
# ------------------------------------------------------------------------------

.PHONY: scverif-check
scverif-check: $(LM_GADGETS_LST)
	ORDER=$(ORDER) sh ./verify/$(ARCH)-gen > $(BUILD)/annotations.il
	scverif \
		--il verify/$(ARCH)-isa.il \
		--il verify/$(ARCH)-leakage.il \
		--asm $(LM_GADGETS_LST) \
		--il $(BUILD)/annotations.il \
		--il verify/check.il

# ------------------------------------------------------------------------------
#                                  EasyCrypt
# ------------------------------------------------------------------------------

.PHONY: extract
extract: $(LM_GADGETS_SRC) $(LM_CONSTANTS) $(SRC_FILES)
	jasmin2ec $(JASMIN_INCLUDES) \
		--array-model=warray \
		--arch=$(ARCH) \
		--cc=linux \
		--output-array=proofs/array-theories \
		-o proofs/extracted/Order${ORDER}.ec \
		$(LM_GADGETS_SRC)

extract-all:
	ORDER=1 make extract
	ORDER=2 make extract
	ORDER=3 make extract
	ORDER=4 make extract

# ------------------------------------------------------------------------------
#                                   Tests
# ------------------------------------------------------------------------------


TEST_BUILD ?= $(BUILD)/test
TEST_SOURCES = $(wildcard $(TEST)/*.c)
TEST_ARCH_DEPENDENT_SOURCES = $(TEST)/$(ARCH)/entry.c $(TEST)/$(ARCH)/flash.s
TEST_OBJS = $(patsubst $(TEST)/%,$(TEST_BUILD)/%.o, $(TEST_SOURCES) $(TEST_ARCH_DEPENDENT_SOURCES))

LD_SCRIPT = $(TEST)/$(ARCH)/linker.ld


.PHONY: testenv
testenv: $(TEST_BUILD)/test.bin

.PHONY: test-arm-m4
test-arm-m4: testenv
	qemu-system-arm \
		-cpu cortex-a15 \
		-M virt \
		-m 4G \
		-nographic -no-reboot -semihosting \
		-kernel $(TEST_BUILD)/test.bin

.PHONY: test-riscv
test-riscv: testenv
	qemu-system-riscv32 \
		-M virt \
		-m 4G \
		-nographic -no-reboot -semihosting \
		-bios none \
		-kernel $(TEST_BUILD)/test.bin

.PHONY: test
test: test-$(ARCH)

$(TEST_BUILD)/%.c.o: $(TEST)/%.c
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -Itest -I. -DLM_ORDER=$(ORDER) -c $^ -o $@

$(TEST_BUILD)/%.s.o: $(TEST)/%.s
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) $^ -o $@

%.bin: %.elf
	@mkdir -p $(@D)
	$(OBJCOPY) -O binary $^ $@

$(TEST_BUILD)/test.elf: $(TEST_OBJS) $(BUILD)/libmasking.a
	@mkdir -p $(@D)
	$(LD) -T $(LD_SCRIPT) $(LDFLAGS) -o $@ $^
