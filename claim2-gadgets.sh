#!/bin/sh
# THIS SCRIPT ASSUMES THAT YOU ARE IN THE DEVSHELL OR IN THE CONTAINER
# Due to set -e, any failing command will cause the script to fail.
set -eu

echo "Cleaning stray build files for clean build"
rm -r _build

echo "Checking wether the gadgets compile for supported configurations..."
echo "This will take up to a minute"

make    -C gadgets ARCH=arm-m4 ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets ARCH=arm-m4 ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets ARCH=arm-m4 ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets ARCH=arm-m4 ORDER=4 >/dev/null 2>&1 \
&& make -C gadgets ARCH=riscv  ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets ARCH=riscv  ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets ARCH=riscv  ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets ARCH=riscv  ORDER=4 >/dev/null 2>&1

echo "Done compiling gadget libraries with exit code $?"
echo "Output binaries:"
ls _build/*/*/libmasking.a

echo "Now we are running unit tests"

make    -C gadgets test ARCH=arm-m4 ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=arm-m4 ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=arm-m4 ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=arm-m4 ORDER=4 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=riscv  ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=riscv  ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=riscv  ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets test ARCH=riscv  ORDER=4 >/dev/null 2>&1

echo "Unit tests succeeded: $?"

echo "We will now check the easycrypt proofs"

make -C gadgets extract-all
(cd gadgets/proofs \
; easycrypt why3config \
; easycrypt runtest easycrypt.project all )

echo "EasyCrypt proofs were checked."
echo "Finally, we perform security verification"

make    -C gadgets scverif-check ARCH=arm-m4 ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=arm-m4 ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=arm-m4 ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=arm-m4 ORDER=4 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=riscv  ORDER=1 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=riscv  ORDER=2 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=riscv  ORDER=3 >/dev/null 2>&1 \
&& make -C gadgets scverif-check ARCH=riscv  ORDER=4 >/dev/null 2>&1

echo "ScVerif verification succeeded: $?"

echo "All tests succeeded!"