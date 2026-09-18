#!/bin/sh
set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
GADGETS_DIR="$SCRIPT_DIR/.."

doas true

> results.txt

put() { printf '%s\n' "$@" | tee -a results.txt; }

build_libmasking() {
    echo "Building libmasking at order $1"
    make -C "$GADGETS_DIR" ORDER="$1" ARCH=arm-m4 libmasking >/dev/null 2>&1
}

build_bench() {
    echo "Building $2 impl for order $1"
    order=$1 impl=$2
    bdir="$SCRIPT_DIR/build/order${order}-${impl}"
    use_jasmin=OFF
    [ "$impl" = jasmin ] && use_jasmin=ON
    mkdir -p "$bdir"
    ORDER="$order" cmake -S "$SCRIPT_DIR" -B "$bdir" \
        -DUSE_JASMIN="$use_jasmin" \
        -DCMAKE_BUILD_TYPE=Release \
        -Wno-dev \
        >/dev/null 2>&1
    cmake --build "$bdir" --target bench -j"$(nproc)" >/dev/null 2>&1
}

flash_and_read() {
    order=$1 impl=$2
    uf2="$SCRIPT_DIR/build/order${order}-${impl}/bench.uf2"
    put "=== order=${order} impl=${impl} ==="
    doas picotool load "$uf2"
    doas picotool reboot
    until [ -e /dev/ttyACM0 ]; do sleep 0.1; done
    doas cat /dev/ttyACM0 | while read -r line; do put "$line"; done
    sleep 0.5
}

for order in 1 2 3 4; do
    build_libmasking "$order"
    for impl in jasmin c; do
        build_bench "$order" "$impl"
    done
done

for order in 1 2 3 4; do
    for impl in jasmin c; do
        flash_and_read "$order" "$impl"
    done
done

put "done"
