#!/bin/sh
# THIS SCRIPT ASSUMES THAT YOU ARE IN THE DEVSHELL OR IN THE CONTAINER
# no set -eu because we expect this script to fail!

make -C gadgets/benchmark/counterexample check
