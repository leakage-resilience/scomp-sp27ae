#!/bin/sh
# THIS SCRIPT ASSUMES THAT YOU ARE IN THE DEVSHELL OR IN THE CONTAINER
cd proofs && dune build
echo "Ran with exit code $?"