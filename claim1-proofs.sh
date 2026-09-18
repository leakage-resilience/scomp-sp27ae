#!/bin/sh
# THIS SCRIPT ASSUMES THAT YOU ARE IN THE DEVSHELL OR IN THE CONTAINER
cd "$(dirname "$0")/proofs" || exit 1
dune build
status=$?
echo "Ran with exit code $status"
exit $status
