#!/bin/bash

set -e

# export TIMECMD="time -f \t%es\t%P"

if [[ "${1##*.}" == "c" ]]; then
    dune exec -- refinedc check "$1"
    cd "$(dirname $1)/proofs/$(basename $1 .c)"
    dune build --display short
else
    dune build --display short "$@"
fi
