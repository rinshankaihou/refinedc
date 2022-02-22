#!/bin/bash

set -e

# use time if available
if env time -f "\t%es\t%P" echo >/dev/null 2>/dev/null; then
   export TIMECMD="time -f \t%es\t%P"
fi

if [[ "${1##*.}" == "c" ]]; then
    dune exec -- refinedc check "$1"
    cd "$(dirname $1)/proofs/$(basename $1 .c)"
    dune build --display short
else
    make
fi
