#!/bin/bash

set -e

# use time if available
if env time -f "\t%es\t%P" echo >/dev/null 2>/dev/null; then
   export TIMECMD="time -f \t%es\t%P"
fi

if [[ "${1##*.}" == "c" ]]; then
    opam exec -- dune exec -- refinedc check "$1"
    cd "$(dirname $1)/proofs/$(basename $1 .c)"
    if [[ -f "generated_proof_$2.v" ]]; then
        echo "Building" "$(pwd)/generated_proof_$2.vo"
        opam exec -- dune build --display short "generated_proof_$2.vo"
    else
        echo "Building" "$1"
        opam exec -- dune build --display short
    fi
else if [[ "${1##*.}" == "v" ]]; then
    echo "Building" "$1o"
    opam exec -- dune build --display short $(realpath --relative-to=. "$1o")
else
    echo "Running make"
    opam exec -- make
fi fi
