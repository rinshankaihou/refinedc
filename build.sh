#!/bin/bash

set -e

FILE="$1"

# use time if available
if env time -f "\t%es\t%P" echo >/dev/null 2>/dev/null; then
   export TIMECMD="time -f \t%es\t%P"
fi

if [[ "${FILE##*.}" == "c" ]]; then
    opam exec -- dune exec -- refinedc check "$FILE"
    cd "$(dirname $FILE)/proofs/$(basename $FILE .c)"
    if [[ -f "generated_proof_$2.v" ]]; then
        echo "Building" "$(pwd)/generated_proof_$2.vo"
        opam exec -- dune build --display short "generated_proof_$2.vo"
    else
        echo "Building" "$FILE"
        opam exec -- dune build --display short
    fi
else if [[ "${FILE##*.}" == "v" ]]; then
    echo "Building" "${FILE}o"
    opam exec -- dune build --display short $(realpath --relative-to=. "${FILE}o")
else
    echo "Running make"
    opam exec -- make
fi fi
