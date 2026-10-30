#!/bin/sh
# Translates set.mm through predicate calculus and checks the result,
# listing the theorems that fail.
# Usage: xlat_pred.sh path/to/set.mm out.gh
cd "$(dirname "$0")"
cargo build -q --release || exit 1
(cd .. && cargo build -q --release) || exit 1
./target/release/mm_xlat script "$1" "$2" > /dev/null || exit 1
../target/release/ghilbert -q -k "$2"
