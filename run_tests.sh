#!/bin/sh
# Runs each case in tests/pass and tests/fail on top of the preludes.
cd "$(dirname "$0")"
cargo build -q 2>/dev/null || exit 1
status=0
tmp=$(mktemp)
for f in tests/pass/*.gh tests/fail/*.gh; do
    cat tests/prelude_prop.gh tests/prelude_pred.gh "$f" > "$tmp"
    out=$(timeout 20 ./target/debug/ghilbert -d "$tmp" 2>&1)
    err=$(echo "$out" | grep -E "^err:|panicked" | head -1)
    case "$f" in
        tests/pass/*) if [ -n "$err" ]; then echo "FAIL (should pass) $f: $err"; status=1; else echo "ok   $f"; fi ;;
        tests/fail/*) if [ -z "$err" ]; then echo "FAIL (should fail) $f"; status=1; else echo "ok   $f: $err"; fi ;;
    esac
done
exit $status
