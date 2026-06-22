#!/usr/bin/env bash
# Completeness regression vs ARM's BSD AARCHMRS A32 encoding index: assert the
# decoder still decodes the supported instructions and fail-closes the rest
# (at most TOL silent mismatches — the 1 known is an UNPREDICTABLE LDRD).
set -euo pipefail
bin="$1"; corpus="$2"; tol="${3:-1}"
out="$("$bin" "$corpus" --stats --dump 2>&1 || true)"
echo "$out" | grep -E 'decoded & correct|MISMATCH:|not decoded'
mis=$(echo "$out" | sed -nE 's/.*MISMATCH: ([0-9]+).*/\1/p' | head -1)
cor=$(echo "$out" | sed -nE 's/.*decoded & correct : ([0-9]+).*/\1/p' | head -1)
echo "completeness: correct=$cor silent_mismatch=$mis tolerance=$tol"
[ "$mis" -le "$tol" ] || { echo "FAIL: $mis silent mis-decodes > $tol"; exit 1; }
[ "$cor" -ge 200 ] || { echo "FAIL: only $cor decoded-correct"; exit 1; }
echo "arm_completeness: PASS"
