#!/usr/bin/env bash
# Drive the Sony ROM with checkpoint chaining.
# Usage: ./tools/sony_drive.sh [start_checkpoint]
#   If start_checkpoint is given, resume from it; otherwise start fresh.
# Produces checkpoints in /tmp/sony_cp_<N>.json and prints progress.

set -euo pipefail

SEI="./bazel-bin/sei_cli"
DESC="packages/sony/sony_main_16.sei.json"
ROM="/home/ubuntu/shadowrealm/sony_main_16.bin"
IMG="sony_main_16.bin=$ROM"
FUEL=500000
CPDIR="/tmp/sony_cps"
mkdir -p "$CPDIR"

START_CP="${1:-}"
STEP=0

# If resuming, get the step number from filename
if [[ -n "$START_CP" && "$START_CP" =~ cp_([0-9]+)\.json ]]; then
    STEP="${BASH_REMATCH[1]}"
fi

prev_cp="$START_CP"

for i in $(seq 1 8); do
    step=$((STEP + i))
    out_cp="$CPDIR/cp_${step}.json"

    echo ""
    echo "=== Step $step: fuel=$FUEL ==="

    if [[ -z "$prev_cp" ]]; then
        $SEI "$DESC" --image "$IMG" \
            --fuel "$FUEL" --fast \
            --checkpoint-out "$out_cp" \
            --trace-tail 15
    else
        $SEI "$DESC" \
            --checkpoint-in "$prev_cp" \
            --fuel "$FUEL" --fast \
            --checkpoint-out "$out_cp" \
            --trace-tail 15
    fi

    # Extract lastPc from output
    prev_cp="$out_cp"

    # Stop on halt or unsupported
    # (The step loop will just continue; user reviews manually)
done
echo ""
echo "Done. Checkpoints in $CPDIR/"
