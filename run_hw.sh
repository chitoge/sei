#!/usr/bin/env bash
# Run the Lean descriptor-ingestion binary on the given .sei.json descriptors.
set -euo pipefail
bin="$1"; shift
exec "$bin" "$@"
