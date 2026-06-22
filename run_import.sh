#!/usr/bin/env bash
# Import an evidence model into a descriptor and assert success.
set -euo pipefail
bin="$1"; ev="$2"
exec "$bin" import "$ev" --out "${TEST_TMPDIR:-/tmp}/imported.sei.json"
