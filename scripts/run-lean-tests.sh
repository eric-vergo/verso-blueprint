#!/usr/bin/env bash

set -euo pipefail

package_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$package_root"

# A kernel replay that accepts records that it did in a file; the tests' own go to a scratch
# folder, never to the user's cache.
replay_record_dir="$(mktemp -d)"
trap 'rm -rf "$replay_record_dir"' EXIT
export VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD="$replay_record_dir/kernel-replay-checkers.json"

./scripts/lean-low-priority lake test
./scripts/lean-low-priority lake build vbp
python3 tests/integration/check_source_schema.py
python3 tests/integration/check_lean_run_external_markup.py
python3 tests/integration/check_embedded_asset_cache.py
python3 tests/integration/check_vbp_failure_protocol.py
