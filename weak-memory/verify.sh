#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_bin="$project_dir/../.tools/lean-4.32.2-linux/bin"

if [[ ! -x "$lean_bin/lake" ]]; then
  echo "Local Lean installation not found: $lean_bin/lake" >&2
  exit 1
fi

echo "C11 Treiber tests"
make -C "$project_dir/c" test

echo "Lean proofs"
export PATH="$lean_bin:$PATH"
cd "$project_dir"
lake build
lake exe weakMemoryDemo

echo "GenMC bounded RC11 checks"
"$project_dir/run_genmc.sh"
