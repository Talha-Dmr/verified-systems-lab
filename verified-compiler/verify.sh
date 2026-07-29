#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_bin="$project_dir/../.tools/lean-4.32.2-linux/bin"

if [[ ! -x "$lean_bin/lake" ]]; then
  echo "Local Lean installation not found: $lean_bin/lake" >&2
  exit 1
fi

export PATH="$lean_bin:$PATH"
cd "$project_dir"

lake build
lake exe verifiedCompilerDemo
