#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
genmc_bin="${GENMC_BIN:-}"

if [[ -z "$genmc_bin" ]]; then
  if command -v genmc >/dev/null 2>&1; then
    genmc_bin="$(command -v genmc)"
  elif [[ -x "$project_dir/../.tools/genmc/genmc" ]]; then
    genmc_bin="$project_dir/../.tools/genmc/genmc"
  fi
fi

if [[ -z "$genmc_bin" || ! -x "$genmc_bin" ]]; then
  echo "GenMC was not found; bounded weak-memory checks were skipped."
  echo "After installation, run GENMC_BIN=/absolute/path/to/genmc ./run_genmc.sh."
  exit 0
fi

echo "GenMC: publication"
"$genmc_bin" "$project_dir/genmc/publication.c"

echo "GenMC: two-thread Treiber"
"$genmc_bin" "$project_dir/genmc/treiber_two_threads.c"
