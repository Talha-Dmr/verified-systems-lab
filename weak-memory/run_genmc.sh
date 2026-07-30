#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
genmc_bin="${GENMC_BIN:-}"
runtime_lib_dir="$project_dir/../.tools/genmc-runtime-libs"

if [[ -d "$runtime_lib_dir" ]]; then
  export LD_LIBRARY_PATH="$runtime_lib_dir${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi

if [[ -z "$genmc_bin" ]]; then
  if [[ -x "$project_dir/../.tools/genmc/genmc" ]]; then
    genmc_bin="$project_dir/../.tools/genmc/genmc"
  elif command -v genmc >/dev/null 2>&1; then
    genmc_bin="$(command -v genmc)"
  fi
fi

if [[ -z "$genmc_bin" || ! -x "$genmc_bin" ]]; then
  echo "GenMC was not found; bounded weak-memory checks cannot run." >&2
  echo "Install the pinned local build with ./weak-memory/install_genmc.sh." >&2
  echo "Alternatively, set GENMC_BIN=/absolute/path/to/genmc." >&2
  exit 1
fi

echo "GenMC version"
"$genmc_bin" --version

echo "GenMC: publication"
"$genmc_bin" --rc11 --disable-estimation "$project_dir/genmc/publication.c"

echo "GenMC: two-thread Treiber"
"$genmc_bin" --rc11 --disable-estimation "$project_dir/genmc/treiber_two_threads.c"

echo "GenMC Relinche: one push and one pop"
"$genmc_bin" \
  --rc11 \
  --disable-estimation \
  --disable-mm-detector \
  --check-lin-spec="$project_dir/genmc/treiber_stack_one_push_one_pop.spec" \
  "$project_dir/genmc/treiber_relinche_one_push_one_pop.c"
