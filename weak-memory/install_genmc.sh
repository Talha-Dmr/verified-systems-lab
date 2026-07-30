#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools_dir="$project_root/.tools"

genmc_version="v0.17.0"
genmc_commit="29b03a66402c4453fc77901ef3be90bb55707cd4"
llvm_major="18"

source_dir="$tools_dir/genmc-${genmc_version}-src"
build_dir="$tools_dir/genmc-${genmc_version}-gcc-build"
llvm_deb_dir="$tools_dir/llvm${llvm_major}-debs"
llvm_root="$tools_dir/llvm${llvm_major}-root"
llvm_prefix="$llvm_root/usr/lib/llvm-${llvm_major}"
local_lib_dir="$llvm_root/usr/lib/x86_64-linux-gnu"
genmc_link_dir="$tools_dir/genmc"

required_commands=(apt-get cmake dpkg-deb g++ gcc git)
for command_name in "${required_commands[@]}"; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Required command not found: $command_name" >&2
    exit 1
  fi
done

mkdir -p "$tools_dir"

if [[ ! -x "$llvm_prefix/bin/clang" || ! -x "$llvm_prefix/bin/llvm-config" ]]; then
  llvm_packages=(
    "clang-${llvm_major}"
    "libclang-common-${llvm_major}-dev"
    "libclang-cpp${llvm_major}"
    "libclang1-${llvm_major}"
    "libedit-dev"
    "libffi-dev"
    "libllvm${llvm_major}"
    "libxml2-dev"
    "libz3-dev"
    "libzstd-dev"
    "llvm-${llvm_major}"
    "llvm-${llvm_major}-dev"
    "llvm-${llvm_major}-linker-tools"
    "llvm-${llvm_major}-runtime"
    "llvm-${llvm_major}-tools"
    "zlib1g-dev"
  )

  echo "Downloading LLVM ${llvm_major} build dependencies"
  mkdir -p "$llvm_deb_dir" "$llvm_root"
  (
    cd "$llvm_deb_dir"
    apt-get download "${llvm_packages[@]}"
  )

  shopt -s nullglob
  llvm_debs=("$llvm_deb_dir"/*.deb)
  shopt -u nullglob
  if [[ "${#llvm_debs[@]}" -eq 0 ]]; then
    echo "No Debian packages were downloaded to $llvm_deb_dir" >&2
    exit 1
  fi

  echo "Extracting LLVM ${llvm_major} locally"
  for package_file in "${llvm_debs[@]}"; do
    dpkg-deb --extract "$package_file" "$llvm_root"
  done
fi

if [[ ! -x "$llvm_prefix/bin/clang" || ! -x "$llvm_prefix/bin/llvm-config" ]]; then
  echo "The local LLVM ${llvm_major} toolchain is incomplete." >&2
  exit 1
fi

if [[ ! -d "$source_dir/.git" ]]; then
  echo "Cloning GenMC ${genmc_version}"
  git clone \
    --branch "$genmc_version" \
    --depth 1 \
    https://github.com/MPI-SWS/genmc.git \
    "$source_dir"
fi

actual_commit="$(git -C "$source_dir" rev-parse HEAD)"
if [[ "$actual_commit" != "$genmc_commit" ]]; then
  echo "Unexpected GenMC source commit: $actual_commit" >&2
  echo "Expected: $genmc_commit" >&2
  exit 1
fi

export LIBRARY_PATH="$local_lib_dir${LIBRARY_PATH:+:$LIBRARY_PATH}"
export LD_LIBRARY_PATH="$local_lib_dir:$llvm_prefix/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

echo "Configuring GenMC ${genmc_version}"
cmake \
  -S "$source_dir" \
  -B "$build_dir" \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DCMAKE_C_COMPILER="$(command -v gcc)" \
  -DCMAKE_CXX_COMPILER="$(command -v g++)" \
  -DCMAKE_PREFIX_PATH="$llvm_prefix;$llvm_root/usr" \
  -DLLVM_DIR="$llvm_prefix/cmake" \
  -DCMAKE_LIBRARY_PATH="$local_lib_dir" \
  -DCMAKE_INCLUDE_PATH="$llvm_root/usr/include;$llvm_root/usr/include/x86_64-linux-gnu" \
  -DBUILD_TESTS=OFF \
  -DENABLE_RUST=OFF

build_jobs="${GENMC_BUILD_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)}"
echo "Building GenMC with $build_jobs job(s)"
cmake --build "$build_dir" --parallel "$build_jobs"

genmc_binary="$build_dir/bin/genmc"
if [[ ! -x "$genmc_binary" ]]; then
  echo "GenMC build did not produce $genmc_binary" >&2
  exit 1
fi

mkdir -p "$genmc_link_dir"
ln -sfn "../$(basename "$build_dir")/bin/genmc" "$genmc_link_dir/genmc"

echo "Installed GenMC at $genmc_link_dir/genmc"
"$genmc_link_dir/genmc" --version
