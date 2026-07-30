#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
remote_host="${REMOTE_VERIFY_HOST:-math-msi}"
remote_dir="${REMOTE_VERIFY_DIR:-Projects/math}"
suite="${1:-weak-memory}"

case "$suite" in
  weak-memory)
    verify_commands=("./weak-memory/verify.sh")
    ;;
  verified-compiler)
    verify_commands=("./verified-compiler/verify.sh")
    ;;
  all)
    verify_commands=(
      "./verified-compiler/verify.sh"
      "./weak-memory/verify.sh"
    )
    ;;
  *)
    echo "Usage: $0 [weak-memory|verified-compiler|all]" >&2
    exit 2
    ;;
esac

if [[ ! "$remote_dir" =~ ^[A-Za-z0-9._/-]+$ ]]; then
  echo "REMOTE_VERIFY_DIR contains unsupported characters: $remote_dir" >&2
  exit 2
fi

for command_name in rsync ssh; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Required command not found: $command_name" >&2
    exit 1
  fi
done

ssh_options=(
  -o BatchMode=yes
  -o ConnectTimeout=8
  -o ServerAliveInterval=30
  -o ServerAliveCountMax=3
)

if ! ssh "${ssh_options[@]}" "$remote_host" \
  "test -d '$remote_dir/.git'"; then
  echo "Remote repository not found: $remote_host:$remote_dir" >&2
  exit 1
fi

echo "Synchronizing source files to $remote_host:$remote_dir"
rsync \
  --archive \
  --compress \
  --human-readable \
  --itemize-changes \
  --exclude '/.git/' \
  --exclude '/.tools/' \
  --exclude '/verified-compiler/.lake/' \
  --exclude '/weak-memory/.lake/' \
  --exclude '/weak-memory/build/' \
  -e "ssh ${ssh_options[*]}" \
  "$project_root/" \
  "$remote_host:$remote_dir/"

for verify_command in "${verify_commands[@]}"; do
  echo "Running on $remote_host: $verify_command"
  ssh "${ssh_options[@]}" "$remote_host" \
    "cd '$remote_dir' && time $verify_command"
done
