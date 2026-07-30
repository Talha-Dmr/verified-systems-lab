# Mathematics Research Workspace

This repository contains formal verification work centered on
`MSC 68N20 — Theory of compilers and interpreters`.

## Projects

- [`verified-compiler`](verified-compiler/README.md): A verified compiler from
  a small expression language to a stack machine.
- [`weak-memory`](weak-memory/README.md): C11 Treiber stack experiments and
  Lean proofs connecting a hash-pinned C source descriptor, executable finite
  RC11-model validators, a reclamation-free release-acquire operational model,
  and classical Herlihy–Wing linearizability.
- [`references/msc2020`](references/msc2020/README.md): A local archive of the
  MSC2020 classification.

## Verification

```bash
./verified-compiler/verify.sh
./weak-memory/verify.sh
```

The Lean and GenMC toolchains are installed locally under `.tools/` and are
excluded from Git because of their size. The pinned GenMC build can be
recreated with:

```bash
./weak-memory/install_genmc.sh
```

## Remote Verification

Source editing and Git operations stay in the local workspace, while builds
and verification can run on a stronger SSH host:

```bash
./scripts/remote_verify.sh
./scripts/remote_verify.sh verified-compiler
./scripts/remote_verify.sh all
```

The script synchronizes source files without `.git`, local toolchains, or build
artifacts, then runs the selected verification command remotely. It uses the
`math-msi` SSH alias by default. Override the target without changing the
script:

```bash
REMOTE_VERIFY_HOST=other-host \
REMOTE_VERIFY_DIR=Projects/math \
./scripts/remote_verify.sh
```
