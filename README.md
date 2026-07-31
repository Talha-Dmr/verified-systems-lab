# Mathematics Research Workspace

This repository contains formal verification work in theoretical computer
science. The weak-memory project is centered on `MSC 68Q85` and `68Q60`;
the verified-compiler project is centered on `MSC 68N20`.

## Projects

- [`verified-compiler`](verified-compiler/README.md): A verified compiler from
  a small expression language to a stack machine.
- [`weak-memory`](weak-memory/README.md): Lean proofs for weak-CAS progress,
  lock-free concurrent algorithms, RC11 execution models, and classical
  Herlihy–Wing linearizability, including Treiber and a reclamation-free
  multi-location Michael--Scott queue under a site-indexed progress theory.
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

The script checks the hash-pinned Clang 18 source descriptor locally,
synchronizes source files without `.git`, local toolchains, or build artifacts,
then runs the C tests, Lean proofs, and GenMC checks remotely. This split keeps
the descriptor tied to the pinned local Clang while using the faster host for
the expensive verification. It uses the `math-msi` SSH alias by default.
Override the target without changing the script:

```bash
REMOTE_VERIFY_HOST=other-host \
REMOTE_VERIFY_DIR=Projects/math \
./scripts/remote_verify.sh
```
