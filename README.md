# Mathematics Research Workspace

This repository contains formal verification work centered on
`MSC 68N20 — Theory of compilers and interpreters`.

## Projects

- [`verified-compiler`](verified-compiler/README.md): A verified compiler from
  a small expression language to a stack machine.
- [`weak-memory`](weak-memory/README.md): C11 Treiber stack experiments and
  Lean proofs connecting an RC11-style execution graph, a reclamation-free
  release-acquire operational model, and a sequential stack specification.
- [`references/msc2020`](references/msc2020/README.md): A local archive of the
  MSC2020 classification.

## Verification

```bash
./verified-compiler/verify.sh
./weak-memory/verify.sh
```

The Lean toolchain is installed locally under `.tools/` and is excluded from
Git because of its size.
