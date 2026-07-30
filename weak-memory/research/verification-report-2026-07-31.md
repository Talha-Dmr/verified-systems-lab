# Verification Report — 2026-07-31

## Snapshot identity

- Repository: `Talha-Dmr/verified-systems-lab`
- Branch: `main`
- Parent commit:
  `8bd56e9af3edd81e9643715720c5aec6ac0e04aa`
- Verified snapshot: the Git commit containing this report
- Snapshot status: committed and fully verified from a clean clone

The exact immutable identifier is the commit containing this file, obtainable
with `git rev-parse HEAD` in the release checkout and recorded by the GitHub
commit page. Embedding that identifier in this report would change the commit
itself, so the report identifies the snapshot by containment rather than by a
self-referential hash.

## Toolchain

- Lean: 4.32.2,
  commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`
- Source-boundary Clang: Ubuntu Clang 18.1.3
- GenMC: 0.17.0, commit `29b03a6`, built with LLVM 18.1.3
- Host timezone: Europe/Istanbul

## Local full verification

Command:

```bash
./verify.sh
```

Result: passed.

- Source extraction: committed JSON and Lean descriptors exactly matched the
  Clang 18.1.3 AST.
- Pinned source hashes:
  - `c/treiber.c`:
    `7a0ef93f9510ae71873d930f7e06a8bb36416a6b33587a814fe779c3b5e56d13`
  - `c/treiber.h`:
    `0f32a0ca76a95891308662143e609c6da03eab49c7254b8ce058fd464ff2d882`
- Native sequential test: passed.
- Native four-thread stress test: 80,000 nodes pushed and popped exactly once.
- Lean full build: 186 jobs passed.
- Public theorem surface target:
  `WeakMemory.WeakCASTreiberResult` passed.
- Demo executable: passed.
- GenMC publication harness: 2 complete executions, no errors.
- GenMC two-thread Treiber harness: 20 complete and 10 blocked executions, no
  errors.
- Relinche one-push/one-pop harness: 2 executions and 1 checked hint, no
  errors.

The GenMC checks remain bounded validation. GenMC 0.17.0 does not explore
equal-value spurious weak-CAS failures; the Lean all-spurious theorem is the
unbounded proof covering that dimension.

## Clean-clone verification

After the snapshot was committed, it was cloned with Git's `--no-local`
option into a fresh directory and the complete `./verify.sh` workflow was
repeated there. The clean-clone run passed the source-descriptor comparison,
native C tests, all 186 Lean jobs, the public theorem-surface builds, the demo,
and every GenMC/Relinche check listed above.

## Independent MSI build

The exact local source tree, excluding `.git`, local build products, and
`.lake`, was copied to a fresh isolated MSI directory:

```text
/tmp/weak-cas-publication.lNiM2y/weak-memory
```

Command:

```bash
/home/talha/Projects/math/.tools/lean-4.32.2-linux/bin/lake build
```

Result: all 186 jobs passed from the isolated source copy using Lean 4.32.2.
The directory is temporary evidence, not a permanent release location.

## Formal surface and axiom audit

The compact entry point is
`WeakMemory/WeakCASTreiberResult.lean`. Its checked results include:

- `genericAllSpuriousSeparation`;
- `treiberAllSpuriousSeparation`;
- `counterResponseProgress`;
- `treiberSystemResponseProgress_of_fromReadFairness`;
- `treiberSystemResponseProgress_of_memoryFairness`;
- `treiberLinearizableLongRun_of_fromReadFairness`; and
- `positiveAssumptionsJointlySatisfiable`.

`#print axioms` reports only standard imported Lean axioms:

```text
propext
Classical.choice
Quot.sound
```

`git diff --check` passed. A word-boundary scan of the result modules found no
`sorry`, `admit`, project `axiom`, or `unsafe` declaration.

## Adversarial definition audit

An independent read-only proof audit found no blocker in the positive
implication. The checked dependency chain is:

```text
no later response
  -> no successful CAS
  -> one stable finite-prefix MO tail
  -> prefix-finite fr eventually exposes that tail
  -> thread fairness and retry control give matching attempts
  -> primitive weak-CAS justice contradicts the no-success suffix
  -> some method responds
```

The audit confirmed these claim boundaries:

- the result is system-wide lock-freedom, not per-operation starvation
  freedom or wait-freedom;
- safety means Herlihy--Wing linearizability of every finite prefix, not one
  selected coherent infinite linearization;
- the exact positive proof consumes prefix-finite `fr`; paired
  prefix-finite `mo`/`fr` memory fairness is a conventional corollary;
- the generic `ProgressRule` is single-site and system-wide, not yet a
  site-indexed multi-location rule;
- the success-rich witness proves joint satisfiability but does not exercise a
  difficult justice premise; and
- the integrated all-spurious Treiber/RC11 carrier is the genuine independence
  result.

## Remaining release gates

Before attaching this report to a public claim:

1. obtain review by an external weak-memory/concurrency expert;
2. repeat the primary-source search at submission time; and
3. archive the toolchains or container used by the artifact.
