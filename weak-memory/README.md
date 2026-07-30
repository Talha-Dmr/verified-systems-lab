# 14G — Concurrent Algorithm Verification under Weak Memory

This project establishes the first verifiable foundation of the research route
using a Treiber stack without memory reclamation. The goal is not merely to
write a working stack, but to express the connection between its execution
model, sequential specification, and linearization points as explicit
theorems.

## Current Contents

- Treiber `push` and `pop` implemented with C11 atomics
- A native stress test using four threads and 80,000 distinct nodes
- Two small bounded C harnesses for GenMC
- Memory-order and execution-graph vocabulary in Lean
- A sequential stack specification and legal-history definition in Lean
- `Treiber.commitTrace_linearizable`, proving that successful abstract
  Treiber commit traces form legal sequential stack histories
- An immutable node heap, freshness condition, and successful/failed CAS steps
- `TreiberRA.allowedExecution_linearizable`, proving the linearization core for
  every execution admitted by the operational RA fragment
- `TreiberRC11.WellFormed`, collecting the current single-location graph
  conditions for `po`, `rf`, `mo`, release sequences, synchronization, and
  RMW atomicity
- `TreiberRC11.CoreConsistent`, adding reads-before, extended coherence,
  no-thin-air, and the non-SC atomic RC11 coherence condition
- `TreiberRC11.certifiedSchedule_linearizable`, composing a certified graph
  schedule with the operational RA proof
- An executable action and graph replay checker in
  `WeakMemory/TreiberReplay.lean`
- `applyAction?_eq_some_iff` and `replay?_eq_some_iff`, proving that executable
  acceptance exactly characterizes the corresponding operational judgments
- `acceptedExecution_linearizable`, closing the proof chain for graphs whose
  supplied order respects `po` and `eco` and passes deterministic replay
- `TreiberRC11.Graph.OrderEdge`, the combined `po ∪ eco` scheduling
  constraint, and `Graph.OrderAcyclic`, which rules out cycles in its
  transitive closure
- `exists_respectsGraph_of_orderAcyclic`, constructing a finite topological
  schedule and proving that it covers every event exactly once and respects
  both constituent orders
- `TreiberRC11.ReplayInvariant`, stating fresh and unique node allocation,
  immutable pop publication, an empty initial head, and genuinely stale failed
  compare-exchanges
- `replay?_eq_some_advanceUncheckedList`, deriving successful executable
  replay from a respecting order and those explicit invariants
- `linearizable_of_replayInvariant`, constructing the schedule and final state
  and proving that the resulting completed history is a legal sequential
  stack history

## Exactly What Is Proved?

The first Lean theorem covers:

```text
abstract successful CAS/load commits
              ↓
legal sequential stack history
```

The following bridge is now proved for the small operational RA model:

```text
operational RA Treiber execution
            ↓
    abstract commit trace
            ↓
 legal sequential stack history
```

In `WeakMemory/TreiberRA.lean`, nodes are immutable and enter the shared heap
only at a successful release push CAS. Pop observations are acquiring. Failed
CAS attempts are stuttering steps that do not change shared state.

The remaining source-level boundary is:

```text
C11 Treiber source / complete RC11 semantics
                    ↓ not yet proved
core-consistent graph + OrderAcyclic + ReplayInvariant
```

The current theorems establish the linearization-point core, not yet the full
Herlihy–Wing invocation/response definition. The stress test is not a proof,
and the project does not claim to verify the complete C11 semantics or the C
source directly.

The RC11-style and replay layers now prove:

```text
core-consistent finite graph
 + acyclic transitive closure of (po ∪ eco)
 + explicit Treiber ReplayInvariant
                    ↓ proved
  constructed order respecting po and eco
                    ↓ proved
       successful executable replay
                    ↓ proved
       certified operational schedule
                    ↓ proved
          legal sequential stack history
```

Executable replay is not treated as an oracle: its acceptance is proved
equivalent to the inductive operational semantics. Combined-order acyclicity
is an explicit premise: the current `CoreConsistent` fields do not silently
claim to imply it. The replay proof uses `rf`, modification-order totality,
and reads-before to show that every event observes the current head. The
remaining heap obligations are visible in `ReplayInvariant`; they are not
hidden inside a replay-success assumption.

## Model References

The definitions of reads-before (`rb`), extended coherence (`eco`),
no-thin-air, and non-SC coherence follow the atomic core presented in:

- [Lahav et al., *Repairing Sequential Consistency in C/C++11*][rc11-paper]
- [The accompanying executable `rc11.cat` model][rc11-cat]

The present Lean development intentionally formalizes only the
single-location, non-SC fragment used by this Treiber stack.

[rc11-paper]: https://plv.mpi-sws.org/scfix/full.pdf
[rc11-cat]: https://diy.inria.fr/www/weblib/rc11.cat.html

## Memory-Management Boundary

Each node is pushed only once and is neither freed nor reused after a pop.
Therefore, the current milestone intentionally excludes ABA and safe memory
reclamation. Hazard pointers or epoch-based reclamation belong to a later
research stage.

## Verification

From the repository root:

```bash
./weak-memory/verify.sh
```

The script:

1. Builds the C code with warnings treated as errors.
2. Runs the sequential and multithreaded tests.
3. Builds the Lean project so the kernel checks all theorems.
4. Runs both bounded weak-memory harnesses explicitly under RC11 with GenMC.

Install the pinned local GenMC toolchain once:

```bash
./weak-memory/install_genmc.sh
```

The bootstrap script targets Debian-based systems with Ubuntu 24.04 package
names. It downloads and extracts LLVM 18 and builds GenMC v0.17.0 entirely
under the ignored `.tools/` directory; it does not require `sudo` or modify
system packages. `verify.sh` fails instead of silently skipping the bounded
checks when GenMC is unavailable.

To use an existing GenMC installation instead:

```bash
GENMC_BIN=/absolute/path/to/genmc ./weak-memory/run_genmc.sh
```

GenMC exhaustively explores these finite harnesses, but that bounded
exploration is supporting evidence rather than a proof of the unbounded C
implementation. The Lean proof boundary described above remains unchanged.

## Next Precise Milestone

Define a typed or generative Treiber candidate-graph interface that records
which push allocates each node and how each algorithm event is produced. Prove
that its local construction rules imply `ReplayInvariant`, rather than asking
graph clients to supply those fields separately. A parallel model-level
obligation is to justify `OrderAcyclic` from the intended RC11 assumptions, or
to retain it visibly as part of the accepted graph interface. Until the
source-to-graph and complete memory-model links are proved, the project does
not claim that the C Treiber stack is fully verified under RC11.
