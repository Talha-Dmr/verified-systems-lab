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
- `orderAcyclic_of_wellFormed_coherent` and
  `CoreConsistent.orderAcyclic`, proving that RC11 coherence already
  discharges the combined scheduling-acyclicity premise in this event model
- `TreiberRC11.ReplayInvariant`, stating fresh and unique node allocation,
  immutable pop publication, and an empty initial head
- `replay?_eq_some_advanceUncheckedList`, deriving successful executable
  replay from a respecting order and those explicit invariants
- `linearizable_of_replayInvariant`, constructing the schedule and final state
  and proving that the resulting completed history is a legal sequential
  stack history
- `AllocatorTable`, `Event.TypedBy`, and `GraphTyping`, replacing pairwise
  replay obligations with one functional node-provenance table and local
  event-typing rules
- `GraphTyping.toReplayInvariant` and `linearizable_of_graphTyping`, deriving
  the replay obligations and end-to-end result from that typed interface
- `GeneratedEvents`, an inductive local event-and-allocator certificate whose
  successful-push rule extends the allocator table only at a fresh unused node
  identifier and whose weak-CAS failures may be spurious
- `GeneratedCandidate.toGraphTyping` and
  `linearizable_of_generatedCandidate`, proving that an emitted list connected
  to the graph carrier by a permutation automatically satisfies the
  allocator-table interface and enters the existing end-to-end theorem
- `ControlFlow.LocalState`, `Label`, `LocalStep`, and `Execution`, retaining
  operation identity across source-shaped push/pop invocations and retry loops
- Control-flow theorems proving that failures update the expected pointer,
  weak compare-exchange may fail spuriously, every projected action belongs to
  its thread, and a failed pop CAS observing null completes immediately
- `EventGraph.Skeleton`, projecting atomic control-flow labels to one
  duplicate-free event carrier with a unique initializer, injective IDs, and
  exact same-thread program order
- `Interleaving.SourceSkeleton`, requiring every thread projection to be a
  locally valid execution with globally unique operation IDs and fresh,
  distinct push-node reservations
- `ControlledCandidate`, indexing `GeneratedEvents` by exactly the source
  skeleton's carrier and requiring the graph's program order to equal the
  generated relation
- `CarrierProgramOrderWellFormed`, deriving the seven carrier, initializer,
  and program-order fields of `WellFormed` from the controlled candidate
- `RemainingConsistency`, containing only the eleven still-supplied
  reads-from, modification-order, RMW, and initial-order fields plus coherence
- `linearizable_of_remainingConsistency`, reconstructing `WellFormed`,
  no-thin-air, scheduling acyclicity, and `CoreConsistent` before applying the
  existing replay and linearizability chain

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
CAS attempts do not change shared state. A failed pop CAS that observes null
is nevertheless the empty-pop linearization point because the C loop returns
without another atomic operation.

The remaining source-level boundary is:

```text
C11 Treiber source / complete RC11 semantics
                    ↓ not yet proved
standalone load/non-atomic events and rf/mo construction
                    ↓ not yet proved
ControlledCandidate + RemainingConsistency
```

The current theorems establish the linearization-point core, not yet the full
Herlihy–Wing invocation/response definition. The stress test is not a proof,
and the project does not claim to verify the complete C11 semantics or the C
source directly.

The RC11-style and replay layers now prove:

```text
ControlledCandidate ──→ carrier/initializer/program-order WellFormed fields
         │
         └────────────→ GeneratedCandidate ──→ GraphTyping ──→ ReplayInvariant

RemainingConsistency ──→ remaining WellFormed fields + coherence
                                      ↓
             CoreConsistent + derived no-thin-air and OrderAcyclic
                                      ↓
                         respecting replay schedule
                                      ↓
                         legal sequential stack history
```

Executable replay is not treated as an oracle: its acceptance is proved
equivalent to the inductive operational semantics. Combined-order acyclicity
is no longer an external premise: `orderAcyclic_of_wellFormed_coherent`
derives it from well-formedness and coherence using a reads-from
source/modification-order rank. The replay proof uses `rf`,
modification-order totality, and reads-before to show that every event
observes the current head. The remaining heap obligations are visible in
`ReplayInvariant`; they are not hidden inside a replay-success assumption.
`GraphTyping` derives those obligations from a functional allocator table:
successful pushes record fresh immutable nodes and pops name their recorded
publisher. Failed weak compare-exchanges record the current head but may be
spurious, matching the C implementation's use of
`atomic_compare_exchange_weak_explicit`.
`GeneratedEvents` builds the table incrementally, and `GeneratedCandidate`
uses an explicit permutation proof instead of identifying emission chronology
with the graph carrier's arbitrary enumeration. This is a local typing
certificate, not yet a generator for `po`, `rf`, `mo`, or `eco`.
`TreiberControlFlow` now constrains each thread to the source retry shape and
retains operation identifiers. Its invocation labels record initial load
observations because the current operational action type does not yet contain
a standalone load event; connecting those observations and the non-atomic node
reads to a complete C11 graph remains future work. `EventGraph`,
`Interleaving`, and `ControlledCandidate` generate the represented atomic
carrier and its exact program order while retaining the erased source metadata.
`RemainingConsistency` still accepts eleven `rf`/`mo`/RMW relation properties
and coherence; it does not claim those relations came from the C program.
Happens-before acyclicity and no-thin-air are now derived rather than repeated
as certificate fields.

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

Extend the event model with the standalone initial head loads and the
non-atomic node-field accesses used by the C control flow. In particular, a
nonempty pop must acquire publication before dereferencing `observed->next`;
the later successful CAS cannot justify an earlier dereference. Then construct
reads-from and modification order and discharge the eleven
`RemainingConsistency` relation fields instead of accepting them. Until those
and the complete source/memory-model links are proved, the project does not
claim that the C Treiber stack is fully verified under RC11.
