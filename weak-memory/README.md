# 14G — Concurrent Algorithm Verification under Weak Memory

This project establishes the first verifiable foundation of the research route
using a Treiber stack without memory reclamation. The goal is not merely to
write a working stack, but to express the connection between its execution
model, sequential specification, and linearization points as explicit
theorems.

## Current Contents

- Treiber `push`, `pop`, and `is_empty` implemented with C11 atomics
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
  operation identity across source-shaped push/pop/is-empty invocations and
  retry loops
- Explicit relaxed push loads and acquire pop/is-empty loads in the
  operational, graph, replay, generation, and source-control-flow layers
- Explicit source-only `writeNext` and `readNext` occurrences, with local
  states forcing each field access to occur before its matching CAS
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
- `RemainingConsistency`, the reusable interface for eleven relation fields
  plus coherence; the canonical source-execution path now derives it
- `linearizable_of_remainingConsistency`, reconstructing `WellFormed`,
  no-thin-air, scheduling acyclicity, and `CoreConsistent` before applying the
  existing replay and linearizability chain
- `PublishedObservation`, expressing the exact release-sequence plus
  reads-from witness that makes a non-null pop observation acquire a node
- `SourceHappensBefore`, `VisibleNextWrite`, and `NodeAccessCertificate`,
  combining source sequenced-before with graph synchronizes-with so every
  modeled `readNext` can be linked to its exact pre-publication `writeNext`
- `NextReadValueCertificate`, retaining only the source-semantics fact that an
  immutable `node->next` read agrees with the allocator record
- Exact inverse projection from every non-initial canonical graph event to its
  occurrence-identified atomic source label, without collapsing equal retries
- Publisher-origin and concrete release-sequence proofs showing that a node
  re-exposed by intervening pop RMWs still originates at its unique release
  push
- `SourceAtomicExecution.toNodeAccessCertificate`, deriving every publication
  and source happens-before witness from canonical RF/MO data plus immutable
  field-value agreement
- `AtomicRelationData`, constructing canonical reads-from and modification
  order from a finite write order and one selected source ID per read, then
  deriving all eleven `RemainingWellFormedRelations` fields
- `RC11OrderWitness`, using one common finite rank for `po`, `rf`, `mo`, and
  `rb` to derive extended-coherence order, synchronization order,
  happens-before order, and coherence
- `SourceAtomicExecution`, whose carrier, program order, reads-from,
  modification order, remaining relation fields, coherence, and no-thin-air
  are constructed around finite relation data and a generic common-rank field
- `ScheduledRelationModelExecution`, whose checked respecting schedule derives
  that common rank from event positions and supplies the replay schedule
- `HerlihyWing.History`, `Completion`, `Equivalent`, `RealTimePrecedes`, and
  `Linearizable`, providing an identity-preserving finite-history definition
- Explicit source response labels separated from their atomic linearization
  points by a `returning` local state, including prefixes that commit before
  returning
- `sourceHistory` and `sourceCommittedOperations`, preserving thread and
  operation identity in client and commit projections
- An indexed `MethodTrace` refinement proving that each local operation has
  the exact `invocation ; commit ; response` shape, while internal retries are
  silent
- `scheduledOperations`, recovering operation identity from canonical event
  IDs without changing the atomic graph event type
- Source/schedule commit permutation and identity-erasure theorems connecting
  scheduled operations to the anonymous commit history already proved legal
- `SourceSkeleton.historyWellFormed` and `sourceCompletion`, deriving all
  structural history and finite-completion obligations from source control
  flow rather than accepting them as history premises
- `SourceAtomicExecution.scheduleEquivalent`, proving that every respecting
  graph schedule has the same completed operations and the same order for
  each client thread as the source completion
- `sameThreadRealTimeCompatible`, deriving same-thread real-time preservation;
  the external cross-thread condition has an exact finite Boolean checker
- `TreiberHistoryBridge`, constructing the complete classical Herlihy--Wing
  witness on every checked client-compatible schedule
- `RelationScheduleCheck` and `RespectsGraph.toRC11OrderWitness`, checking a
  finite primitive-edge schedule and deriving the common RC11 rank from event
  positions instead of accepting numeric ranks
- Executable raw-data validators for local control flow, global source
  interleavings, RF/MO data, event-ID schedules, extended-coherence paths,
  allocator/event generation, immutable `next` reads, and client real time
- `RawTreiberModelExecution.verified_of_supported`, proving node-access safety
  and Herlihy--Wing linearizability for every finite raw execution accepted by
  the pinned program-specific validator
- `RawValidationProvenance`, retaining exact source-label certification,
  relation data, schedule IDs, publication input, and final Boolean checks for
  each accepted raw value
- `NormalizedSupportedModelExecution.toRaw_supported`, proving the converse
  model-to-validator direction: canonical proof-carrying model executions
  serialize to raw inputs accepted by the complete executable pipeline
- Executable two-thread examples showing that an overlapping empty pop is
  accepted while the same schedule is rejected when a completed push precedes
  the other thread's invocation
- A deterministic Clang 18 AST extraction boundary that hash-pins
  `c/treiber.c` and `c/treiber.h`, generates both JSON and Lean descriptors,
  and checks their exact agreement with the formal control-flow descriptor

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

The checked source/model boundary is now:

```text
hash-pinned treiber.c ──trusted Clang-AST extractor──→ generated Lean descriptor
                                                          ↓ kernel-checked equality
externally supplied raw source/RF/MO/schedule/publication inputs
                              ────────────────────────→ executable Lean validators
                                                          ↓
                                  ValidatedTreiberModelExecution
                                      │                 │
                                      ├──→ node safety  └──→ HW linearizability
```

The Lean theorem now connects source invocations/responses in an accepted raw
input to its checked linearization-point schedule. The source extractor is an
explicit trust boundary: the project still does not claim a proved semantics
for arbitrary C, a proof of Clang, or completeness for the full C11 standard.
For every finite raw input the validator accepts, the theorem proves the
result; it is not proved that every execution of the C program produces such
an input. The native stress test and bounded GenMC runs remain validation
evidence, not substitutes for the Lean theorem.

The RC11-style and replay layers now prove:

```text
source skeleton + finite rf/mo data ──→ canonical Graph
                    │
                    ├──→ eleven remaining WellFormed fields
                    └──→ checked relation schedule
                                  └──→ position rank ──→ coherence
                                      ↓
                           SourceAtomicExecution
                                      ↓
ControlledCandidate ──→ carrier/initializer/program-order WellFormed fields
         │
         └────────────→ GeneratedCandidate ──→ GraphTyping ──→ ReplayInvariant

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
with the graph carrier's arbitrary enumeration. `GeneratedCandidate` itself
is only a local typing certificate; the top-level validator separately checks
source-derived `po`, raw `rf`/`mo`, and a primitive-edge relation schedule.
`TreiberControlFlow` now constrains each thread to the source retry shape and
retains operation identifiers. The source's relaxed push load and acquire
pop/is-empty loads are explicit graph events. An initially empty pop commits at
its acquire load, while a failed pop CAS observing null commits at that failed
CAS because the source loop returns immediately. `EventGraph`, `Interleaving`,
and `ControlledCandidate` generate the represented atomic carrier and its
exact program order while retaining the erased source metadata. Non-atomic
`node->next` initialization and dereference remain outside that carrier but
are now retained as occurrence-identified source labels. The local machine
proves which acquire load or failed CAS authorizes each dereference and which
field write precedes each release push. `NodeAccessCertificate` joins those
source edges with a release-sequence/reads-from witness. The canonical
execution now derives that certificate: allocator uniqueness identifies the
original release push; decreasing common rank rules out fabricated pointers
when a pop re-exposes an older node; and adjacency in the concrete
modification order constructs the complete RMW release sequence. At the raw
validator boundary, `NextReadCheck` now compares every finite `readNext` label
to the generated allocator table and constructs the immutable-value
certificate.
`RemainingConsistency` remains as a reusable interface, but the canonical
`SourceAtomicExecution` path no longer asks a caller to assemble its eleven
fields or coherence: `AtomicRelationData` and `RC11OrderWitness` derive them.
The write order and read-source function remain genuine semantic choices of an
RC11 execution, not values inferable from source syntax. They are supplied as
finite raw data and checked for exact write/read coverage, value agreement,
and RMW adjacency. A checked primitive-edge schedule constructs their common
rank. Happens-before acyclicity and no-thin-air are derived rather than
repeated as certificate fields.

`TreiberHistory` defines classical Herlihy--Wing completion, per-thread
equivalence, real-time preservation, and sequential legality with operation
identity retained. Control flow now emits explicit responses after a distinct
atomic commit, and exact event-ID lookup reconstructs the matching operation
identity in any respecting graph schedule. Source well-formedness, completion,
per-thread equivalence, and same-thread real time are now derived. RC11
consistency alone still does not turn cross-thread wall-clock order into C11
happens-before; the validator therefore checks compatibility with exactly the
cross-thread response-before-invocation edges encoded by the supplied trace
before constructing the classical Herlihy--Wing witness. Fidelity of that
trace to physical execution time remains part of the external semantics
boundary. This condition is intentionally not mislabeled as an RC11 axiom.

## Source-Extraction Trust Boundary

`tools/extract_treiber_source_trust_boundary.py` checks the exact Clang 18 AST
shape used by the model and generates:

- `c/treiber.source-extraction-trust-boundary.json`;
- `WeakMemory/TreiberExtractedProgram.lean`.

`TreiberProgramRefinement` proves the generated descriptor agrees component by
component with the Lean memory orders and control-flow transitions. The
extractor check separately byte-compares artifacts and source hashes. Together
these narrow and record the trusted surface, but do not prove Clang correct or
prove a general C11 operational-semantics refinement. See
`tools/README-source-extraction-trust-boundary.md` for the exact claim.

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

1. Re-extracts the Clang AST facts and byte-checks the committed JSON and Lean
   descriptors, including both source hashes.
2. Builds the C code with warnings treated as errors.
3. Runs the sequential and multithreaded tests.
4. Builds the Lean project so the kernel checks all theorems and the executable
   single- and cross-thread raw-model examples.
5. Runs both bounded weak-memory harnesses explicitly under RC11 with GenMC.

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

Formalize the remaining execution-frontend theorem: every execution of the
hash-pinned reclamation-free C program under the explicitly selected
C11/RC11 semantics must translate to finite raw source, relation, schedule,
publication, next-read, and client-order data accepted by `validate?`.
Validator soundness is now proved, but validator acceptance is not yet proved
complete for executions of the C program. Until that connection is formalized
or isolated behind a precisely specified trusted translator, the project does
not claim full C-source verification under RC11.
