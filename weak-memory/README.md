# 14G — Concurrent Algorithm Verification under Weak Memory

This project establishes the first verifiable foundation of the research route
using a Treiber stack without memory reclamation. The goal is not merely to
write a working stack, but to express the connection between its execution
model, sequential specification, and linearization points as explicit
theorems.

## Current Contents

- Treiber `push`, `pop`, and `is_empty` implemented with C11 atomics
- A native stress test using four threads and 80,000 distinct nodes
- Two bounded safety harnesses and one bounded Relinche linearizability
  harness for GenMC
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
- `ExternalExecutionSemantics`, `PureExecutionFrontend`, and
  `FrontendContract`, specifying a non-circular program/execution boundary as
  pinned program identity, exact validator acceptance, and exact
  client-history fidelity
- `verified_of_external_allowed`, transferring raw-input provenance,
  descriptor agreement, modeled node-access safety, and Herlihy--Wing
  linearizability to every external execution covered by an explicit
  frontend contract; the `TreiberC11V1` frontend now instantiates that
  contract for its independently defined declarative semantics
- `TreiberC11V1.DeclarativeExecution`, the public finite execution semantics,
  combining an explicit source run, an independently defined `RC11.Valid`
  candidate, the source/client lifetime and value contract, and acyclicity of
  program-order, extended-coherence, and committed client-real-time edges
- `DerivedOrder.existsClientCompatibleOrder`, constructing the internal
  client-compatible schedule by finite topological sorting instead of asking
  a declarative execution to supply a schedule or numeric rank
- `relationData_coreConsistent_of_rc11` and
  `relationData_orderAcyclic_of_rc11`, directly translating independent RC11
  no-thin-air and coherence into the target `CoreConsistent` and
  `OrderAcyclic` obligations
- `GenerationFrontend.generationResult`, deriving allocator-backed generated
  events, publication origins, and the immutable-`next` certificate used by
  the normalized validator frontend
- `projectedGraphTyping` and `existsCertifiedReplay_of_rc11`, combining
  generated `GraphTyping` with directly derived RC11 `CoreConsistent` to
  construct a certified replay for the exact same projected graph
- `FullDeclarativeGuarantees` and
  `everyDeclarativeExecution_fullyVerified`, the canonical final bundle of
  direct RC11 consistency, graph typing, certified replay, the derived client
  schedule, validator provenance, node safety, and Herlihy--Wing
  linearizability for every declaratively admitted execution
- `DeclarativeExecution.singlePush`, a concrete nonempty execution with a
  successful release-CAS commit, plus `singlePush_linearizable` as a
  nontrivial instance of the public theorem
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

The new public, schedule-free theorem adds this path:

```text
finite explicit TreiberC11V1 source execution
        + independent RC11 candidate and RC11.Valid
        + ClientContract
        + ClientOrderAcyclic
                         │
                         ├── RC11 no-thin-air/coherence
                         │       └──→ CoreConsistent + OrderAcyclic
                         ├── source generation ──→ GraphTyping
                         │       └──→ CoreConsistent + GraphTyping
                         │              (exact same projected graph)
                         │                    └──→ some certified replay schedule
                         ├── augmented PO/ECO/real-time topological construction
                         │       └──→ client-compatible schedule ──→ HW
                         └── immutable next values
                                 └──→ normalized checked model
                                             ├──→ validator provenance
                                             ├──→ node safety
                                             └──→ HW linearizability
```

`DeclarativeExecution` is the public semantic domain. It contains no selected
event schedule and no accepted-validator result. Its four components are the
explicit source/candidate execution, independent `RC11.Valid`,
`ClientContract`, and `ClientOrderAcyclic`. The last condition says that the
union of independent program order, extended coherence, and atomic commit
edges induced by client real time is acyclic. A finite topological proof
constructs the client-compatible schedule used by the normalized
Herlihy--Wing path. Separately, the relation projection uses
`RC11.Valid.noThinAir` and `RC11.Valid.coherence` directly to derive target
`CoreConsistent` and `OrderAcyclic`; those results are not obtained from the
selected client schedule.

The source and generation frontends then derive exact source/event/history
projections, unique node publishers, allocator-backed generated events,
publication witnesses, and immutable-`next` read certificates. The normalized
model is proved accepted by the existing executable validator.
`projectedGraphTyping` applies the generated typing proof to the exact graph
whose `CoreConsistent` proof was derived directly from `RC11.Valid`.
`existsCertifiedReplay_of_rc11` combines those certificates to construct some
accepted operational replay and certified schedule for that same graph.

That RC11-only certified replay schedule and the augmented
program-order/extended-coherence/real-time client schedule are two separately
constructed witnesses and need not be definitionally equal. The latter is the
one carrying the real-time certificate used by the Herlihy--Wing bridge.
`clientScheduleReplay_of_rc11` additionally proves that this exact augmented
schedule replays successfully, using direct RC11-derived `WellFormed`,
generated `GraphTyping`, and its graph-order certificate; the separate
existential `CertifiedSchedule` retains the full `CoreConsistent` certificate,
including no-thin-air.

`FullDeclarativeGuarantees` is the canonical final result package. It contains
the direct `CoreConsistent` and `OrderAcyclic` results, generated
`GraphTyping`, certified replay, topologically derived client-compatible
schedule and its exact successful-replay equality, validator-backed
allowed-execution guarantees, and direct Herlihy--Wing theorem.
`everyDeclarativeExecution_fullyVerified` constructs that complete bundle for
every admitted `DeclarativeExecution`; in particular, the certified-replay
dependency path does not bypass independent RC11 no-thin-air or coherence.
The older `everyDeclarativeExecution_linearizable` theorem remains a
convenient direct projection to the history result.

`DeclarativeExecution.singlePush` provides a concrete nonempty source
execution containing a successful push commit, and `singlePush_linearizable`
instantiates the public result for that witness.

The quantified model is deliberately narrower than full C11:

- executions are finite prefixes;
- the modeled algorithm has one atomic `head` and uses only the required
  non-SC RC11 fragment;
- memory reclamation, freeing, and node reuse are excluded;
- invocation identifiers and pushed nodes are unique;
- source payloads agree with the candidate payload function;
- non-atomic `node->next` reads obey the immutable field-value contract; and
- the client/environment satisfies augmented-order acyclicity, including
  committed real-time edges.

The final client condition is necessary because C11/RC11 atomic relations do
not, by themselves, encode arbitrary cross-thread response-before-invocation
order observed by an external client. Such real-time order must come from a
client/environment model; requiring the augmented order to be acyclic states
exactly the compatibility needed for a Herlihy--Wing schedule without
mislabeling wall-clock order as an RC11 axiom.

The source extractor remains an explicit trust boundary. It hash-pins the
implementation and checks the expected Clang AST descriptor, but the
`TreiberC11V1` source semantics is hand-defined and versioned rather than
derived by a proved ISO C semantics or a proof of Clang. Thus the theorem
covers every finite `DeclarativeExecution` admitted by that explicit model,
not every execution of arbitrary C or every execution permitted by the full
C11 standard. The native stress test and bounded GenMC runs remain validation
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
identity retained. Control flow emits explicit responses after a distinct
atomic commit, and exact event-ID lookup reconstructs the matching operation
identity in the derived graph schedule. Source well-formedness, completion,
per-thread equivalence, and same-thread real time are derived. RC11
consistency alone still does not turn cross-thread wall-clock order into C11
happens-before. In the public semantics, the trace supplies those
response-before-invocation facts and `ClientOrderAcyclic` requires their
committed event edges to be compatible with program order and extended
coherence. The internal client-compatible schedule is then constructed
topologically. Fidelity of the hand-defined trace to a physical C execution
remains part of the source-semantics trust boundary, not an RC11 axiom.

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
4. Builds the Lean project so the kernel checks all theorems, the final
   `TreiberC11V1` frontend, its concrete single-push witness, and the
   executable single- and cross-thread raw-model examples.
5. Runs two bounded weak-memory safety harnesses explicitly under RC11 with
   GenMC.
6. Runs GenMC's Relinche checker against the exact `treiber.c` implementation
   for the most-parallel client containing one push and one pop.

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

GenMC exhaustively explores these finite harnesses according to its
implemented model, but that bounded exploration is supporting evidence rather
than a proof of the unbounded C implementation. In particular, the pinned
GenMC v0.17.0 interpreter does not branch on LLVM's `cmpxchg weak` flag:
equal expected and observed values always succeed, so spurious weak-CAS
failures are absent. It also uses the success ordering for the CAS read half
instead of selecting the failure ordering on failure. The Lean semantics does
model equal-value weak-CAS failures, so the GenMC executions form a
strong-CAS-like subset of the executions admitted by the current Lean model
and by C11. See `tools/README-genmc-validation-boundary.md` for the source
audit and exact limitations.

## Next Precise Milestone

Replace the hand-defined, hash-pinned source boundary with a proved refinement
from a substantially fuller ISO C execution semantics. That proof should
derive `TreiberC11V1` source traces, non-atomic field behavior, and the
independent RC11 candidate from executions of the parsed C program, while
making compiler and library assumptions explicit. It should then show that
the resulting client/environment model establishes the current declarative
admissibility conditions. Until such a refinement is proved, the project
claims verification of the explicit versioned `TreiberC11V1` semantics, not a
general proof of Clang or full C-source verification under all of ISO C11.
