# Site-Indexed/MS Queue Working-Tree Verification — 2026-07-31

## Scope

This report records verification of the site-indexed weak-CAS and
Michael--Scott queue milestone. It is an implementation verification record,
not a mathematical novelty or publication claim. The objective--finite-prefix
Herlihy--Wing linearizability plus site-indexed system response progress--is
now represented by a checked public theorem with explicit finite-prefix
scheduling, weak thread fairness, per-site RC11 memory fairness, and
independent primitive weak-CAS justice premises. The queue-specific
`ProgressObligations` package is
derived from those concrete scheduler and visibility assumptions rather than
accepted by the public result.

Checked milestones:

- generic site-indexed weak-CAS progress and per-site justice separation;
- conservative recovery of the single-site API and two-site witnesses;
- FIFO commit specification;
- finite multi-location non-SC RC11 core;
- full non-fence RC11 release-sequence semantics and focused witnesses;
- source-shaped reclamation-free Michael--Scott local control;
- global source-trace well-formedness and negative regressions;
- an exact source-projected `SupportedExecution` with explicit RF/MO and full
  RC11 `Valid`; and
- the invariant-preserving finite chain/FIFO replay kernel;
- an exact source-to-chain structural extractor and whole-carrier
  `PO`/`ECO`-respecting atom-schedule certificate;
- universal canonical replay and FIFO legality for every admitted atom
  schedule, without an externally supplied replay or final state;
- source-history well-formedness, completion, per-thread schedule
  equivalence, same-thread real-time preservation, and the final finite
  `HW.Linearizable` bridge;
- one coherent infinite queue carrier with global RF/per-site MO restrictions
  and an exact site-indexed progress-interface instantiation;
- per-site `FromReadFair`/`MemoryFair`, maximal-write selected-site visibility,
  and one uniform stable-value cutoff for all later atomic reads;
- response-free all-site stabilization from weak thread fairness, canonical
  replay's finite Tail-move budget, and finite-thread bounds on fresh `next`
  initialization;
- the stable-read/control-rank argument, represented-site atomic-read bridge,
  and finite-site infinitely-often pigeonhole theorem deriving
  `ProgressObligations`;
- `MSQueueFairLockFreedom.linearizableLockFree_of_fairness`, its exact-`fr`,
  selected-visibility, strong-CAS, and recurring-demand variants;
- a coherent all-spurious queue execution satisfying the concrete scheduler
  and RC11 memory-fairness hypotheses while refuting primitive justice and
  system response progress at `.next 0`; and
- `MSQueueInfiniteWitnessExecution` and
  `MSQueueInfiniteWitnessFairness`, which package the success-rich source and
  its valid prefixes as one coherent infinite execution and prove the full
  scheduler, memory-fairness, visibility, progress, recurring-demand, and
  same-site weak-CAS justice bundle;
- `successfulAssumptionsJointlySatisfiable`, the positive joint witness, and
  `successfulWitness_linearizableLongRun`, its finite-prefix FIFO
  linearizability and arbitrarily-late-response consequence; and
- one concrete certificate from the checked 18-atom execution through FIFO
  legality.

The positive joint-satisfiability witness is therefore complete. Its justice
proof couples each matching attempt to success at the same site; unrelated
successes are not used to discharge the obligation.

## Full milestone verification

Command:

```bash
./scripts/remote_verify.sh weak-memory
```

The complete integrated suite passed on `math-msi` in 55.743 seconds for the
remote verification command:

- the local trust-boundary check matched the JSON and Lean descriptors to the
  pinned Clang 18.1.3 AST and recorded the expected C-source hashes;
- native C sequential and four-thread 80,000-node stress tests passed;
- the full Lean library, public `MSQueueResult` surface, both infinite
  witnesses, all explicit verification targets, and the demo executable
  passed; the top-level library build completed 308 jobs;
- the new witness modules emitted no own linter warnings; the only replayed
  warnings were the four pre-existing warnings in
  `MSQueueSourceHeadTailGap` and `MSQueueSourceMethodTrace`;
- GenMC 0.17.0 completed the publication harness (2 executions) and the
  two-thread Treiber harness (20 complete, 10 blocked executions) with no
  errors; and
- the GenMC Relinche one-push/one-pop check completed 2 executions and 1
  checked hint with no errors.

A direct `lean --trust=0 WeakMemory/MSQueueResult.lean` check also passed.
`#print axioms` for the public memory-fair theorem and both headline witness
theorems reported only Lean's standard imported axioms `propext`,
`Classical.choice`, and `Quot.sound`. A word-boundary scan of all new queue
modules found no `sorry`, `admit`, project `axiom`, or `unsafe` declaration;
`git diff --check` and shell syntax checks passed.

The run used the exact Lean and C source content recorded by this milestone;
the subsequent repository-recording steps changed only Git metadata and
documentation.

## Earlier local baseline

The checks below predate the final concrete fairness modules and are retained
as historical baseline evidence, not as verification of the newly completed
liveness extension.

- `lake build`: all 188 library jobs passed.
- The combined queue theorem surface
  (`MSQueueSourceScheduleEquivalence`, `MSQueueSourceSameThreadRealTime`,
  `MSQueueSourceHistoryBridge`, `MSQueueInfinite`, and
  `MSQueueInfiniteSafety`) passed a 60-job targeted build.
- Every new public example target passed, including:
  - `WeakMemory.MultiLocationRC11ReleaseSequenceExamples`;
  - `WeakMemory.MSQueueSourceWellFormedExamples`;
  - `WeakMemory.MSQueueSourceRC11Examples`; and
  - `WeakMemory.MSQueueChainExamples`.
- `WeakMemory.MSQueueSourceChain`, `MSQueueSourceUniversalReplay`,
  `MSQueueSourceHistoryBridge`, `MSQueueInfiniteSafety`, and the concrete
  chain examples passed targeted local kernel checks.
- The retroactive-empty regression now also proves that source-emission order
  `[enqueue 7, dequeueEmpty]` admits no FIFO `CommitTrace`, while anchor order
  `[dequeueEmpty, enqueue 7]` does.
- The 18-atom source-backed RC11 witness required approximately 334 seconds
  to elaborate on the local machine.
- `bash -n` passed for both verification scripts.
- `git diff --check` passed.
- A word-boundary scan of every new Lean module found no `sorry`, `admit`,
  project `axiom`, or `unsafe` declaration.

## Earlier MSI full-verification baseline

Command:

```bash
./scripts/remote_verify.sh weak-memory
```

The original full run passed in 2m06s wall-clock time. After adding the exact
source-to-chain scheduling bridge, a second full run passed in 1m58s. The
latest run, including universal replay, the complete finite HW bridge, and the
coherent-infinite *conditional* lock-freedom bundle, passed in 3m14.109s. These
timings predate `MSQueueInfiniteFairProgress` and
`MSQueueFairLockFreedom`; the current replacement timing is recorded above.

- The pinned Clang 18.1.3 source descriptor was checked locally before sync.
- Native C sequential and 80,000-node stress tests passed remotely.
- The Lean library and every explicit new target passed.
- The 18-atom source-backed RC11 witness took 81 seconds on the latest MSI
  run.
- The new schedule-equivalence theorem built in 0.708 seconds; the combined
  60-job queue history/infinite bundle completed successfully.
- GenMC 0.17.0 publication and two-thread checks passed.
- The Relinche one-push/one-pop check passed.

## Checked result and claim boundary

The concrete `SupportedExecution` proves that the source, carrier, RF/MO, and
RC11 layers are jointly satisfiable and that dynamic `next` initialization is
published through a successful release link to an acquiring cross-thread
read. It is a non-vacuity/integration witness, not the general queue theorem.

The new scheduling bridge prevents a favorable unrelated replay: its atom
schedule covers the candidate exactly and respects `PO`/`ECO`; every
successful structural CAS and retroactive empty anchor is placed on that
schedule with exact coverage; and FIFO legality uses precisely the resulting
record order. Exact record coverage is now derived by a generic bucketing
permutation theorem from scheduled-ID uniqueness and source-checked anchor
membership rather than being supplied as an algorithm-specific fact. The
concrete supported execution discharges the remaining fields.

The scheduling layer now includes a kernel-checked finite topological
constructor under explicit `PO ∪ ECO` transitive-closure acyclicity. A common
relation rank proves that premise for the concrete queue witness. The premise
is intentionally separate from generic `Valid`; multi-location RC11 admits
mixed cross-location program/modification-order cycles that do not violate its
no-thin-air or coherence clauses. A checked two-thread/two-location candidate
now proves both `Valid` and the nonexistence of any list respecting all of its
`PO` and `ECO` edges.

The first schedule-to-representation kernel is checked as well: RF, MO, and
RB edges induce strict schedule order; an RF source is protected against any
MO-later write already occurring before its read; and successful RMW sources
are their immediate MO predecessors.

The replay and finite client-history obligations are now derived. For every
admitted `AtomSchedule`, `canonicalCertificate` supplies the exact replay and
FIFO legality. `AtomSchedule.scheduleEquivalent` preserves each client's
commit order, including retroactive empty anchors. With explicit cross-thread
client-time compatibility, `AtomSchedule.linearizable` constructs the full
Herlihy--Wing witness.

`MSQueueInfiniteSafety.linearizableLockFree_of_siteJustice` remains the
conditional composition point. It combines a client-compatible schedule for
every coherent finite prefix with two non-circular liveness premises:
`ProgressObligations` selects one exact stable site with arbitrarily late
matching attempts on every response-free active suffix, and `WeakCASJustice`
excludes stable all-spurious behavior at each site.

The concrete queue chain now derives the first premise. `FromReadFair` is the
exact per-site prefix-finite `fr` condition used by visibility; conventional
`MemoryFair` supplies paired prefix-finite `mo` and `fr` and implies it.
`SelectedSiteVisibilityFair` says that, once a represented site is stable,
all sufficiently late reads use the cutoff prefix's maximal write. A finite
represented-site list then turns the pointwise visibility facts into one
uniform `stableValueAt` assignment for every later atomic read.

On a hypothetical response-free active suffix, weak thread fairness first
rules out later enqueue/dequeue commits. Canonical FIFO replay bounds the
number of successful Tail advances by the links already present at the suffix
boundary, while the finite source thread family bounds one-time fresh `next`
initializations. Thus `eventually_noModification_on_responseFreeSuffix`
produces a common cutoff after which no `.head`, `.tail`, or `.next node` site
is modified.

The stable-control proof then uses a finite rank combining stale-cache
flushing and aligned source progress. A continuously active fairly scheduled
owner cannot decrease that rank forever, so
`infinitelyOften_matchingCAS_of_stableObservations` produces arbitrarily late
compare-equal CAS events. Each such event is proved to have an RC11 read
component at a site represented by the finite stabilization prefix. The
finite-list infinitely-often pigeonhole lemma fixes one site and thereby
constructs the exact coupled witness required by `ProgressObligations`.

The public `MSQueueFairLockFreedom` module's
`linearizableLockFree_of_fairness` theorem therefore assumes
`PrefixSchedules`, source `WeakThreadFair`, per-site `MemoryFair`, and
independent `WeakCASJustice`, and concludes both
finite-prefix Herlihy--Wing FIFO linearizability and system response progress.
`linearizableLockFree_of_fromReadFairness` exposes the exact `fr` dependency,
and the strong-CAS corollary discharges primitive justice automatically.

The coherent all-spurious queue witness checks the remaining separation: both
prefix scheduling layers, scheduler fairness, `MemoryFair`, `FromReadFair`,
selected-site visibility, and the derived `ProgressObligations` all hold, yet
primitive justice and system response progress fail at `.next 0`. The
success-rich counterpart is now complete:
`MSQueueInfiniteWitnessExecution` packages its valid finite prefixes as a
coherent `InfiniteRC11Execution`, and `MSQueueInfiniteWitnessFairness` proves
the full fairness, visibility, progress-obligation, recurring-demand, and
same-site justice bundle. `successfulAssumptionsJointlySatisfiable` records
those assumptions in one existential theorem, while
`successfulWitness_linearizableLongRun` applies the public liveness result to
obtain finite-prefix FIFO linearizability and arbitrarily late responses.

The claim boundary otherwise remains unchanged. General payload
initialization from HB is still follow-up work; the present payload condition
is the explicit `SourceWellFormed.payloadReadInitialized` contract. Raw
cross-thread source-carrier enumeration is never treated as an RC11
chronological order, cross-thread client real time remains an explicit premise
for the classical history theorem, and the result does not cover reclamation,
address reuse/ABA, allocation progress, starvation-freedom, minimal memory
orders, full ISO C semantics, compiler correctness, or physical hardware.
