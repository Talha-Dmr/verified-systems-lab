# Site-Indexed/MS Queue Working-Tree Verification — 2026-07-31

## Scope

This report records verification of the active, uncommitted site-indexed
weak-CAS and Michael--Scott queue development. It is not a release snapshot or
a publication claim. The stated conditional objective--finite-prefix
Herlihy--Wing linearizability plus site-indexed system response progress--is
now represented by a checked end-to-end theorem with explicit premises.

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
- conditional linearizable lock-freedom, its strong-CAS specialization, and
  the recurring-demand late-response consequence; and
- one concrete certificate from the checked 18-atom execution through FIFO
  legality.

## Local checks

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

## MSI full verification

Command:

```bash
./scripts/remote_verify.sh weak-memory
```

The original full run passed in 2m06s wall-clock time. After adding the exact
source-to-chain scheduling bridge, a second full run passed in 1m58s. The
latest run, including universal replay, the complete finite HW bridge, and the
coherent-infinite conditional lock-freedom bundle, passed in 3m14.109s.

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

`MSQueueInfiniteSafety.linearizableLockFree_of_siteJustice` then combines a
client-compatible schedule for every coherent finite prefix with two
non-circular liveness premises: `ProgressObligations` selects one exact stable
site with arbitrarily late matching attempts on every response-free active
suffix, and `WeakCASJustice` excludes stable all-spurious behavior at each
site. Its conclusion contains both finite-prefix linearizability and system
response progress. The strong-CAS corollary discharges justice automatically.

The theorem does **not** yet derive `ProgressObligations` from ordinary weak
thread fairness plus selected-location RC11 memory fairness. That stronger
corollary, success-rich/site-specific infinite witnesses, and a derivation of
general payload initialization from HB remain follow-up work. The present
payload condition is the explicit `SourceWellFormed.payloadReadInitialized`
contract. Raw cross-thread source-carrier enumeration is never treated as an
RC11 chronological order, and cross-thread client real time remains an
explicit boundary for the classical history theorem.
