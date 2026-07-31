# Site-Indexed Weak-CAS Progress Roadmap

**Status:** core theorem chain and positive/negative infinite witnesses
complete; full milestone verification passed on 2026-07-31
**Started:** 2026-07-31
**Primary MSC:** 68Q85
**Secondary MSC:** 68Q60, 68Q55, 03B70

## Objective

Develop a reusable, machine-checked progress theory for multi-location
concurrent algorithms using genuinely weak compare-and-exchange. The theory
must distinguish scheduler fairness, memory visibility, and primitive
weak-CAS justice; associate justice with the exact logical CAS site; and
compose finite-prefix linearizability with conditional unbounded system
progress.

The first realistic multi-location target is a reclamation-free
Michael--Scott FIFO queue under an explicit RC11 model.

## Completed foundation

The following generic and validation milestones are implemented:

1. `WeakCAS.SiteProgressRule.Interface Thread Site` indexes matching attempts,
   successful CAS events, and all generation-changing modifications by one
   logical site.
2. `PrimitiveJusticeAt` uses an eventually modification-free site, not merely
   a success-free site. Same-valued writes and ABA-shaped changes therefore do
   not masquerade as stability.
3. `Obligations` may choose a later cutoff, a helper thread, and a site on a
   response-free suffix. This admits finite helping before stabilization and
   does not require the initially active owner to perform the progress step.
4. `systemResponseProgress_of_siteJustice` proves system response progress
   from those coupled obligations and per-site justice.
5. `primitiveJusticeAt_iff_noStablePureSpuriousSuffixAt` gives the exact
   execution-level characterization of site justice.
6. Strong compare-equal CAS behavior discharges site justice directly.
7. The original single-site rule is recovered through `Site := Unit`; the
   existing Treiber and counter clients continue to use their public API.
8. `WeakCASTwoSite` supplies:
   - a fair success-rich run with recurring successes at both sites;
   - a fair all-spurious run violating justice at both sites; and
   - a wrong-site run where recurring right-site successes do not discharge a
     stable all-spurious left retry loop.

The compact public entry point is
`WeakMemory/WeakCASSiteResult.lean`.

## Logical site contract

A site denotes a logical atomic location together with enough identity to
distinguish allocation generations when reuse is modeled. `modifiedAt` must
record every event that changes the supplying-write generation, including
same-valued writes. Each concrete RC11 client must prove that its projection is
complete for the selected site.

The generic theorem establishes system lock-freedom, not starvation-freedom:
the success forced at a site need not belong to the repeatedly attempting
thread.

## Michael--Scott queue target

The site type will be:

```lean
inductive Site
  | head
  | tail
  | next (node : NodeId)
```

The model will use one permanent dummy node, unique fresh enqueue nodes,
immutable payloads, atomic `next` fields, and no `free`, address reuse, or
reclamation.

Linearization points:

| Operation | Linearization event |
|---|---|
| `enqueue value` | successful `CAS(next tail, null, fresh)` |
| nonempty `dequeue` | successful `CAS(Head, head, next)` |
| empty `dequeue` | validated observation `head.next = null` |
| tail helping | abstract stutter |

The initial memory-order profile is intentionally sufficient rather than
minimal: acquire pointer loads, acq_rel successful CAS, and acquire failed CAS.
No minimal-order claim is part of the first theorem.

## Implementation stages

### M1 -- FIFO specification and multi-location RC11 core

**Status: complete and independently verified on 2026-07-31.**

- Define queue operations, responses, legal sequential FIFO histories, nodes,
  sites, and commit events.
- Define location-indexed `rf`, `mo`, `rb`, `eco`, `hb`, per-location
  initialization, per-location total modification order, and same-location RMW
  adjacency.
- Validate the core on explicit two-location finite examples.

The non-fence release-sequence relation follows the
[RC11 repair paper](https://plv.mpi-sws.org/scfix/paper.pdf) and the
[official executable `rc11.cat`](https://diy.inria.fr/www/weblib/rc11.cat.html):
an optional later same-thread/same-location atomic write is followed by zero
or more RF-linked RMW events. RMW modification-order adjacency is checked by
well-formedness rather than built into the release-sequence definition.

### M2 -- Source-shaped operational queue

**Status: complete and integration-tested on 2026-07-31.** M2a (the local
enqueue/dequeue machine) is complete.
M2b now supplies a global interleaving certificate with canonical atom IDs,
unique operations and fresh non-dummy nodes, per-thread idle-started `Run`
projections, payload provenance, exact static/dynamic carrier construction,
and validated retroactive-empty anchors. The three-operation source trace is
packaged as a concrete `SupportedExecution` with explicit RF/MO and full RC11
`Valid`; its dynamic next initializer is proven HB-before a cross-thread
acquire read through the successful release link. The execution-to-chain and
visibility obligations deferred at M2 are now discharged by M3/M4; general
non-atomic payload publication remains an explicit later obligation rather
than a hidden M2 assumption.

- Model full enqueue/dequeue control flow, including validation reloads,
  mismatch, spurious failure, helping, commit, and separate response events.
- Enforce fresh nodes, immutable payloads, and no reuse.

The M3 reachability proof must explicitly exclude stable snapshots with
`Head != Tail` but `Head.next = null`, as well as null Head/Tail pointer loads.
The source machine intentionally has no transition for those states; treating
them as impossible without a chain/publication invariant would make the later
progress proof circular.

### M3 -- Finite safety and linearizability

**Status: complete for finite-prefix safety under an admitted atom schedule
and explicit cross-thread client-time compatibility.** A
memory-model-independent chain state represents the permanent
dummy, fresh append-only node chain, aligned immutable payloads, Head/Tail
indices, and at-most-one-node Tail lag. Link, Head, Tail-help, and empty
structural steps preserve the invariant; every finite replay projects to a
legal FIFO `CommitTrace`.

`MSQueueSourceChain` now extracts every successful structural CAS, including
abstractly silent Tail swings, and retains the full source occurrence. Empty
dequeue is anchored at its earlier null-next read rather than its later
validation event. An `AtomSchedule` covers the exact RC11 carrier by
permutation and respects both program order and extended coherence; structural
records are placed definitionally at their anchor atoms in that schedule.
Unique scheduled IDs plus source-checked anchor membership now derive
`AtomSchedule.recordsOn_perm` automatically, preventing omission,
duplication, or invention of effects. `Certificate.ofReplay` fills the exact
coverage field, and source well-formedness now also derives uniqueness of all
record points, including retroactive empty anchors, rather than accepting it
as a certificate input. The replay is indexed by that same derived list. The
concrete 18-atom `SupportedExecution` discharges this interface and yields a
checked FIFO history.

`MSQueueSourceSchedule` constructs the required whole-carrier atom schedule by
finite topological sorting from an explicit acyclicity proof for the
transitive closure of `PO ∪ ECO`. A common RC11 relation rank discharges this
premise for the concrete witness. The premise is not folded into `Valid`:
general multi-location RC11 candidates can be valid while containing an
alternating cross-location `PO`/`MO` cycle, so an algorithm-specific proof or
an explicit client-admissibility condition is genuinely required.
`MultiLocationRC11ScheduleCounterexample.valid_but_no_respecting_schedule`
machine-checks this separation.

The general replay-invariant lemmas are also checked: in any admitted
atom schedule, an RF source precedes its read, MO and RB edges point forward,
and no write MO-later than that source can already precede the read. Successful
RMW source events are recovered as their immediate MO predecessors. These
`LatestSource` facts form the visibility kernel for the Head/Tail/next prefix
representation proof. Each extracted record is bound to its exact
source point atom and an actual RF source. Every represented write is
classified exhaustively as a location initializer or the exact point of a
CAS-backed structural record; site-specific refinements reduce these to
`next` links, Tail advances, and Head advances. Checked compare operands then
give recursive immediate-predecessor theorems for Head and Tail and prove that
a successful link follows its `next` initializer, hence one owner location can
be linked at most once.

The source-control side now retains whole-run factors and final-step factors.
For a successful link it reconstructs the exact same-attempt sequence Tail
load, null-next load, stable Tail validation, and link CAS. All three
successful Tail-advance paths are covered separately: enqueue help, dequeue
help, and the enqueue-finishing swing after its own link. Successful Head CAS
records retain the exact Head/Tail/next/stable-Head/payload attempt, while
empty records retain the Head=Tail snapshot and their retroactive null-next
anchor. These events are lifted to global trace order and typed program-order
edges. The resulting schedule lemmas prove that every Tail advance follows
the exact link it traverses, every Head advance follows the exact link it
crosses, and every empty anchor reads from that node's next initializer.

The source-side refinement is now closed for every admitted `AtomSchedule`.
Exact schedule-prefix ordering, reservation uniqueness, the rooted link
graph, and a deterministic `Prefix.Rep` support readiness proofs for link,
Tail, Head, and empty records. The Head proof retains the already constructed
prefix replay as historical evidence; this is essential because a final
projection invariant alone does not imply that every earlier Head transition
was ready when it occurred. `AtomSchedule.recordReady` dispatches all four
cases, and generic atom-prefix induction derives `canonicalReplay`,
`canonicalCertificate`, and legal FIFO commits without an externally supplied
replay or final state.

RC11 `Valid` still does not make raw cross-thread source enumeration a
chronological schedule. The theorem therefore quantifies over an explicit
`AtomSchedule`; the existing topological constructor supplies one from the
stronger `PO ∪ ECO` acyclicity premise. General non-atomic payload
publication is also still represented by the explicit
`SourceWellFormed.payloadReadInitialized` contract rather than a derived HB
theorem.

M3 is now closed. The source method trace proves history well-formedness and
the standard finite completion. `AtomSchedule.scheduleEquivalent` proves that
an RC11-respecting schedule preserves every client's source commit order,
including the retroactive empty-dequeue anchor. Same-thread real time follows
from source control flow; cross-thread client time remains explicit because it
is not an RC11 edge. `AtomSchedule.linearizable` then combines these results
with canonical FIFO replay into the final finite `HW.Linearizable` witness.

### M4 -- Infinite RC11 carrier and visibility

**Status: complete for the explicit reclamation-free queue model.**

- **Completed:** restrict one global event stream, RF lookup, and per-location
  MO relation to a `SupportedExecution` at every finite prefix.
- **Completed:** instantiate successful CAS, every site modification, and
  matching attempts at the exact `.head`, `.tail`, or `.next node` site.
- **Completed:** define position-indexed per-site `FromReadFair` as the exact
  prefix-finite `fr` assumption consumed by visibility, define conventional
  `MemoryFair` as paired prefix-finite `mo`/`fr`, and derive the former from
  the latter.
- **Completed:** derive `SelectedSiteVisibilityFair`: once a represented site
  stops being modified, all sufficiently late reads at that site observe the
  maximal write of the cutoff prefix.
- **Completed:** lift pointwise selected-site visibility to one uniform cutoff
  and one `stableValueAt` assignment for every later atomic read. Later read
  sites are proved to be represented at the stabilization prefix rather than
  assumed to belong to a fixed global site universe.
- **Completed:** prove response-free all-site stabilization. Weak thread
  fairness excludes later abstract commits; canonical structural replay
  bounds successful Tail advances by the already accumulated link count; and
  source control permits at most one fresh `next` initialization per finite
  thread. A common later cutoff therefore has no modification at any logical
  queue site.

### M5 -- Site obligation and final theorem

**Status: complete for the theorem chain and both infinite witnesses.**

- **Completed:** retain the reusable non-circular `ProgressObligations`
  interface: every response-free active suffix selects a thread, cutoff, and
  one exact site with no later modification and arbitrarily late matching
  attempts.
- **Completed:** prove the queue control step. Under stable observations and
  weak thread fairness, a continuously active owner cannot decrease the
  finite stale-cache/aligned-control rank forever, so matching CAS attempts
  occur arbitrarily late.
- **Completed:** prove that every such later matching event is an atomic read
  at a site represented by the finite stabilization prefix. A finite-list
  infinitely-often pigeonhole lemma then fixes one site, rather than allowing
  the witness site to vary with time.
- **Completed:** derive `ProgressObligations` from `PrefixAtomSchedules`, weak
  thread fairness, and `SelectedSiteVisibilityFair`, with public wrappers for
  exact `FromReadFair` and conventional `MemoryFair` assumptions.
- **Completed:** apply `SiteProgressRule` to obtain system response progress
  and combine it with finite-prefix FIFO linearizability. The public
  `MSQueueFairLockFreedom` module exposes
  `linearizableLockFree_of_fairness`, whose assumptions are finite-prefix
  client-compatible schedules, weak thread fairness, per-site RC11 memory
  fairness, and independent per-site weak-CAS justice. It no longer accepts a
  packaged `ProgressObligations` premise.
- **Completed:** construct a coherent all-spurious queue execution satisfying
  both prefix-schedule layers, weak thread fairness, `MemoryFair`,
  `FromReadFair`, selected-site visibility, and the derived
  `ProgressObligations`, while refuting primitive justice and system response
  progress at `.next 0`.
- **Completed:** `MSQueueInfiniteWitnessExecution` packages the successful
  source and valid finite prefixes as one coherent `InfiniteRC11Execution`.
  `MSQueueInfiniteWitnessFairness` proves both prefix-schedule layers, thread
  and memory fairness, selected-site visibility, derived obligations,
  recurring demand, same-site matching-attempt-to-success justice, and
  arbitrarily late successes and responses.
  `successfulAssumptionsJointlySatisfiable` is the headline joint witness,
  while `successfulWitness_linearizableLongRun` applies
  `linearizableLongRun_of_fairness`.

The earlier conditional composition theorem remains available:

```lean
theorem linearizableLockFree_of_siteJustice
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (obligations : execution.ProgressObligations)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees
```

The completed public fairness theorem has the following shape:

```lean
theorem linearizableLockFree_of_fairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees
```

The exact dependency is also exposed by
`linearizableLockFree_of_fromReadFairness`, which replaces `MemoryFair` with
`FromReadFair`. Primitive weak-CAS justice deliberately remains independent:
the all-spurious witness satisfies scheduler and memory fairness but refutes
justice and system response progress.

## Claim boundary

The intended contribution is not the first Michael--Scott safety or
lock-freedom proof. The candidate conjunction, requiring a fresh literature
audit, is:

> An explicit reclamation-free RC11 Michael--Scott queue with genuinely weak
> CAS, per-location primitive justice separated from scheduler and memory
> fairness, finite-prefix Herlihy--Wing linearizability, an integrated
> site-specific spurious-failure separation, and conditional unbounded system
> response progress.

Excluded from the first result:

- memory reclamation, `free`, address reuse, and ABA safety;
- allocation failure or allocator progress;
- wait-freedom or per-operation starvation-freedom;
- minimal memory orders or minimal justice assumptions;
- full ISO C semantics, compiler correctness, or physical-hardware proof; and
- one projectively coherent linearization of the complete infinite history.

## Verification gates

Each milestone must pass:

1. full Lean build with no `sorry`, `admit`, project axiom, or `unsafe` proof;
2. public theorem-surface build;
3. positive joint-satisfiability witness;
4. negative independence witness using the same predicates as the positive
   result;
5. clean-clone verification and independent MSI build; and
6. claim-specific primary-source and external expert review before publication.
