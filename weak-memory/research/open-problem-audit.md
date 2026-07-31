# Open-Problem Audit for the Weak-Memory Project

**Audit date:** 2026-07-30
**Scope:** mathematical software theory, C11/RC11 concurrency, liveness,
linearizability, and safe memory reclamation
**Status:** literature-first research triage; no novelty claim in this document
is a proof that no unpublished or undiscovered result exists

**Implementation update (2026-07-31):** the Rank 1 core theorem is now
machine-checked for the repository's explicit, finite-thread,
reclamation-free `TreiberC11V1` model. The development separates thread,
memory, and primitive weak-CAS fairness; proves an all-spurious independence
counterexample inside a coherent Treiber/RC11 carrier with fully verified raw
prefixes; derives generic CAS-loop progress; and proves
infinitely many responses under recurring pending push/pop demand. A single
forever-stuck call satisfies that state-based demand premise, so the premise
does not presuppose fresh invocations or responses. A concrete one-thread
execution now witnesses joint satisfiability of the full carrier, recurring
demand, thread fairness, prefix-finite `mo`/`fr`, and weak-CAS justice, and the
final theorem is applied to that witness. A second, Treiber-independent
weak-CAS increment loop now consumes the reusable rule and has separate
success-rich and all-spurious executions. The exact Treiber dependency has
also been sharpened to prefix-finite `fr`; the standard paired `mo`/`fr`
memory-fairness theorem is retained as a corollary. The strong-CAS variant
remains future work. The primary-source search was refreshed on the audit
date; it must still be repeated at submission time.

**Post-audit extension (2026-07-31):** the previously single-site generic rule
has been conservatively generalized to a site-indexed rule with explicit
generation-changing modifications, an eventual stabilization cutoff, and a
helper-thread witness. A two-site operational client now has success-rich,
all-spurious, and wrong-site executions. This extension is an implementation
milestone, not a retrospective change to the audited Treiber novelty claim.
The realistic next client is a reclamation-free Michael--Scott queue; its
separate roadmap and claim boundary are in
[`site-indexed-progress-roadmap.md`](site-indexed-progress-roadmap.md).

## 1. Purpose

The purpose of this project is not merely to verify another implementation of
Treiber's stack. It is to solve a research problem that is still unresolved.
This audit separates:

1. results already present in the repository;
2. results already established in the literature;
3. explicit open directions stated by authors;
4. plausible gaps inferred from the intersection of existing results; and
5. exact theorem targets that can be falsified before a large development is
   attempted.

The recommended target is:

> **Develop a mechanized fairness theory for weak compare-and-exchange under
> RC11, prove that thread fairness plus memory fairness is insufficient, and
> derive an unbounded lock-freedom theorem for weak-CAS Treiber executions under
> an explicit primitive-progress contract.**

Treiber's stack is the first case study, not the whole claimed contribution.
The intended reusable contribution is a liveness rule for a class of weak-CAS
retry loops.

## 2. Evidence Policy

Candidates are classified by the strongest evidence currently available.

- **Tier A — author-stated open direction.** A primary source explicitly calls
  the issue future work, an open problem, or an unhandled limitation, and the
  audit found no later primary source closing the exact issue.
- **Tier B — triangulated gap.** Adjacent pieces are solved independently, but
  no primary source found in the audit combines them. This is evidence of a
  plausible gap, not permission to write "the problem is known to be open."
- **Tier C — engineering opportunity.** The work may be useful, but the
  theorem-level novelty is uncertain or too dependent on implementation work.

Before any eventual novelty claim, the search must be repeated against papers,
preprints, artifacts, theses, and author repositories current at submission
time. Negative search results are never treated as proofs of absence.

## 3. What the Repository Already Establishes

The repository proves a substantial finite-execution safety result for an
explicit, versioned semantics:

```text
finite TreiberC11V1 source/candidate execution
        + RC11 validity
        + client contract and order compatibility
                         |
                         v
certified operational replay
        + node safety
        + Herlihy--Wing linearizability
```

It also contains:

- a hash-pinned Clang-AST extraction boundary for `c/treiber.c`;
- explicit release/acquire and weak-CAS control flow;
- RC11 consistency, graph typing, replay, and history bridges;
- GenMC and Relinche checks for bounded clients; and
- a precise exclusion of node reclamation, address reuse, and ABA.

The original finite safety infrastructure has now been extended with an
explicit infinite-execution theorem. The project still does not provide:

- a proof from a full ISO C semantics;
- an unconditional portable lock-freedom theorem for ISO C weak CAS;
- a memory-reclamation theorem; or
- evidence that Treiber safety under relaxed memory was previously open.

## 4. Results That Must Not Be Claimed as New

The following problem statements are already solved, at least in a form strong
enough to invalidate a broad novelty claim.

### 4.1 Relaxed-memory Treiber safety and linearizability

COMPASS and the later proof-recipe work give mechanized iRC11 proofs for
Treiber-style stacks and more complicated libraries. Therefore, "the first
mechanized RC11 Treiber linearizability proof" is not an available claim.

### 4.2 Treiber lock-freedom under interleaving/SC semantics

Classical and mechanized work already proves non-blocking properties of
Treiber-style algorithms under interleaving semantics. Weak memory, infinite
execution semantics, and primitive progress must be essential to any new
claim.

### 4.3 Weak-memory fairness in general

Lahav et al. formalized thread and memory fairness for infinite executions.
Lee et al.'s mechanized Fair Operational Semantics can express arbitrary
custom fairness dimensions and combines scheduler, lock, and weak-memory
fairness in one Coq case study. Abdulla et al. give a uniform operational
framework combining transition and memory fairness. Bargmann and Wehrheim
later presented the first proof calculus specifically for weak-memory
liveness, and Haas et al. developed fair recurrence sets for axiomatic memory
models. A new result cannot be advertised as the first theory, mechanization,
or combination of fairness under weak memory, nor as the first weak-memory
liveness calculus.

### 4.4 Bounded weak-memory checking

GenMC, Dartagnan, and Relinche already support strong bounded analyses. Bounded
termination or bounded linearizability is not an unbounded lock-freedom proof.

### 4.5 Hazard-pointer Treiber verification under SC

Jung et al. mechanized modular hazard-pointer reclamation and applied it to
Treiber's stack under sequential consistency. The missing part is not hazard
pointers alone; it is their composition with realistic relaxed memory,
allocation lifetime, reuse, and the desired client specification.

## 5. Primary Recommendation: Fair Weak CAS under RC11

### 5.1 Why this is a defensible open direction

The C11 and C23 drafts permit a weak compare-and-exchange operation to fail
spuriously. They do not impose a normative rule that prevents every attempt in
an infinite retry loop from failing spuriously.

The current implementation uses:

```c
atomic_compare_exchange_weak_explicit(...)
```

Consequently, a portable guarantee based only on ISO C cannot rule out
implementation behavior in which:

1. `head` never changes;
2. the expected value equals `head` at every attempt;
3. every weak CAS fails spuriously;
4. an operation retries forever; and
5. no stack operation completes.

Thus the following unconditional statement is not derivable from ISO C:

> Every fair ISO C execution of the current source is lock-free.

Lahav et al. explicitly identify fairness for weak RMW operations as future
work. Their memory-fairness condition does not rule out infinite spurious weak
CAS failures. Lee et al.'s fully mechanized general fairness framework could
express the desired primitive contract in principle—their lottery example
already excludes an infinite sequence of false outcomes—but it does not
instantiate weak CAS, prefix-finite axiomatic memory fairness, or Treiber.
Abdulla et al. treat RMWs atomically without a separate spurious-failure
dimension. The 2026 weak-memory liveness calculus covers loads, stores, and
fetch-and-add, and its principal case study is a ticket lock; it does not model
weak CAS.

Haas et al. are the closest later overlap. They explicitly mention weak-CAS
and LL/SC spurious failure as another fairness dimension, then omit it from the
remainder of their theory while stating that inclusion would be
straightforward. Their Dartagnan experiments are bounded and do not establish
an unbounded Treiber theorem. This source prevents a claim that weak-CAS
fairness was previously unidentified or inexpressible.

The core motivation retains **Tier A provenance** from Lahav et al.'s stated
future work. The exact mechanized combination with Treiber is a **Tier B
intersection claim**, not proof that the problem remained universally open.

### 5.2 Research question

> What is the weakest useful, compositional fairness condition for weak
> read-modify-write primitives that is separate from scheduler fairness and
> memory-propagation fairness, admits an operational/declarative account, and
> suffices to recover standard lock-freedom proofs for weak-CAS retry loops
> under RC11?

### 5.3 Initial primitive-progress condition

The first condition to investigate is weak justice for an enabled successful
CAS transition:

```text
WeakCASJustice(run) :=
  if, from some point onward,
    - an active thread is scheduled infinitely often at one weak-CAS site,
    - the compared object and expected value remain equal, and
    - the successful CAS transition remains continuously enabled,
  then one of those attempts eventually succeeds.
```

An execution-graph formulation suitable for the current model is:

```text
NoStablePureSpuriousSuffix(run) :=
  no invocation has an infinite suffix in which
    - the target atomic object is unchanged,
    - infinitely many attempts compare equal, and
    - all such attempts fail spuriously.
```

These conditions are not claimed to be minimal.  For the Treiber
specialization, Lean proves that primitive justice is equivalent to excluding
a stable suffix with arbitrarily late compare-equal attempts and no successful
CAS.  Comparing that execution-level condition with weaker implementation
contracts remains future work.

### 5.4 Exact negative theorem

The first required theorem should be a counterexample:

> **Memory fairness is insufficient for weak CAS.** There exists a coherent
> infinite `TreiberC11V1` execution whose every raw prefix is a valid
> declarative RC11 execution, which is thread-fair and memory-fair and has
> recurring pending push demand, but in which the supplying write is stable,
> every weak-CAS comparison is equal, every CAS fails spuriously, primitive
> justice is false, and no method responds.

This theorem prevents the project from hiding primitive progress inside RC11
memory fairness and explains why an additional contract is necessary.
`InfiniteSpurious.execution` is the full integrated witness. The earlier
smaller `WeakCAS.AllSpurious.run` remains as an algorithm-independent sanity
check, but the headline independence theorem now uses the same
`InfiniteRC11Execution`, `WeakCASJustice`, and `SystemResponseProgress`
predicates as the positive Treiber result.

### 5.5 Exact generic positive theorem

The implemented reusable layer is
`WeakCAS.ProgressRule.Interface`/`Obligations`.  It abstracts active owners,
method responses, primitive successes, and compare-equal attempts, then proves:

> **Generic weak-CAS system-progress rule.** If every response-free active
> suffix has no primitive success but contains compare-equal attempts
> arbitrarily late, primitive weak-CAS justice forces a later response.

The two suffix obligations are deliberately separate from primitive justice.
The one-location machine derives them from retry control and weak scheduling;
the Treiber instantiation derives them from source control, thread fairness,
prefix-finite RC11 memory fairness, stable RF-source visibility, and retry-seed
preservation.  `TreiberC11V1.progressRuleInterface` is consumed directly by the
generic theorem, so the application is not a parallel toy proof.

The Treiber discharge exposes the standard dichotomy:

```text
infinitely many interfering successful modifications
        => system progress already occurs

only finitely many successful modifications
        => the atomic state eventually stabilizes
        => memory fairness eventually exposes the stable value
        => weak-CAS justice forces a success
```

The rule does not assume method completion, and primitive justice remains
independently falsifiable by the all-spurious execution.
`WeakCASCounter.responseProgress_of_primitiveJustice` is now a second,
Treiber-independent mechanized client. Its transition system includes
invocation, mismatch refresh, spurious failure, and successful increment
steps; it derives the generic obligations and has both a success-rich run and
an all-spurious independence run. This is deliberately a minimal genericity
check, not a second RC11 result: it has one thread, mandatory trace
scheduling, no execution graph, and fuses primitive success with method
response. The current `ProgressRule.Interface` is also system-wide and
single-site: its justice conclusion is some success rather than a success
indexed by the matching attempt's location. That is exact for Treiber's one
`head` and the counter's one location, but a multi-site application needs a
site-indexed refinement. A richer syntactic `StableCASLoop` class remains a
possible generalization.

### 5.6 Exact Treiber theorem

The first application should state true unbounded lock-freedom:

> **Fair-RC11 Treiber lock-freedom.** For every finite number of threads, every
> coherent infinite execution subject to the explicit TreiberC11V1 source
> semantics, finite-prefix RC11 validity, thread fairness, memory fairness, and
> weak-CAS justice has system response progress: from every state containing
> an active operation, some later method returns.

The mechanized proof is slightly stronger than this conventional statement.
`systemResponseProgress_of_fromReadFairness` and
`linearizableLongRun_of_fromReadFairness` require prefix-finite `fr`, not the
full paired prefix-finite `mo`/`fr` condition. The displayed
full-memory-fairness theorem is a corollary retained to match the standard
declarative interface. This proof does not establish that either formulation
is the weakest possible condition.

Under the additional state-based condition that a push or pop is pending at
arbitrarily late states, a corollary gives infinitely many method-return
events.  A single push or pop stuck forever satisfies this pending-demand
condition, so it does not presuppose infinitely many fresh invocations or any
response.

The initial theorem deliberately assumes:

- preallocated nodes;
- no `free`, reallocation, or address reuse;
- no ABA;
- immutable `next` fields after publication; and
- a client discipline matching the current repository.

Pending demand concerns one long-lived stack. It does not mean that node
addresses may be reclaimed and reused.

For a strong-CAS source variant, the spurious-failure premise should disappear,
while the implementation's atomic-operation progress contract remains
explicit.

### 5.7 Composition with current safety

Every finite prefix ending in completed operations should be mapped into the
existing finite `TreiberC11V1` semantics. The final result should combine:

```text
all finite prefixes are safe and linearizable
                    +
every fair active state has a later response
                    =
finite-prefix linearizability plus system lock-freedom

recurring pending push/pop demand
                    +
system lock-freedom
                    =
responses occur arbitrarily late
```

This bridge is important: a separate liveness toy model would fail to capitalize
on the current development.

The repository now also supplies a concrete non-vacuity witness for this
composition. One source thread repeatedly pushes fresh nodes using a relaxed
head load and a successful release weak CAS. Every raw source prefix is
projected to a full `DeclarativeExecution` using restrictions of one global RF
function and one global MO relation. Lean proves recurring pending demand,
weak thread fairness, prefix-finite position-indexed `mo` and `fr`, and
primitive weak-CAS justice, then applies
`execution_linearizableLongRun`.

This witness establishes joint satisfiability; it is not a contention
benchmark and does not itself contain spurious failures. Its justice proof is
non-circular because every suffix contains an actual successful primitive CAS.
The integrated `InfiniteSpurious.execution` provides the complementary
negative carrier: its same valid finite-prefix RC11 semantics has thread and
memory fairness plus recurring pending demand, but all compare-equal weak CAS
attempts fail, justice is false, and no response occurs.

### 5.8 Novelty risks and falsification checks

This candidate should be abandoned or reformulated if any of the following is
found:

1. a mechanized result already gives weak-RMW fairness plus unbounded Treiber
   lock-freedom under RC11;
2. the proposed fairness condition is equivalent to assuming method completion;
3. the generic rule cannot cover more than the exact Treiber source;
4. RC11 memory behavior is irrelevant after the model is stated precisely,
   leaving only a classical SC argument with a renamed assumption; or
5. finite-prefix composition requires a second incompatible semantics.

To reduce the "one case study" risk, the generic rule should be instantiated on
at least one additional weak-CAS loop or be formulated for a clearly reusable
semantic class.

### 5.9 Literature refresh and current novelty position

A primary-source search refreshed through **2026-07-30** found no result that
closes the exact target combination. The nearest results delimit the claim:

| Work | What it already supplies | What it does not supply |
|---|---|---|
| Lahav et al. (OOPSLA 2021) | Prefix-finite declarative memory fairness and RC11 liveness examples | Weak-RMW fairness, which it explicitly leaves for future work |
| Lee et al. (PLDI 2023) | A Coq framework for arbitrary and composed fairness, including weak-memory examples | A weak-CAS or Treiber instantiation and the axiomatic `mo`/`fr` carrier used here |
| Abdulla et al. (CAV 2023) | Uniform operational transition and memory fairness with atomic RMWs | A distinct spurious-failure condition or Treiber theorem |
| Haas et al. (POPL 2026) | Fair axiomatic recurrence sets and bounded Dartagnan experiments | Weak-CAS fairness in the developed theory and an unbounded Treiber result |
| Bargmann and Wehrheim (FM 2026) | A weak-memory liveness calculus and ticket-lock starvation freedom | Weak CAS, Treiber, or an all-spurious separation theorem |
| RC11 Treiber logics and tools | Mechanized or checked safety and linearizability | The target infinite-execution liveness composition |
| Classical Treiber liveness proofs | Lock-freedom under interleaving/strong-CAS settings | RC11 memory fairness and weak-CAS spurious failure |

The strongest defensible categorical wording is deliberately narrow:

> To the best of our knowledge, based on literature searched through 30 July
> 2026, this is the first machine-checked result for an explicit finite-thread,
> reclamation-free RC11 Treiber model that treats weak-CAS spurious-failure
> justice as a primitive assumption distinct from scheduler and memory
> fairness, proves through a coherent all-spurious Treiber execution with
> RC11-valid finite prefixes that the latter two assumptions are
> insufficient, and composes all three assumptions to derive system-wide
> response progress.

The safer formulation, preferred until an external expert review and a
submission-time search, is:

> We give a machine-checked closure, for an explicit reclamation-free RC11
> Treiber model, of the weak-RMW fairness issue isolated by Lahav et al. Our
> search through 30 July 2026 found no prior result with this exact
> combination. The contribution is the explicit separation, independence
> witness, and composition of primitive weak-CAS justice with scheduler and
> memory fairness—not a new general fairness formalism or a first Treiber
> safety proof.

Negative search results are not a priority proof. The first wording must be
rechecked at submission time.

## 6. Second Recommendation: Hazard Pointers under RC11

### 6.1 Evidence

This direction also has **Tier A evidence**.

- The 2023 modular reclamation work assumes sequential consistency and
  explicitly proposes adaptation to iRC11.
- The 2025 general-purpose RCU work solves the RCU part under iRC11 and points
  to hazard pointers as a later application.
- The 2025 hazard-pointer traversal work is mechanized in SC HeapLang, not
  iRC11.
- Relaxed Treiber linearizability without reclamation is already solved.

The audit found no mechanized proof combining:

```text
hazard-pointer Treiber
    + actual free/reallocation and address reuse
    + RC11/iRC11
    + no use-after-free
    + reuse-ABA prevention
    + linearizability
```

### 6.2 Exact finite theorem

Extend node identity from a raw address to an allocation generation:

```text
NodeId := (address, generation)
```

Add events for allocation, hazard publication, head validation, retirement,
hazard scanning, freeing, and reallocation. Then prove for every finite valid
execution:

1. **No use-after-free:** every dereference targets the currently live
   generation of its allocation.
2. **No reuse ABA:** a successful head CAS cannot confuse two generations that
   occupy the same address.
3. **Linearizability preservation:** projection to stack operations satisfies
   the existing Herlihy--Wing specification.

The crucial change is to remove the current global no-reuse assumption and
derive the needed lifetime fact from the hazard-pointer protocol.

### 6.3 Smallest meaningful subproblem

The best first lemma is a relaxed-memory protect-or-observe dichotomy:

```text
the reader's validation observes the unlink
                         OR
the reclaimer's scan observes the hazard publication
```

Under the sufficient memory-order/fence assignment, one side must observe the
other. Under a deliberately weaker assignment, a generated RC11 counterexample
should show that both can miss.

### 6.4 Main risks

- The model expansion is much larger than the liveness extension.
- Pointer lifetime and provenance must be versioned precisely.
- The current single-publication/no-reuse invariants cannot simply be retained.
- Another research group has explicitly announced this direction, creating a
  higher race risk.
- Safety, eventual reclamation, bounded unreclaimed memory, and lock-freedom
  are separate theorems and must not be conflated.

## 7. Other Candidates

### 7.1 Certified C-Core to RC11 refinement — Tier B

Construct a reusable, mechanized refinement from a meaningful atomic-C core
language with simple structs, pointers, immutable non-atomic fields, and weak
CAS into the current RC11 execution-graph interface.

This would remove a real trust boundary, but it has substantial overlap risk:
operational C11 semantics, Cerberus, Cerberus-BMC, GenMC's LLVM front end, and
IMM already solve important adjacent pieces. A hand-transcribed AST or a
Treiber-specific parser would not be enough for a strong novelty claim.

### 7.2 RC11-to-IMM/ARM history preservation — Tier B

Prove that compilation preserves method histories, successful linearization
events, client order, and immutable-field observations for the non-SC Treiber
fragment.

This could connect source-level linearizability to hardware executions, but the
existing compilation developments are large, use another prover, and omit
features relevant to the current source. It is high impact and very high scope.

### 7.3 Certified relaxed-linearizability checking or synthesis — Tier A/C

Possible exact targets include:

- proof-producing Relinche/GenMC coverage and linearization certificates; or
- Pareto-minimal RC11 memory-order synthesis for all clients up to an explicit
  invocation bound.

Relinche explicitly leaves soundness/scalability tradeoffs and integrations as
future work. However, this area is crowded by existing checking and synthesis
tools. The distinguishing theorem would have to include relaxed
linearizability and independently checkable coverage or minimality, not merely
per-execution certificates.

## 8. Ranking

| Rank | Candidate | Evidence | Fit to current Lean work | Scope | Main risk |
|---:|---|---|---|---|---|
| 1 | Weak-RMW fairness plus unbounded Treiber lock-freedom | Tier A core / Tier B application | Excellent | Medium | Too Treiber-specific or fairness too strong |
| 2 | Hazard-pointer Treiber with reuse under RC11 | Tier A | Very good | High | Large model expansion and publication race |
| 3 | Certified C-Core to RC11 refinement | Tier B | Excellent | Very high | Adjacent semantics/front-end work already exists |
| 4 | Certified bounded linearizability or order synthesis | Tier A/C | Moderate | High | Crowded tool space; bounded result |
| 5 | RC11-to-IMM/ARM history preservation | Tier B | Moderate | Very high | Cross-prover and semantic scale |

The recommended order is to attack Rank 1 first while retaining Rank 2 as the
next independent research program.

## 9. First Research Milestones for Rank 1

**Lean status (2026-07-30):** the core exit criteria of Milestones A, B, and C
are discharged for the explicit `TreiberC11V1` model by
`InfiniteRC11Execution.linearizableLockFree_of_fairness`; recurring pending
push/pop demand gives the separate
`InfiniteRC11Execution.linearizableLongRun_of_fairness` corollary. The
concrete `InfiniteWitness.execution` inhabits the full fair infinite carrier
and satisfies the corollary. `WeakCASCounter` supplies the additional minimal
algorithmic instantiation. The strong-CAS corollary and a richer syntactic
stable-loop class remain open extensions.

### Milestone A — semantic separation

1. Define infinite executions and finite prefixes.
2. Define method invocations, returns, active operations, and system
   lock-freedom.
3. Define thread fairness, RC11 memory fairness, and weak-CAS fairness as three
   separate predicates.
4. Construct and mechanize the all-spurious counterexample.

**Exit criterion:** Lean proves that thread fairness plus memory fairness does
not imply weak-CAS progress.

### Milestone B — generic progress rule

1. Define a reusable weak-CAS progress interface and its concrete obligations.
2. Prove the interference-or-stability argument in the Treiber discharge.
3. Derive system response progress and its unbounded-response corollary.
4. Compare per-thread weak justice with weaker system-wide CAS progress.

**Exit criterion:** the theorem does not mention Treiber-specific stack
invariants.

### Milestone C — Treiber composition

1. Instantiate the generic rule for `push` and `pop`.
2. Map every completed finite prefix to the existing safety semantics.
3. Prove unbounded system lock-freedom.
4. Prove the strong-CAS corollary.
5. Add bounded counterexample harnesses only as validation, not as the proof.

**Exit criterion:** one public theorem bundles explicit assumptions,
finite-prefix linearizability, and infinite-execution lock-freedom.

## 10. Claim Discipline

The literature review was refreshed on 2026-07-30. Until it is independently
reviewed and repeated at submission time, use:

> We give a machine-checked closure, for an explicit reclamation-free RC11
> Treiber model, of the weak-RMW fairness issue isolated by Lahav et al. The
> result separates primitive weak-CAS justice from scheduler and memory
> fairness inside one coherent infinite Treiber/RC11 carrier, proves their
> independence with a full all-spurious execution, and composes them into
> conditional system-wide response progress.

Do not use:

> We are solving the open problem of Treiber verification.

Also do not claim the first general fairness framework, the first
weak-memory-liveness mechanization, or the first framework capable of
expressing weak-CAS fairness. Fair Operational Semantics is already general
enough to express arbitrary custom fairness, and Haas et al. explicitly note
that spurious-instruction fairness can be included in their axiomatic theory.

Do not claim portable ISO C lock-freedom unless the theorem explicitly states:

- the selected C standard/version;
- atomic-pointer lock-freedom or the implementation contract;
- primitive termination;
- weak-CAS spurious-failure progress;
- scheduler fairness;
- memory fairness; and
- memory-management assumptions.

## 11. Primary Sources

### Standards and primitive progress

- ISO C11 committee draft N1570, §7.17.7.4:
  <https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf>
- ISO C23 committee draft N3096, §7.17.7.4:
  <https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf>
- C2Y working draft N3854, §7.17.7.5:
  <https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3854.pdf>
- C++ library issue 2075, documenting the weak-CAS progress ambiguity:
  <https://cplusplus.github.io/LWG/issue2075>
- WG21 N3927, adopted lock-free progress wording:
  <https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2014/n3927.html>

### Weak-memory fairness and liveness

- Lahav et al., *Making Weak Memory Models Fair*, OOPSLA 2021:
  <https://arxiv.org/pdf/2012.01067>
- Lee et al., *Fair Operational Semantics*, PLDI 2023:
  <https://sf.snu.ac.kr/publications/fairness.pdf>
- Lee et al., mechanized Coq artifact for *Fair Operational Semantics*:
  <https://github.com/snu-sf/fairness>
- Abdulla et al., *Overcoming Memory Weakness with Unified Fairness*,
  CAV 2023:
  <https://arxiv.org/pdf/2305.17605>
- Bargmann and Wehrheim, *Towards Proving Liveness on Weak Memory*, FM 2026:
  <https://arxiv.org/pdf/2602.19609>
- Haas et al., *Recurrence Sets for Proving Fair Non-termination under
  Axiomatic Memory Consistency Models*, POPL 2026:
  <https://hernanponcedeleon.github.io/pdfs/popl2026.pdf>
- Gotsman et al., *Proving That Non-Blocking Algorithms Don't Block*,
  POPL 2009:
  <https://people.mpi-sws.org/~viktor/papers/popl2009-nonblocking.pdf>

### Relaxed-memory safety and linearizability

- Lahav et al., *Repairing Sequential Consistency in C/C++11*, PLDI 2017:
  <https://plv.mpi-sws.org/scfix/full.pdf>
- Dang et al., *COMPASS: Strong and Compositional Library Specifications in
  Relaxed Memory Separation Logic*, PLDI 2022:
  <https://plv.mpi-sws.org/compass/paper.pdf>
- Park et al., *A Proof Recipe for Linearizability in Relaxed Memory Separation
  Logic*, PLDI 2024:
  <https://iris-project.org/pdfs/2024-pldi-proof-recipe.pdf>
- Golovin et al., *Relinche: Automatically Checking Linearizability under
  Relaxed Memory*, POPL 2025:
  <https://plv.mpi-sws.org/genmc/popl2025-relinche.pdf>
- Dalvandi and Dongol, *Verifying C11-Style Weak Memory Libraries via
  Refinement*:
  <https://arxiv.org/pdf/2108.06944>
- Margalit et al., *Dynamic Robustness Verification against Weak Memory*,
  PLDI 2025:
  <https://arxiv.org/pdf/2504.15036>
- GenMC project and formalization links:
  <https://plv.mpi-sws.org/genmc/>

### Safe memory reclamation

- Michael, *Hazard Pointers: Safe Memory Reclamation for Lock-Free Objects*:
  <https://www.cs.otago.ac.nz/cosc440/readings/hazard-pointers.pdf>
- Jung et al., *Modular Verification of Safe Memory Reclamation in Concurrent
  Separation Logic*, OOPSLA 2023:
  <https://iris-project.org/pdfs/2023-oopsla-reclamation.pdf>
- Jung et al., *Verifying General-Purpose RCU for Reclamation in Relaxed Memory
  Separation Logic*, PLDI 2025:
  <https://iris-project.org/pdfs/2025-pldi-weak-smr.pdf>
- Lee et al., *Leveraging Immutability to Validate Hazard Pointers for
  Optimistic Traversals*, PLDI 2025:
  <https://iris-project.org/pdfs/2025-pldi-hp-revisited.pdf>
- Dang et al., *RustBelt Meets Relaxed Memory*, POPL 2020:
  <https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf>

### Source and compilation semantics

- Nienhuis et al., *An Operational Semantics for C/C++11 Concurrency*,
  OOPSLA 2016:
  <https://www.cl.cam.ac.uk/~pes20/rems/papers/nienhuis-oopsla-2016.pdf>
- Lau et al., *Cerberus-BMC: A Principled Reference Semantics and Exploration
  Tool for Concurrent and Sequential C*, CAV 2019:
  <https://www.cl.cam.ac.uk/~pes20/cerberus/bmc-cerberus.pdf>
- Podkopaev et al., *Bridging the Gap between Programming Languages and
  Hardware Weak Memory Models*, POPL 2019:
  <https://plv.mpi-sws.org/imm/paper.pdf>
