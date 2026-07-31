# External Review Packet: Weak-CAS Treiber under RC11

## Review requested

We are seeking an adversarial prior-art and model-fidelity review of one narrow
machine-checked result. We are not asking for endorsement, authorship, or an
exposition review. A claim-defeating reference, hidden artifact theorem, or
counterexample to the model is more useful than general encouragement.
The present audit cutoff is 2026-07-31.

The internal snapshot supplied for review contains 230 canonical sources,
240 canonical screening decisions, 110 closest works, and 122 theorem-level
comparisons. Ten checksum-bound overlays record 4,267 decisions across
overlapping immutable citation queues; the closing 179-work queue produced no
new closest-work promotion. These figures document the completed internal
screen, not independent confirmation: every decision remains human-pending,
provider and identifier gaps leave zero protocol-complete snowballing rounds,
and the packet has not yet received an external expert verdict.

Please assess the exact conjunction below, not any broader “first” claim. For a
negative verdict, please give the closest available theorem/definition and,
where possible, its section, theorem number, artifact version, file, and line
or declaration name. A result subsumes the claim only if its model and
quantifiers translate to the target without adding a stronger progress
assumption.

Suggested verdicts are:

1. **Defeated/subsumed:** an earlier result covers the full conjunction or a
   formally stronger one.
2. **Must narrow:** one or more claimed dimensions are already established or
   the wording overstates the checked result.
3. **No defeating result known:** after considering the mandatory comparisons
   below, no earlier theorem covering the full conjunction is known to you.
4. **Model objection:** the theorem is checked as stated, but an assumption,
   definition, or claimed interpretation is technically unsound or misleading.

“No defeating result known” is evidence from one reviewer, not a priority
certificate. Silence will not be treated as agreement.

## Candidate claim under review

> To the best of our knowledge, this is the first machine-checked result for
> the full conjunction of: an explicit finite-thread, reclamation-free RC11
> Treiber model; genuinely weak CAS; primitive weak-CAS justice distinct from
> scheduler and memory fairness; an RC11-valid all-spurious Treiber execution
> proving that distinction; unbounded system-wide response progress; and
> finite-prefix linearizability.

This is a candidate, date-bounded statement. It will be narrowed or withdrawn
if an earlier result subsumes it. The factual contribution statement does not
depend on priority.

The candidate is not a claim to the first result proving Treiber safety and
liveness together. Liang et al. (S53/PA42) already prove Treiber
linearizability and lock-freedom together in an atomic, exact-match strong-CAS
setting. The question under review is only whether an earlier result covers the
full six-part conjunction: reclamation-free RC11 Treiber, genuinely weak CAS,
separate primitive justice, an integrated all-spurious separation, unbounded
system-wide response progress, and machine-checked finite-prefix
linearizability composition.

Nor is this a claim to the first weak-memory model or tool supporting genuine
weak CAS. Margalit et al.'s RSan (S59/PA47) expressly supports weak CAS that may
fail after reading the expected value under the C11-style RC20 model. Its result
is dynamic robustness checking, not Treiber liveness or fairness-separated
progress.

## Exact target to compare

The target is the conjunction of all rows below:

| Dimension | Checked target |
|---|---|
| Program | Explicit finite-thread, reclamation-free Treiber push/pop model |
| Memory | One coherent infinite carrier whose every raw finite prefix is a valid declarative RC11 execution |
| Primitive | Weak compare-and-exchange permits compare-equal spurious failure |
| Scheduler assumption | Weak fairness for continuously active source threads |
| Memory assumption | Prefix-finite from-read in the exact theorem; paired prefix-finite modification-order/from-read as a conventional corollary |
| Primitive assumption | Weak-CAS justice is stated separately and is not derived from scheduler or memory fairness |
| Positive conclusion | From every state with an active operation, some method response occurs later or at that state |
| Unbounded corollary | Under recurring pending push/pop demand, responses occur arbitrarily late |
| Negative separation | One integrated all-spurious Treiber execution satisfies thread and paired memory fairness but violates primitive justice and response progress |
| Safety composition | Every finite prefix receives the existing Herlihy--Wing linearizability package |
| Mechanization | Public Lean theorem surface; no `sorry`, project `axiom`, `admit`, or `unsafe` declaration in the result modules |

The progress conclusion is system-wide lock-freedom. It does not promise that
the same operation, or every operation, completes.

## Result summary

- **Positive:** weak thread fairness, prefix-finite from-read, and primitive
  weak-CAS justice imply system-wide response progress for the versioned
  Treiber model.
- **Negative:** one coherent all-spurious execution in the same carrier has
  RC11-valid finite prefixes, thread fairness, and paired memory fairness, but
  lacks primitive justice and response progress.
- **Safety:** every finite prefix receives the existing
  Herlihy--Wing-linearizability package; the result does not choose one
  projectively coherent linearization order for the entire infinite history.
- **Reuse:** a separate weak-CAS counter instantiates the generic single-site,
  system-wide progress rule. It is reuse evidence, not a second RC11 case
  study.

Historical wording is deliberately narrow.
[WG21 N2427](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2007/n2427.html),
[N2748](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2008/n2748.html),
[N3209](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3209.htm),
[Library issue 2075](https://timsong-cpp.github.io/lwg-issues/2075),
[N3927](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2014/n3927.html),
and the later C++ working draft already document spurious-CAS retry-loop
progress, the introduction of weak/strong API names, scheduler isolation
versus implementation guarantees, and should-level encouragement of eventual
non-spurious success. They do not provide a formal primitive-justice trace
assumption or an RC11/Treiber theorem. The candidate therefore makes no
priority claim for recognizing that practical issue.

## Core falsification comparisons

The thirty-four expanded entries below are the highest-severity review set, not the
entire bibliography. The linked [prior-art matrix](prior-art-matrix.csv)
contains 122 theorem-level comparisons for all 110 current closest works, and
the [artifact audit](artifact-audit.md) gives exact checksums, source paths,
line references, and source-level comparisons for the eleven locally retained
artifact bundles. A missing work anywhere in that larger set is a
claim-relevant finding even if it is not expanded below.

### 1. Fair Operational Semantics (FOS)

- Paper: [Lee et al., *Fair Operational Semantics*](https://sf.snu.ac.kr/publications/fairness.pdf);
  [DOI 10.1145/3591253](https://doi.org/10.1145/3591253).
- Artifact: [Zenodo 7711063](https://doi.org/10.5281/zenodo.7711063).
- Known overlap: the Coq artifact already defines an address-indexed
  `cas_weak` whose spurious branch emits a failure fairness event. Its
  well-founded fairness update semantically excludes an infinite
  fixed-address all-spurious suffix on a fair behavior. FOS also supplies a
  mechanized fair weak-memory ticket-lock/client refinement.
- Recorded gap: `cas_weak` appears only at its definition and registration;
  the weak-memory case uses load/store/FAA, not CAS. No Treiber, RC11
  execution-graph separation, or system-response theorem was found.

Please test:

1. Is the FOS weak-CAS fairness semantics equivalent to, stronger than, or
   weaker than the target `WeakCASJustice`?
2. Is there a theorem, later branch, thesis, or client that instantiates
   `cas_weak` on Treiber or another CAS retry loop?
3. Does FOS already prove independence from scheduler and memory fairness, or
   only provide a composable primitive event mechanism?
4. Would the target theorem be a direct instance of a published FOS theorem,
   rather than a new checked algorithm/model composition?

### 2. Lilo

- Paper: [Lee et al., *Lilo*](https://iris-project.org/pdfs/2025-oopsla-lilo.pdf);
  [DOI 10.1145/3720525](https://doi.org/10.1145/3720525).
- Artifact: [Zenodo record 14927742, version 3](https://doi.org/10.5281/zenodo.14927742).
- Known overlap: Lilo gives Coq-mechanized termination-guaranteeing
  logical-atomic specifications for Treiber push/pop and carries the FOS-style
  fair `cas_weak` definition in the same source tree.
- Recorded gap: Treiber calls strong `"cas"` in a single-global-heap
  interleaving model; repository-wide `cas_weak` search finds only its
  definition and registration. The proof relies on failure indicating
  interference and uses a finite-use obligation.

Please test:

1. Does any Lilo version, branch, supplementary theorem, or downstream client
   connect `cas_weak` to the Treiber proof?
2. Does the finite-use, per-operation specification imply the target's
   unbounded system-wide response property under ongoing demand?
3. Can the co-located fair weak-CAS primitive be substituted for strong CAS
   without a new liveness proof or stronger client obligation?
4. Does Lilo contain a memory-model result that includes the target RC11
   finite-prefix executions?

### 3. Haas et al.

- Paper: [Haas et al., *Recurrence Sets for Proving Fair Non-termination under
  Axiomatic Memory Consistency Models*](https://hernanponcedeleon.github.io/pdfs/popl2026.pdf);
  [DOI 10.1145/3776687](https://doi.org/10.1145/3776687).
- Known overlap: the paper explicitly identifies spurious weak CAS and LL/SC
  as a platform-fairness dimension in an axiomatic weak-memory setting.
- Additional implementation overlap: the paper-era Dartagnan
  `NonTerminationEncoder` forces a potentially recurring
  `RMWStoreExclusive` to execute in the suffix, with the source comment that
  infinite spurious failure is unfair. The paper's public artifact-branch
  snapshot contains this rule, but its C11 frontend hard-codes the corresponding
  LLVM compare-exchange store as strong. Current Dartagnan now compiles LLVM
  weak compare-exchange to a non-strong exclusive store.
- Recorded gap: the paper omits primitive fairness from its developed theory.
  Proper weak-LLVM-compare-exchange lowering entered Dartagnan after the
  paper's January 2026 publication. The current repository's Treiber
  benchmark uses strong CAS, and its C11/RC11 regression verdict is
  `UNKNOWN`, not a positive termination result. No target weak-CAS/Treiber
  theorem or integrated separation was found.

Please test:

1. Can the published lower-semicontinuity/fair-recurrence theory already encode
   primitive weak-CAS fairness without extending its definitions?
2. Does the implementation-level suffix constraint constitute a sound and
   complete weak-CAS fairness treatment, and what execution or bounded-lasso
   restrictions qualify it?
3. Is there a recurrence-set result whose negation directly yields the target
   positive system-response theorem with the same fairness quantifiers?
4. Does any Dartagnan branch or benchmark turn its strong-CAS Treiber
   `UNKNOWN` result into a weak-CAS C11/RC11 termination proof, or contain an
   all-spurious separation missed by the current screen?

### 4. Total-TaDA

- Paper: [da Rocha Pinto et al., *Modular Termination Verification for
  Non-blocking Concurrency*](https://vtss.doc.ic.ac.uk/publications/daRochaPinto2016Modular.techreport.pdf);
  [DOI 10.1007/978-3-662-49498-1_8](https://doi.org/10.1007/978-3-662-49498-1_8).
- Known overlap: Total-TaDA proves functional correctness and termination for
  Treiber operations and formalizes lock-/wait-freedom-style specifications.
- Recorded gap: the Treiber proof uses a classical interleaving heap and strong
  CAS, with failure indicating a head change; it has no weak-memory or
  spurious-failure separation.

Please test:

1. Does a published Total-TaDA rule or variant cover genuinely weak CAS under
   a separate primitive-justice assumption?
2. Do its ordinal interference assumptions subsume, or materially differ
   from, the target's scheduler/memory/primitive fairness conjunction?
3. Is its per-operation total-correctness result stronger than the target
   system-wide property on a semantics that actually includes all target
   executions?

### 5. Atig et al.: fair nontermination detection

- Paper: [Atig et al., *Detecting Fair Non-termination in Multithreaded
  Programs*](https://doi.org/10.1007/978-3-642-31424-7_19)
  ([author-hosted version](https://github.com/michael-emmi/research-papers/raw/master/conf-cav-AtigBEL12.pdf)).
- Audit identifiers: S52 / PA41; promoted citation candidate CG0263.
- Known overlap: the paper reduces detection of bounded-stem/bounded-lasso,
  strongly fair, ultimately periodic nontermination in atomic shared-memory
  programs to sequential assertion reachability. Lemma 5 supplies the
  reduction, and MUTANT finds an `OptimisticList` nontermination lasso.
- Recorded gap: this is detection of a negative execution, not a positive
  Treiber response-progress theorem. The model has no RC11 execution graph,
  genuinely weak CAS, separate primitive justice, integrated all-spurious
  Treiber execution, or proof-assistant certificate.

Please test:

1. Can the reduction express compare-equal weak-CAS failures as a fairness
   class distinct from process fairness without strengthening the target
   assumptions?
2. Does a later MUTANT/CORRAL development apply the method to Treiber under
   C11/RC11 and prove absence, rather than presence, of a fair lasso?
3. Can a bounded-stem/bounded-lasso detection result imply the target's
   unbounded positive response property?

### 6. Liang et al.: Treiber linearizability and lock-freedom together

- Paper: [Liang et al., *Compositional Verification of
  Termination-Preserving Refinement of Concurrent
  Programs*](https://doi.org/10.1145/2603088.2603123)
  ([extended technical report](https://flint.cs.yale.edu/flint/publications/rgsimt-tr.pdf)).
- Audit identifiers: S53 / PA42; promoted citation candidate CG0593.
- Known overlap: §4.3 and Figures 22--24 of the extended report directly prove
  Treiber linearizability and lock-freedom together via
  termination-preserving refinement. The progress argument requires a failed
  push/pop CAS to have been caused by another thread's successful update.
  This defeats any broad claim to the first compositional or combined Treiber
  safety-plus-progress proof.
- Recorded gap: the semantics is atomic interleaving and CAS is exact-match
  strong CAS. The work has no RC11 execution graph, compare-equal spurious
  failure, separate primitive justice, all-spurious separation, or
  machine-checked artifact. Its failure-implies-interference step is precisely
  what genuinely weak CAS invalidates.

Please test:

1. Is any mechanized or relaxed-memory version of the
   termination-preserving-refinement proof available?
2. Can its simulation argument be instantiated with genuinely weak CAS and a
   separate justice premise without replacing the failed-CAS progress step?
3. Does its conclusion quantify over recurring demand in a way stronger than
   the target once the execution spaces and CAS semantics are aligned?

### 7. Colvin and Groves: scalable lock-free stack verification

- Paper: [Colvin and Groves, *A Scalable Lock-Free Stack Algorithm and its
  Verification*](https://doi.org/10.1109/SEFM.2007.2).
- Audit identifiers: A32 / PA43; promoted citation candidate CG0456.
- Known overlap: the exact abstract reports PVS-checked verification of a
  finite-process scalable elimination stack under atomic interleaving. The
  accessible companion defines exact-match CAS and identifies the earlier
  I/O-automata/PVS result as preservation of linearizability. That verification
  lineage concerns safety, not progress.
- Access limitation: the exact SEFM full text was not available during this
  audit. Its theorem statement still needs line-level confirmation against the
  publisher copy, but accessible primary evidence does not establish a
  PVS-checked lock-freedom theorem.
- Recorded gap on accessible evidence: no RC11 semantics, compare-equal
  spurious CAS failure, memory/primitive-fairness separation, integrated
  all-spurious execution, or target finite-prefix safety composition is shown.

Please test:

1. Does the closed SEFM text contain any progress theorem beyond the
   PVS-checked linearizability result described by the accessible primary
   lineage?
2. Is the elimination choice assumption scheduler fairness, an algorithmic
   oracle, or a primitive-progress premise, and how is it quantified?
3. Does the checked model admit any compare-equal CAS failure or relaxed-memory
   execution?

### 8. Doherty's nonblocking-data-structure thesis (partly PVS-checked)

- Thesis: [Doherty, *The Design and Verification of Dynamic-sized Nonblocking
  Data Structures*](https://doi.org/10.26686/wgtn.16969549.v1)
  ([institutional PDF](https://ndownloader.figshare.com/files/31390636)).
- Audit identifiers: S54 / PA44; promoted citation candidate CG0910.
- Known overlap: Chapters 3, 4, and 6 give PVS-checked
  nonblocking-data-structure verifications. Chapter 5 separately presents a
  lock-freedom-preserving reference-counting transformation applied to Treiber
  under atomic exact-CAS semantics; the thesis does not identify the Chapter 5
  transformation as PVS-checked.
- Recorded gap: §7.2.2 explicitly says relaxed consistency is not treated and
  assumes atomic shared-memory operations. The result therefore has no RC11
  carrier, genuinely weak CAS, separate primitive justice, or integrated
  all-spurious execution.

Please test:

1. Which Chapter 5 safety and liveness obligations are PVS-checked, and do they
   yield one combined theorem for the transformed Treiber stack?
2. Does the transformation preserve progress if exact-match CAS is replaced by
   genuinely weak CAS under a justice assumption?
3. Is there a later relaxed-memory or weak-CAS continuation of this PVS
   development?

### 9. Classical machine-checked Treiber progress lineage

- 2007: [Colvin and Dongol, *Verifying Lock-Freedom Using Well-Founded
  Orders*](https://doi.org/10.1007/978-3-540-75292-9_9)
  ([UQ record](https://espace.library.uq.edu.au/view/UQ:136195)) reports a
  direct PVS-checked basic Treiber lock-freedom proof. Its conclusion is
  system-wide/existential rather than per-process. The full paper was
  access-controlled during this audit, so the exact theorem text and
  instantiation details still require checking against a publisher copy; the
  primary-author thesis and official abstract corroborate the result.
- 2007: [Parkinson, Bornat, and O'Hearn, *Modular Verification of a
  Non-Blocking Stack*](https://doi.org/10.1145/1190216.1190261) gives a
  manual separation-logic safety proof for a fixed-thread hazard-pointer
  stack and free list. It explicitly does not establish linearizability or
  lock-freedom.
- 2008: [Derrick, Schellhorn, and Wehrheim, *Mechanizing a Correctness Proof
  for a Lock-Free Concurrent
  Stack*](https://doi.org/10.1007/978-3-540-68863-1_6) KIV-mechanizes a
  Herlihy--Wing linearizability proof for a simplified Treiber stack and an
  arbitrary number of processes. Despite the title, it contains no
  lock-freedom or termination theorem.
- 2009: [Colvin and Dongol, *A General Technique for Proving
  Lock-Freedom*](https://doi.org/10.1016/j.scico.2008.09.013) supersedes the
  2007 method, but its published PVS cases are queues. Its
  [source bundle](https://brijeshdongol.github.io/mechanisation/SCP-2009-PVS.zip)
  does **not** establish a second completed Treiber artifact: the legacy
  `treiber.pvs` has no matching proof file and leaves two obligations marked
  “Will not prove.”
- 2009: [Petrank, Musuvathi, and Steensgaard, *Progress Guarantee for
  Parallel Programs via Bounded
  Lock-Freedom*](https://doi.org/10.1145/1542476.1542493) formally defines
  ordinary and bounded lock-freedom, CHESS-checks 2–6 one-shot harnesses for
  the Herlihy--Shavit `LockFreeStack` (a standard Treiber-style strong-CAS
  stack) under explicit SC, and manually proves a generic program/service
  progress-composition theorem. CHESS does not symbolically prove the
  inferred all-\(n\) bound. Its weak-LL/SC discussion separately observes
  that spurious failure can destroy lock-freedom even when threads receive
  CPU steps.
- 2011: [Tofan et al., *Formal Verification of a Lock-Free Stack with Hazard
  Pointers*](https://doi.org/10.1007/978-3-642-23283-1_16)
  ([KIV project](https://kiv.isse.de/projects/lock-free.html)) mechanizes
  memory safety, ABA prevention, linearizability, and system lock-freedom for
  a Treiber stack with hazard-pointer reclamation.
- 2013: [Hoffmann, Marmar, and Shao, *Quantitative Reasoning for Proving
  Lock-Freedom*](https://doi.org/10.1109/LICS.2013.18) manually proves
  system-wide strong-CAS Treiber lock-freedom for arbitrary fixed finite
  thread/client instances using consumable interference tokens, with an
  \(nM\) aggregate retry bound and companion memory-safety reasoning.
- 2013: [Tofan et al., *Compositional Verification of a Lock-Free Stack with
  RGITL*](https://doi.org/10.14279/tuj.eceasst.66.885)
  ([KIV project](https://kiv.isse.de/projects/avocs13.html)) mechanizes the
  same broad safety/progress combination for a Treiber-derived data stack plus
  a lock-free allocator/free stack.
- 2015: [Jia, Li, and Vafeiadis, *Proving Lock-Freedom Easily and
  Automatically*](https://doi.org/10.1145/2676724.2693179)
  ([CAVE artifacts](https://people.mpi-sws.org/~viktor/cave/lockfree/))
  automatically verifies system-wide lock-freedom for a public strong-CAS
  Treiber input. Coq checks the generic instrumentation metatheory; CAVE does
  not emit an end-to-end kernel-checked Treiber certificate.
- 2021: [Pani, Weissenbacher, and Zuleger, *Rely-guarantee bound analysis of
  parameterized concurrent shared-memory
  programs*](https://doi.org/10.1007/s10703-021-00370-8) uses Coachman to
  infer per-thread and total transition bounds for a symbolic-\(N\),
  one-operation-per-thread Treiber client under SC, exact-match CAS, and
  garbage collection. The theorem is a parameterized finite-batch resource
  bound, not a repeated-client response or linearizability theorem.
- Recorded gap: these are SC-style interleaving developments with exact-match
  strong CAS. None supplies an RC11 execution graph, compare-equal spurious
  failure, separated scheduler/memory/primitive fairness, or the target
  all-spurious execution.

Please test:

1. Against the 2007 full text, is the reported PVS theorem exactly the same
   global response quantifier as the target, and what enabledness or execution
   assumptions qualify it?
2. Do the 2011 or 2013 KIV temporal models impose scheduler conditions that
   make their system lock-freedom conclusions weaker or stronger than the
   target response theorem?
3. Is there a later PVS/KIV development transporting any of these proofs to
   C11/RC11 or genuinely weak CAS?
4. Does a generic theorem in this lineage make the target conjunction an
   immediate instance once primitive justice is supplied?
5. Can the Petrank program/service theorem or the Pani finite-batch bounds be
   lifted to recurring demand without assuming the target response property?
6. Does any checked development connect Petrank et al.'s spurious-LL/SC
   warning to its stack model, rather than treating it as a separate
   implementation caveat?
7. Does the Hoffmann token-compensation rule or the CAVE instrumentation
   remain sound if equality permits a spurious failure under a separate
   primitive-justice assumption, or is a materially new proof required?
8. Is there an unpublished certificate path that turns CAVE's concrete
   Treiber verdict into an end-to-end Coq-checked theorem and composes it with
   the tool's separate linearizability mode?

### 10. Lawyer

- Paper: [Namakonov et al., *Lawyer*](https://iris-project.org/pdfs/2026-oopsla-lawyer.pdf);
  [DOI 10.1145/3798240](https://doi.org/10.1145/3798240).
- Artifact: [Zenodo 18457698](https://doi.org/10.5281/zenodo.18457698).
- Known overlap: Lawyer gives a Rocq/Iris/Trillium liveness logic, weak
  scheduler-fairness infrastructure, a two-thread strong-CAS retrying counter,
  and machine-checked closed-program termination.
- Recorded gap: its HeapLang compare-exchange succeeds exactly on equality;
  the final result list has no stack theorem, and the source scan finds no
  Treiber, weak-CAS, or spurious-failure definition.

Please test:

1. Is there a Lawyer development, follow-up, or unpublished case study for
   Treiber or genuinely weak CAS?
2. Does Lawyer's general adequacy theorem make the target result an immediate
   checked instance, or would a new RC11 semantics, primitive-fairness model,
   and Treiber proof be required?
3. Is the counter's termination-under-any-scheduler theorem comparable to the
   target system-wide response theorem once primitive and memory semantics are
   aligned?

### 11. Mechanized relaxed-memory Treiber safety

- Papers and artifacts:
  [Kaiser et al., *The Compass*](https://doi.org/10.1145/3519939.3523451)
  ([artifact](https://doi.org/10.5281/zenodo.6323656));
  [Park et al., *A Proof Recipe for Linearizability in Relaxed Memory
  Separation Logic*](https://doi.org/10.1145/3656384)
  ([artifact](https://doi.org/10.5281/zenodo.10933398)); and
  [Dalvandi and Dongol, *Verifying C11-Style Weak Memory Libraries via
  Refinement*](https://doi.org/10.1145/3437801.3441619). The same boundary
  also includes [Park et al., *Verifying Lock-Free Traversals in Relaxed
  Memory Separation
  Logic*](https://doi.org/10.1145/3729248), whose Rocq/iRC11 development
  verifies Harris-style lists, a skiplist, and a skiplist priority queue.
- Known overlap: these works already mechanize Treiber safety, refinement, or
  linearizability in RC11-family relaxed-memory settings. Their checked CAS
  rules fail on mismatch rather than on an equal-value spurious branch.
- Recorded gap: they prove partial correctness/safety, not a weak-CAS liveness
  theorem; they contain no scheduler/memory/primitive-fairness separation or
  all-spurious progress counterexecution. The Compass and Proof Recipe use
  ORC11/iRC11 variants, while the Isabelle development uses an RC11-RAR
  fragment. The traversal work has no Treiber client and uses mismatch-only
  strong CAS; its “lock-free” and “wait-free” labels are not proved progress
  theorems.

Please test:

1. Does any extended version or artifact contain an unadvertised Treiber
   progress theorem or weak-CAS rule?
2. Does one of these execution models formally contain every target finite
   RC11 prefix, or is the target's safety result a reusable package rather than
   a new relaxed-memory safety theorem?
3. Is there a generic safety/liveness composition theorem in these
   developments that the target should instantiate or cite explicitly?
4. Which of the three gives the strongest directly comparable linearizability
   statement?
5. Does the traversal development contain an unadvertised liveness theorem,
   or are all of its logically atomic specifications partial-correctness
   safety statements?

### 12. RoboCop

- Paper: [Nagar et al., *Automated Robustness Verification of Concurrent Data
  Structure Libraries against Relaxed Memory
  Models*](https://doi.org/10.1145/3689802)
  ([extended author version](https://kartiknagar.github.io/publication/oopsla24/oopsla24.pdf);
  [artifact](https://doi.org/10.5281/zenodo.13626195)).
- Audit identifiers: S55 / PA45; promoted citation candidate CG0815.
- Known overlap: RoboCop proves RC20 execution-graph robustness, including
  unbounded-library-client composition results, and evaluates Treiber.
  Appendix A's `casFalse` rule requires a value mismatch, and the archived
  Treiber benchmark calls `atomic_compare_exchange_strong_explicit`. Its §5.4
  CAS-loop transformation removes independent failed read-only iterations and
  replaces the final CAS with blocking CAS; Lemma 5.4 preserves robustness for
  that transformation.
- Recorded gap: robustness is a safety property. Removing failed iterations
  deliberately discards the retry behavior that is decisive for genuinely
  weak-CAS liveness. RoboCop proves no operation-response theorem, primitive
  justice condition, or integrated all-spurious separation.

Please test:

1. Do Theorems 4.4, 4.6, 6.1, or 6.2 imply any liveness property beyond RC20
   robustness?
2. Is the §5.4 transformation sound for a source language in which CAS may
   fail spuriously on equal values, and if so only for safety?
3. Does any benchmark, extension, or artifact retain failed Treiber iterations
   and analyze fair unbounded progress?

### 13. RCU-protected Treiber under iRC11

- Paper: [Jung et al., *Verifying General-Purpose RCU for Reclamation in
  Relaxed Memory Separation Logic*](https://doi.org/10.1145/3729246)
  ([author version](https://iris-project.org/pdfs/2025-pldi-weak-smr.pdf);
  [artifact](https://doi.org/10.5281/zenodo.15167032)).
- Audit identifiers: S56 / PA46; promoted citation candidate CG0825.
- Known overlap: the paper uses Algorithm 1's RCU-protected Treiber stack as an
  illustrative iRC11 safety argument and explicitly accounts for stale head
  messages. The archived Rocq development machine-checks general-purpose RCU,
  Peterson mutex, Michael--Scott queue, and Harris-list clients; its README
  and file inventory identify no Treiber/stack development.
- Recorded gap: the CAS is ordinary exact-match CAS, and the theorem concerns
  safe reclamation and functional correctness rather than termination.
  Moreover, the available artifact does not machine-check the paper's Treiber
  illustration. It has no weak-CAS justice, unbounded response theorem, or
  all-spurious fairness-independence execution; the illustrative stack is also
  RCU-protected rather than reclamation-free.

Please test:

1. Is there a separate Rocq Treiber development omitted from Zenodo 15167032,
   or should the paper's Treiber discussion be treated only as an illustrative
   pen-and-paper proof argument?
2. Could its Treiber safety package be reused for genuinely weak CAS without
   changing its operational CAS rules or logical specifications?
3. Does iRC11's stale-message reasoning impose a liveness or memory-fairness
   premise comparable to the target's prefix-finite from-read condition?

Taken together, S52--S56 and A32 materially narrow the historical wording but
do not subsume the candidate. Atig et al. supply fair negative-execution
detection; Liang et al. supply combined classical Treiber safety and liveness;
Colvin--Groves and Doherty supply classical verification lineage; RoboCop
supplies RC20 safety/robustness; and Jung et al. supply a paper-level iRC11
Treiber-with-RCU safety argument adjacent to mechanized RCU and queue/list
clients. None supplies in one result all six target parts: reclamation-free
RC11 Treiber, genuinely weak CAS, primitive justice separate from scheduler
and memory fairness, an integrated all-spurious separation, unbounded
system-wide response progress, and machine-checked finite-prefix
linearizability composition.

### 14. Spirea

- Paper: [Vindum and Birkedal, *Spirea*](https://cs.au.dk/~birke/papers/spirea-2023.pdf);
  [DOI 10.1145/3622820](https://doi.org/10.1145/3622820).
- Artifact: [Zenodo 8314888](https://doi.org/10.5281/zenodo.8314888).
- Known overlap: Spirea Coq-mechanizes a durable Treiber implementation under
  an operational release/acquire weak-persistent-memory semantics and proves
  modular thread safety, crash safety, and null recovery.
- Follow-up overlap: the unprotected `high-nextgen-logic` branch at
  [`925a8d7a`](https://github.com/logsem/spirea/tree/925a8d7a7c69c0c83163fe78d0d93f668e0558ca)
  substantially extends the durable Treiber history/specification proof and
  includes it in the branch build list. No pull request or CI result records
  review of that branch.
- Recorded gap: its compare-exchange failure rule requires inequality. Section
  6.3.2 explicitly says that the verified specification does not imply
  linearizability or LIFO. The follow-up branch retains the same
  mismatch-only CAS and ordinary partial-correctness loop proofs; no liveness
  or progress-fairness theorem was found. The paper also leaves formal
  correspondence with the original declarative explicit-epoch model to future
  work.

Please test:

1. Does the `high-nextgen-logic` history/specification upgrade imply a
   linearizability or progress property not made explicit in its source?
2. Does Spirea's operational weak-memory component include behavior that makes
   it a direct semantic predecessor of the target RC11 carrier?
3. Is any compare-equal failure possible below the language head-step rules,
   despite the explicit inequality premise on `CmpXchgFailS`?
4. Does its safety adequacy theorem add a composition obligation that the
   target finite-prefix package has missed?

### 15. Memento

- Paper: [Cho et al., *Memento*](https://www.soundandcomplete.org/papers/PLDI2023/memento.pdf);
  [DOI 10.1145/3591232](https://doi.org/10.1145/3591232).
- Artifact: [Zenodo 7811928](https://doi.org/10.5281/zenodo.7811928).
- Known overlap: Memento formalizes detectable recoverability and erasure
  refinement and implements a detectable persistent Treiber stack using a
  helping compare-and-swap construction.
- Recorded gap: the implementation is built from exact-match CAS and x86
  persistency operations. The core theorems concern detectability and erasure;
  no machine-checked RC11 weak-CAS Treiber response-progress or
  fairness-separation theorem was found.

Please test:

1. Does Memento's erased-program refinement inherit a formally established
   Treiber linearizability or progress theorem not stated in the paper?
2. Is its helping CAS progress guarantee strong enough to subsume primitive
   justice on an execution model containing all target behaviors?
3. Is there a mechanized artifact theorem, rather than an implementation and
   empirical case study, for the persistent Treiber instance?

### 16. Relinche

- Paper: [Golovin et al., *Relinche: Automatically Checking Linearizability
  under Relaxed Memory Consistency*](https://doi.org/10.1145/3704906).
- Artifact: [Zenodo 13992580](https://doi.org/10.5281/zenodo.13992580).
- Known overlap: Relinche uses GenMC to check contextual refinement of C/C++
  Treiber variants under RC11. Its soundness result ranges over every client
  respecting a fixed bound on method invocations.
- Recorded gap: this is finite, bounded safety/refinement checking. It has no
  infinite carrier, unbounded response theorem, scheduler or memory fairness,
  weak-CAS justice, or all-spurious separation.

Please test:

1. Does Theorem 4.3 or an artifact configuration justify any unbounded
   linearizability or liveness conclusion beyond the fixed invocation bound?
2. Do the evaluated Treiber variants genuinely admit compare-equal spurious
   CAS failure, and if so is it explored rather than assumed away?
3. Is any progress result hidden in the checker, benchmarks, or later branch?

### 17. Will It Fit?

- Paper: [Moine et al., *Will It Fit? Verifying Heap Space Bounds of
  Concurrent Programs under Garbage Collection*](https://doi.org/10.1145/3716312).
- Artifact: [IrisFit](https://github.com/nobrakal/irisfit).
- Known overlap: one Coq/Iris development combines functional and heap-space
  specifications for a Treiber stack with bounded-time liveness theorems for
  garbage-collection polling and allocation enablement.
- Recorded gap: LambdaFit is SC-style and its CAS failure rule requires
  inequality. The liveness conclusion concerns allocation requests and
  enabled threads, not push/pop response or system lock-freedom.

Please test:

1. Can Theorems 8.2--8.3 be composed with the Treiber specifications to imply
   any operation-response property, or do they end at allocation enablement?
2. Does the development contain a scheduler/progress assumption or retry-loop
   theorem not visible in the paper's Treiber case study?
3. Is there a weak-memory or genuinely weak-CAS variant?

### 18. Miri--GenMC

- Thesis: [Muntwiler, *Marrying Miri and GenMC: Improving Miri's Ability to
  Detect Concurrency Bugs*](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/MasterTheses/2025-Patrick-Thesis.pdf).
- Cutoff-pinned source:
  [GenMC v0.17.0](https://github.com/MPI-SWS/genmc/tree/29b03a66402c4453fc77901ef3be90bb55707cd4).
- Known overlap: the thesis evaluates a reclamation-free Treiber benchmark
  with GenMC under RC11 and explicitly studies weak compare-exchange.
- Recorded gap: the benchmark calls strong Rust `compare_exchange`; the thesis
  states that GenMC omits compare-equal spurious failures and demonstrates a
  weak-CAS bug the integration can miss. The Treiber run is bounded
  safety/performance exploration, not a liveness theorem.

Please test:

1. Does any current or historical GenMC mode soundly explore genuine
   weak-CAS spurious behavior in the Treiber benchmark?
2. Do the benchmark transformations, including collapsed spin loops, exclude
   the infinite behaviors material to the target?
3. Is there a separate GenMC theorem or artifact result for fair unbounded
   weak-CAS Treiber progress?

### 19. Mirror is Not Strong

- Paper: [Schellhorn et al., *Mirror is Not Strong: Discovery of a Persistent
  Memory Bug using Refinement in KIV*](https://doi.org/10.1007/978-3-031-92196-4_16).
- Mechanization: [KIV MIRROR project](https://kiv.isse.de/projects/MIRROR.html).
- Known overlap: KIV reveals that Mirror implements durable
  `compare_exchange_weak`, whose failure may occur even when the values match,
  rather than the advertised strong operation.
- Recorded gap: the completed mechanization covers the lower
  Mirror-to-IMirror refinement. The upper IMirror-to-PLib refinement is
  explicitly unfinished, so the conditional end-to-end durability argument
  must not be presented as fully mechanized. There is no Treiber client,
  RC11 fairness model, primitive justice, or operation-progress theorem.

Please test:

1. Does any completed KIV obligation establish an end-to-end property beyond
   the lower refinement, or has the upper refinement since been finished?
2. Is Mirror's durable weak-CAS behavior governed by any fairness or
   non-spurious-progress condition?
3. Can its conditional generic transformation theorem subsume the target
   Treiber result without a new liveness proof?

### 20. Parcas

- Paper: [Moine et al., *Parcas*](https://doi.org/10.1145/3828679).
- Artifact: [public Rocq/Iris development](https://github.com/nobrakal/parcas).
- Known overlap: Parcas mechanizes Treiber linearizability together with
  worst-case work/span and retry-cost bounds for fixed participant and
  operation budgets.
- Recorded gap: its language is SC-style and CAS failure requires inequality.
  Its bounds assume a finite workload; the paper explicitly says they are not
  a formal lock-freedom proof. It has no unbounded recurring demand, RC11, or
  separated primitive justice.

Please test:

1. Can the finite credit bounds imply the target's unbounded response theorem
   under recurring demand without introducing an additional compactness or
   fairness argument?
2. Does any artifact theorem state lock-freedom despite the paper's explicit
   qualification?
3. Is a weak-CAS or relaxed-memory port available?

### 21. Zoo

- Paper: [Allain and Scherer, *Zoo: A Framework for the Verification of
  Concurrent OCaml 5 Programs using Separation
  Logic*](https://doi.org/10.1145/3776701).
- Known overlap: Zoo's public Rocq/Iris development verifies functional
  specifications for three Treiber variants.
- Recorded gap: ZooLang is sequentially consistent, CAS is a physical-equality
  compare-and-set rather than genuinely weak CAS, and no stack-progress
  theorem is claimed. Relaxed memory is identified as future work.

Please test:

1. Does any of the three Treiber variants carry an unadvertised termination,
   lock-freedom, or fairness theorem?
2. Does a development branch add relaxed-memory or spurious-CAS behavior?
3. Is Zoo's safety interface directly reusable for the target finite-prefix
   composition in a way that changes the claim wording?

### 22. Friggens's bounded and unbounded Treiber analyses

- Thesis: [Friggens, *On the Use of Model Checking for the Bounded and
  Unbounded Verification of Nonblocking Concurrent Data
  Structures*](https://doi.org/10.26686/wgtn.17004076).
- Known overlap: the thesis expresses Treiber wait-/lock-freedom in LTL,
  explicitly distinguishes weak-fair scheduling formulations, and uses Spin
  to find non-wait-freedom and verify lock-freedom on fixed small instances.
  Its separate TVLA/3VMC analysis establishes unbounded Treiber
  linearizability/safety.
- Recorded gap: the progress experiments remain bounded; the thesis expressly
  does not lift them through finite-execution canonical abstraction. The
  model is SC with mismatch-only strong CAS and has no weak-memory visibility
  fairness, primitive justice, all-spurious trace, or proof-assistant theorem.

Please test:

1. Does any thesis appendix, model file, follow-up, or soft-invariant result
   turn the bounded Spin lock-freedom checks into an arbitrary-thread theorem?
2. Is there a justified composition between the TVLA/3VMC safety proof and the
   Spin progress result that the audit has missed?
3. Does any model variant admit compare-equal CAS failure or another primitive
   nondeterminism requiring justice?

### 23. Final TSO liveness-decidability result

- Article: [Wang et al., *Decidability of Liveness on the TSO Memory
  Model*](https://doi.org/10.1145/3766061), Formal Aspects of Computing
  38(1), 2026.
- Known overlap: the work formalizes concurrent-object liveness under TSO for
  a bounded process population and distinguishes scheduler conditions. The
  final abstract adds fixed-\(k\) bounded-wait-freedom decidability,
  non-primitive-recursive complexity, and a TSO object that is wait-free but
  not \(k\)-bounded wait-free for any \(k\).
- Recorded gap: the generic libraries use atomic exact-match CAS and unbounded
  store buffers, not RC11 Treiber or genuinely weak CAS. There is no primitive
  justice, all-spurious separation, or mechanized algorithm theorem. The
  audit had full access to the preliminary model but not yet to every theorem
  page of the final publisher version.

Please test:

1. Do the final theorems or separation object contain any Treiber instance,
   spurious-failure semantics, or primitive-progress premise omitted from the
   abstract and preliminary version?
2. Does the TSO scheduler/flush treatment subsume the target's independent
   thread, memory, and primitive fairness assumptions?
3. Is the final wait-free-versus-\(k\)-bounded separation relevant to the
   target system-wide response quantifier in a way that requires narrower
   wording?

### 24. Dynamic Robustness Verification against Weak Memory (RSan)

- Paper: [Margalit et al., *Dynamic Robustness Verification against Weak
  Memory*](https://doi.org/10.1145/3729277)
  ([author PDF](https://people.inf.ethz.ch/mkokologiann/papers/pldi2025-rsan.pdf)).
- Artifact: exact audited version [Zenodo record 15002568, version
  1](https://doi.org/10.5281/zenodo.15002568); concept record
  [15002567](https://doi.org/10.5281/zenodo.15002567).
- Audit identifiers: S59 / PA47; promoted citation candidate CG0201.
- Known overlap: Theorem 3.1 characterizes RC20 robustness through the
  location-clock instrumentation. Section 4.1, footnote 3 says that weak CAS
  may fail after reading the expected value and that the development and tool
  support both weak and strong CAS.
- Recorded gap in the audited paper and metadata: this is dynamic
  safety/robustness verification, not a Treiber progress theorem. Section 4.3
  treats weak-memory busy-wait and CAS-loop failures as benign robustness
  violations and uses blocking `BCAS` annotations whose graphs omit failed
  attempts. Neither a scheduler/memory/primitive fairness factorization,
  primitive justice, an integrated all-spurious progress witness, nor a
  proof-assistant certificate is stated there. The Zenodo payload is a
  12,331,288,562-byte compressed Docker image and was metadata-audited but not
  downloaded into the local eleven-bundle corpus; no source-level absence claim
  is made about that image.

Please test:

1. Does the implementation's weak-CAS support impose any progress condition
   not stated in the paper, or can it represent unbounded compare-equal
   failures?
2. Can the `BCAS` abstraction soundly support any liveness conclusion, or does
   omitting failed attempts necessarily limit it to robustness/safety?
3. Does any RSan benchmark, extended appendix, or successor contain a Treiber
   liveness theorem or an explicit scheduler/primitive fairness separation?

### 25. CQS: fair and abortable synchronization

- Paper: [Koval et al., *CQS: A Formally-Verified Framework for Fair and
  Abortable Synchronization*](https://arxiv.org/pdf/2111.12682)
  ([DOI 10.1145/3591230](https://doi.org/10.1145/3591230)).
- Artifact: [pinned public proof snapshot, commit
  `970ef8c`](https://github.com/Kotlin/kotlinx.coroutines/tree/970ef8c280dd8b934b3e89f78266e9b68b1a1290).
- Audit identifiers: S67 / PA48.
- Known overlap: CQS gives paper-level fairness and progress arguments for a
  fair, abortable synchronizer; Appendix F.4 uses a modified classical
  Treiber stack as outer storage. The checked HeapLang/Iris development is
  sequentially consistent and uses equality-guarded exact CAS.
- Recorded gap: the audited 33-file Coq snapshot checks safety/functional
  specifications but contains no liveness or fairness definition and omits
  the paper-referenced blocking-pool and outer-stack files. Neither the paper
  nor that snapshot supplies RC11, genuine weak-CAS spuriosity, primitive
  justice, an all-spurious execution, or a machine-checked Treiber response
  theorem.

Please test:

1. Is there a fuller author artifact or commit containing Appendix F.4's
   outer stack and the omitted blocking-pool proofs?
2. Does any CQS theorem mechanize execution fairness or progress, rather than
   only safety and functional specifications?
3. Does any version model compare-equal spurious CAS failure or relaxed memory
   and constrain such failures with a primitive-progress premise?
4. Can the paper's client-fairness argument imply the target system-wide
   Treiber response theorem, or is it specific to CQS clients?

### 26. GenMC

- Paper: [Kokologiannakis and Vafeiadis, *GenMC: A Model Checker for Weak
  Memory Models*](https://people.inf.ethz.ch/mkokologiann/papers/cav2021-genmc.pdf)
  ([DOI
  10.1007/978-3-030-81685-8_20](https://doi.org/10.1007/978-3-030-81685-8_20)).
- Artifact: [pinned GenMC v0.6 source, commit
  `364e02a`](https://github.com/MPI-SWS/genmc/tree/364e02afa1dec0e5c9fbedca6a2306d0ed5f1abf).
- Audit identifiers: S70 / PA49.
- Known overlap: GenMC is an executable stateless model checker for
  C11/RC11-family weak-memory executions, and its regression suite includes a
  Treiber stack. Its public C interface exposes
  `atomic_compare_exchange_weak`.
- Recorded gap: at the pinned commit, the LLVM compare-exchange visitor
  ignores the `isWeak` flag and generates equality-guarded exact CAS; the
  bundled Treiber test calls strong compare-exchange. GenMC checks finite
  executions for safety/errors, not unbounded fair liveness. The audited
  source has no primitive justice, all-spurious witness, or proof-assistant
  Treiber theorem. The archived 3.18 GB VM image was not downloaded, so this
  source-level statement is limited to the pinned source tree.

Please test:

1. Does the archived v0.6 VM or another v0.6 execution path implement
   compare-equal spuriosity despite the audited LLVM visitor?
2. Does any bundled or unpublished Treiber configuration use genuine weak
   compare-exchange and explore spurious failure?
3. Does any GenMC mode or theorem establish unbounded fair response progress
   rather than finite-execution safety?
4. If a later GenMC version honors the weak flag, does it add a
   justice/fairness premise or merely permit nondeterministic finite spurious
   failures?

### 27. Gao and Hesselink's formal lock-free reduction

- Paper: [Gao and Hesselink, *A Formal Reduction for Lock-Free Parallel
  Algorithms*](https://pure.rug.nl/ws/files/2980544/2004LNCSGao.pdf)
  ([DOI
  10.1007/978-3-540-27813-9_4](https://doi.org/10.1007/978-3-540-27813-9_4)).
- Audit identifiers: S76 / PA50.
- Known overlap: this is a generic Herlihy-style LL/SC transformation with
  PVS-supported simulation and invariant proofs. Its classical lock-freedom
  argument assumes strong scheduler fairness and, separately, eventual access
  to a valid reservation/success for a process that retries forever. It is
  therefore important prior art for separating scheduler fairness from an
  additional primitive/platform-success premise.
- Recorded gap: LL/SC failure is tied to reservation
  invalidation/interference, not compare-equal weak-CAS spuriosity. The result
  has no Treiber instance, RC11 execution graph, prefix-finite memory
  fairness, named weak-CAS justice, all-spurious counterexecution, or
  target-style finite-prefix safety/liveness composition.

Please test:

1. Does the complete PVS development mechanize the liveness/refinement
   argument and its extra premise, or only invariants and simulation?
2. When instantiated with genuine weak CAS, is the
   eventual-valid-reservation premise logically equivalent to primitive
   justice, or does it cover only interference-driven LL/SC failure?
3. Is there a Treiber or weak-memory instantiation in an extended report,
   artifact, or follow-up?
4. Does Theorem 4 compose safety and liveness strongly enough to require
   narrower wording of the candidate's machine-checked composition claim?

### 28. VeriFast termination verification of a Treiber-style stack

- Paper: [Jacobs, Bošnački, and Kuiper, *Modular Termination Verification of
  Single-Threaded and Multithreaded
  Programs*](https://lirias.kuleuven.be/retrieve/411c54a9-cb2e-45d2-bd69-3a789d9cdec9)
  ([DOI 10.1145/3210258](https://doi.org/10.1145/3210258)).
- Artifact: [VeriFast 18.02 termination
  examples](https://github.com/verifast/verifast/tree/18.02/examples/java/termination).
- Audit identifiers: S78 / PA51.
- Known overlap: Section 4.4 tool-checks termination of finite client programs
  using a direct Treiber-style push loop; pop is stated analogous. Under SC
  and exact CAS, each failed retry witnesses another successful operation,
  allowing call permissions to transfer from successful to failed operations.
  A separate Coq companion mechanizes the generic termination metatheory.
- Recorded gap: compare-equal spurious failure breaks the
  interference-to-permission step. The audited result has no RC11 semantics,
  memory fairness, primitive justice, three-way fairness split, all-spurious
  execution, unbounded system-wide response theorem, or kernel-checked
  concurrent-stack theorem; the stack was not identified in the Coq
  companion.

Please test:

1. Does the artifact contain a verified pop or a system-wide lock-freedom
   theorem beyond the published finite-client judgment?
2. Is the concurrent stack present in the Coq companion, rather than only the
   generic levels metatheory?
3. Can the permission proof survive genuine weak CAS without explicit
   justice; if so, what rules out repeated compare-equal failure?
4. Is there a later weak-memory version or a composition with a
   machine-checked linearizability proof?

### 29. Gao's lock-free-algorithms thesis

- Thesis record: [Gao, *Design and Verification of Lock-Free Parallel
  Algorithms*](https://research.rug.nl/en/publications/design-and-verification-of-lock-free-parallel-algorithms/);
  [full thesis
  PDF](https://www.mi.fu-berlin.de/inf/groups/ag-tech/intern/19548-V-Model-Checking/Hui_Gao.pdf).
- Audit identifiers: S87 / PA52; promoted citation candidate CG0221.
- Known overlap: this is an expanded umbrella source for the Gao--Hesselink
  lineage, not an exact duplicate of PA50. Chapter 3 reproduces and expands
  the LL/SC reduction; Chapter 4 adds a generic exact-CAS refinement and
  handwritten lock-freedom proof under strong fairness plus an eventual
  matching-indirection/success premise.
- Recorded gap: Chapter 4's conclusion says the PVS development checks
  invariants and simulation while deferring the liveness proof, and the thesis
  summary says some liveness proofs remain informal. The model is SC with
  exact CAS and contains no Treiber instance, RC11, genuine weak CAS,
  primitive justice, all-spurious execution, or finite-prefix composition
  theorem.

Please test:

1. Are there unpublished or repository PVS liveness files that supersede the
   thesis's explicit deferral?
2. Does the matching-indirection premise also constrain compare-equal
   spurious CAS failure, or only interference-driven retries?
3. Does any thesis supplement or follow-up instantiate Chapter 4 to a
   reclamation-free Treiber stack and compose the PVS safety result with
   liveness?
4. Is there a weak-memory extension of this reduction that changes the
   recorded gap?

### 30. Promising-ARM/RISC-V

- Paper: [Pulte et al., *Promising-ARM/RISC-V: A Simpler and Faster
  Operational Concurrency
  Model*](https://www.cl.cam.ac.uk/~pes20/promising-arm-riscv.pdf);
  [DOI 10.1145/3314221.3314624](https://doi.org/10.1145/3314221.3314624).
- Supplement:
  [project page](https://sf.snu.ac.kr/promising-arm-riscv/) and
  [source archive](https://sf.snu.ac.kr/publications/promising-arm-riscv-supp.zip).
- Audit identifiers: S226 / PA118 / A11; promoted citation candidate CG0690.
- Known overlap: the Coq model's `write_failure` rule permits an exclusive
  store to return failure without a mismatch or interference premise, and the
  step relation exposes it directly. The supplement also contains finite C++
  and Rust Treiber exploration inputs.
- Recorded gap: the source-level Treiber examples use strong
  compare-exchange and are separate from the 25 project Coq modules. The
  checked results concern model equivalence, certification, promise
  computation, and RISC-V deadlock freedom. No primitive-justice condition,
  scheduler/memory/primitive fairness factorization, all-spurious separation
  theorem, unbounded Treiber response theorem, or mechanized Treiber
  safety-and-liveness composition was found.

Please test:

1. Is the unguarded `write_failure` constructor intended to model genuinely
   spurious store-exclusive failure even when no conflicting write occurs?
2. Does `certified_deadlock_free` imply any infinite-execution fairness or
   client-operation response property beyond reachability of a no-promises
   machine state?
3. Is there a Coq Treiber instantiation, safety proof, or liveness theorem in
   another branch or supplement that is not present in A11?
4. When the strong-CAS C++/Rust examples compile through load/store
   exclusives, what architectural or compiler-level progress premise, if any,
   rules out indefinitely repeated exclusive failure?

### 31. Trace-based derivation of a scalable lock-free stack

- Paper: [Groves and Colvin, *Trace-based derivation of a scalable lock-free
  stack
  algorithm*](https://link.springer.com/article/10.1007/s00165-008-0092-5);
  [DOI 10.1007/s00165-008-0092-5](https://doi.org/10.1007/s00165-008-0092-5).
- Audit identifiers: S227 / PA119; promoted citation candidate CG0553.
- Known overlap: the accessible 2007 precursor derives an SC exact-CAS
  Treiber/elimination stack, establishes linearisability by trace
  transformation, and manually argues system lock-freedom. The elimination
  extension requires fair internal choice so an operation cannot forever
  avoid the central stack.
- Recorded gap: the progress argument is informal and unmechanized, and the
  exact 2009 journal PDF remains subscription-restricted. The model has no
  RC11, genuine weak CAS, memory fairness, primitive justice, or all-spurious
  execution.

Please test:

1. Does the 2009 journal version strengthen the accessible precursor into a
   formal theorem or machine-checked proof?
2. Is its fair internal choice a scheduler premise, a primitive premise, or a
   distinct algorithmic fairness assumption?
3. Does another artifact mechanize the liveness argument, rather than only
   the separate PVS linearizability lineage?

### 32. Temporally Bounding TSO

- Paper: [Morrison and Afek, *Temporally Bounding TSO for Fence-Free
  Asymmetric
  Synchronization*](https://www.cs.tau.ac.il/~mad/publications/asplos2015-tbtso.pdf);
  [DOI 10.1145/2694344.2694374](https://doi.org/10.1145/2694344.2694374).
- Audit identifiers: S228 / PA120; promoted citation candidate CG1057.
- Known overlap: scheduling remains asynchronous while TBTSO requires every
  store enqueued at time \(t_0\) to reach memory by \(t_0+\Delta\). The paper
  uses that separate memory-service premise to obtain wait-free fence-free
  hazard-pointer reclamation and bounded/nonblocking biased-lock behavior.
- Recorded gap: the work is TSO with exact atomics and non-Treiber clients.
  It has no genuine weak CAS, primitive justice, all-spurious separation, or
  machine-checked safety/liveness composition. The hardware \(\Delta\) bound
  is estimated under explicit assumptions rather than proved for current
  processors.

Please test:

1. Is TBTSO's hard deadline a stronger form of the target memory-fairness
   premise, or is it incomparable because it uses real time?
2. Does any follow-up instantiate TBTSO on Treiber or mechanize its progress
   arguments?
3. Does the global fair memory-system lock hide a primitive-progress premise
   relevant to compare-exchange?

### 33. Progress of Concurrent Objects

- Tutorial: [Liang and Feng, *Progress of Concurrent
  Objects*](https://plax-lab.github.io/publications/fntpl20/fntpl20-progress.pdf);
  [DOI 10.1561/2500000041](https://doi.org/10.1561/2500000041).
- Audit identifiers: S229 / PA121; promoted citation candidate CG1441.
- Known overlap: this authoritative synthesis defines ordinary, strong, and
  weak scheduler fairness, characterizes six progress properties by
  contextual refinement, proves LiLi soundness, and reports exact-CAS Treiber
  and partial-pop applications.
- Recorded gap: the tutorial consolidates the authors' 2013--2018 papers and
  receives no independent historical priority. Its semantics are SC with
  mismatch-only CAS failure; no weak memory, primitive justice, all-spurious
  system-wide nonprogress execution, or proof-assistant artifact was found.

Please test:

1. Does any omitted appendix, implementation, or later paper mechanize the
   Treiber applications?
2. Is any fairness definition strong enough to rule out genuine
   compare-equal spurious failure without a separate primitive premise?
3. Which original source should receive priority for each Treiber theorem
   summarized by the tutorial?

### 34. Progress of Concurrent Objects with Partial Methods

- Paper: [Liang and Feng, *Progress of Concurrent Objects with Partial
  Methods*](https://hongjin-liang.github.io/papers/popl18-partial.pdf);
  [DOI 10.1145/3158108](https://doi.org/10.1145/3158108).
- Extended report:
  [author PDF](https://hongjin-liang.github.io/papers/popl18-partial-tr.pdf).
- Audit identifiers: S230 / PA122; promoted citation candidate CG1155.
- Known overlap: generalized LiLi establishes linearizability plus partial
  progress. Extended-report Appendix C.3 applies it to an exact-CAS Treiber
  stack with possibly blocking pop and obtains partial deadlock-freedom under
  weak, and therefore strong, scheduler fairness.
- Recorded gap: the Treiber proof does not establish partial
  starvation-freedom; that generic LiLi conclusion needs additional level-0
  rely/guarantee premises. The result is handwritten and SC, with no genuine
  weak CAS, memory fairness, primitive justice, all-spurious execution, or
  mechanized artifact.

Please test:

1. Is there a stronger unpublished or mechanized Treiber proof satisfying the
   level-0 premises for partial starvation-freedom?
2. Can the partial-pop proof accommodate compare-equal weak-CAS failure
   without an additional justice premise?
3. Does its abstraction theorem imply any target-style system-wide response
   result under an RC11 refinement?

## Focused falsification questions

Please prioritize any question within your expertise:

1. **Exact prior theorem:** Do you know an earlier theorem whose execution
   space contains every target execution and whose assumptions are no stronger,
   while yielding the same or a stronger conclusion?
2. **Hidden mechanization:** Is there an artifact theorem not advertised in a
   title or abstract that connects weak CAS, Treiber, and weak memory?
3. **Implicit primitive progress:** Does weak thread fairness,
   prefix-finite from-read, RC11 validity, the source/control contract, or any
   other premise already entail weak-CAS justice?
4. **Justice fidelity:** Is the target justice definition too strong, too weak,
   wrongly indexed, or unlike the progress condition used for real weak
   compare-exchange?
5. **Independence witness:** Is the all-spurious execution genuinely in the
   same carrier and subject to the same source and RC11-prefix contracts as the
   positive theorem?
6. **Infinite coherence:** Is requiring every raw finite prefix to be RC11
   valid sufficient for the claimed coherent infinite-execution
   interpretation, or is a missing projective/global condition material?
7. **Memory fairness:** Is prefix-finite from-read used consistently with the
   RC11 memory-fairness literature? Does the proof need modification-order
   prefix-finiteness even though the exact theorem consumes only from-read?
8. **Progress classification:** Does “from every active state, some later
   response” match standard system-wide lock-freedom for this finite-thread
   model? Does the recurring-demand corollary justify “responses arbitrarily
   late” without implying per-operation completion?
9. **Safety composition:** Is finite-prefix Herlihy--Wing linearizability the
   correct safety statement to compose here, and are we avoiding any
   unjustified claim of one infinite coherent linearization?
10. **Model boundary:** Do the reclamation-free, no-address-reuse, hand-defined
    source semantics or absence of a verified full-ISO-C refinement require
    further qualification?
11. **Missing closest work:** Which paper, thesis, repository, branch, or
    extended version should be mandatory in the comparison set?
12. **Claim wording:** Even if the full conjunction is unmatched, which word
    in the candidate sentence is most likely to be read more broadly than the
    checked result permits?

## Important boundaries

The result does not claim:

- the first Treiber safety, progress, termination, or mechanized liveness
  proof, or the first result proving Treiber linearizability and lock-freedom
  together;
- the first weak-memory fairness or liveness framework;
- the first formal weak-CAS fairness mechanism or observation that weak CAS
  needs a progress condition;
- the first exact-CAS Treiber/partial-pop proof combining linearizability with
  scheduler-sensitive partial progress;
- the first memory-service progress assumption, distinct from scheduler
  fairness, used to derive bounded or wait-free algorithmic progress;
- a full ISO C theorem, verified compiler refinement, or unconditional
  hardware progress guarantee;
- wait-freedom, per-operation starvation-freedom, or per-thread completion;
- memory reclamation, address reuse, or ABA safety;
- minimality of primitive justice or of paired memory fairness;
- a site-indexed multi-location progress rule; or
- one projectively coherent linearization order for the whole infinite
  history.

## Review materials

- [Claim card](claim-card.md)
- [Prior-art matrix](prior-art-matrix.csv)
- [Prior-art analysis](prior-art-analysis.md)
- [Search report and coverage limits](search-report.md)
- [Closing citation decision overlay](citation-screening-decisions-20260731T101000Z.csv)
- [Reproducible artifact audit](artifact-audit.md)
- [Search protocol](protocol.md)
- [External-review response ledger](expert-review-ledger.csv)
- [Public Lean entry point](../../WeakMemory/WeakCASTreiberResult.lean)
- [Publication boundary](../publication-boundary.md)
- [Clean-clone verification report](../verification-report-2026-07-31.md)

When this packet is sent, it should be accompanied by the exact immutable
repository commit used for review. Please record that commit in the response
so later changes cannot be confused with the reviewed snapshot.

## Minimal useful response

A short response is sufficient if it contains:

1. one of the four verdicts above;
2. the closest work considered;
3. the exact technical reason it does or does not subsume the conjunction;
4. any model-fidelity objection; and
5. a source location for every claim-defeating observation.

Please also indicate whether the response may be:

- quoted with attribution;
- summarized with attribution;
- summarized anonymously; or
- used only to guide a private revision.

No response will be presented as agreement by silence.
