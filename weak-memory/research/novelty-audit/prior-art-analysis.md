# Prior-Art Analysis

## Current conclusion

The exact conjunction in `claim-card.md` has survived the reproducible,
date-bounded audit performed so far. The current corpus contains 230 sources,
240 canonical screening decisions, 110 closest-source records, and 122
theorem-level prior-art rows; every matrix row records
`subsumes_candidate=no`. Ten overlapping, checksum-bound decision overlays
contain 4,267 decisions, including completed exhaustive queues of 1,167, 313,
1,978, and 179 candidates. The closing 179-candidate expansion produced no
new closest source. No inspected work proves all of:

1. RC11-valid finite execution prefixes for an explicit reclamation-free
   Treiber model;
2. genuinely weak compare-and-exchange with equal-value spurious failure;
3. primitive weak-CAS justice kept distinct from thread and memory fairness;
4. an integrated all-spurious Treiber execution showing that thread and memory
   fairness do not imply progress;
5. unbounded system-wide response progress; and
6. machine-checked composition with finite-prefix linearizability.

This is not a priority certificate and remains an N0–N1 novelty judgment. The
recorded queues are fully classified, but the audit has zero
protocol-complete citation waves: identifier gaps, incomplete keyed OpenAlex
and Semantic Scholar discovery, Semantic Scholar rate limiting, and
publisher-elided reference lists prevent the stopping rule from firing. All
screening decisions still await human confirmation, independent expert review
has not occurred, and S227 remains a partial-full-text assessment.

## Broad claims defeated by prior art

The audit has already established that the following claims would be false or
materially misleading:

- first Treiber lock-freedom proof;
- first Treiber termination or total-correctness proof;
- first machine-checked Treiber liveness proof;
- first relaxed-memory Treiber safety or linearizability proof;
- first mechanized weak-memory liveness framework;
- first formal model capable of expressing weak-CAS fairness;
- first weak-memory verification tool supporting genuinely weak CAS;
- first primitive-fairness mechanism excluding an all-spurious trace; and
- first observation that weak CAS needs a progress/fairness condition;
- first separation of scheduler fairness from an additional
  primitive/reservation-success premise;
- first formal or tool-checked exact-CAS Treiber retry-loop termination proof;
- first weak-memory model checker carrying a Treiber benchmark; and
- first mechanized weak-memory model to combine independently failing
  load/store exclusives with finite Treiber exploration inputs;
- first exact-CAS partial-Treiber result combining linearizability with
  scheduler-sensitive partial deadlock-freedom;
- first exact-CAS elimination-stack lock-freedom argument conditional on fair
  internal branch choice; and
- first use of a memory-service progress bound, distinct from scheduler
  progress, to obtain bounded or wait-free algorithmic progress.

## Highest-severity novelty threats

### Fair Operational Semantics

The FOS paper and Coq artifact predate this project. The artifact defines an
address-indexed `cas_weak` whose nondeterministic spurious-failure branch emits
a fairness failure event. Its well-founded fairness counter is designed to
exclude an infinite sequence of failures at the same address. This is already
a formal weak-CAS primitive-fairness model.

The definition is not used by a theorem, client, or data structure in the
artifact. The paper's weak-memory case study instead proves ticket-lock
refinement using load, store, and fetch-and-add. FOS therefore defeats novelty
for the primitive mechanism, but not for the integrated weak-CAS Treiber
theorem.

### Lilo

Lilo proves Coq-mechanized termination-guaranteeing specifications for
Treiber's stack and the elimination stack. The Treiber implementation uses
strong CAS in a single-heap interleaving model, and the proof relies on every
failed CAS witnessing a successful interfering update. Its guarantee is
conditional on a finite-use obligation.

The Lilo artifact also carries the unused FOS-style fair `cas_weak` definition.
Thus one artifact contains both a mechanized strong-CAS Treiber liveness proof
and a separate fair weak-CAS primitive. It does not connect them. This makes
Lilo the closest integration threat and requires the candidate claim to keep
the RC11, genuinely weak-CAS, integrated theorem, and unbounded-response
qualifiers explicit.

### Haas et al.

The fair-recurrence-set paper explicitly identifies spurious weak CAS and
LL/SC as a further platform-fairness dimension, then omits it from the
developed theory while saying that incorporation is straightforward. Its
recurrence-set theorems are unbounded; only parts of the automated search are
bounded.

A follow-up source audit found that Dartagnan implements part of the omitted
dimension. The paper-era nontermination encoder requires every
`RMWStoreExclusive` reached in a repeating suffix to execute, explicitly to
exclude infinite spurious failure. The rule entered the repository in
[PR 772](https://github.com/hernanponcedeleon/Dat3M/pull/772), merged on
2025-03-10. The paper's public artifact-branch snapshot
[`44553917`](https://github.com/hernanponcedeleon/Dat3M/tree/445539172ba3af3c2020409249053e3c5f356bc2)
contains that rule, but its C11 frontend still compiles LLVM compare-exchange
as strong. Proper preservation of LLVM's weak compare-exchange flag arrived
after the paper's January 2026 publication in
[PR 976](https://github.com/hernanponcedeleon/Dat3M/pull/976), merged on
2026-03-05.

At the cutoff-pinned repository commit
[`a7e3e484`](https://github.com/hernanponcedeleon/Dat3M/tree/a7e3e4843359dde3a0e29500a821030e2433e316),
these two implementation pieces compose for weak LLVM compare-exchange.
That source tree also contains a Treiber benchmark, but it calls strong CAS
and the C11 and RC11 regression suites expect `UNKNOWN`, not a successful
termination verdict. No Treiber theorem, weak-CAS Treiber benchmark, positive
progress proof, or integrated all-spurious separation was found.

The project must therefore claim a completed, checked algorithm/model
instantiation and separation result—not invention or first implementation of
the primitive-fairness dimension.

### Citation-wave closest additions (PA41--PA47)

Seven additional sources sharpen the boundary without defeating the exact
conjunction:

- Atig et al. (S52/PA41) reduce bounded-stem/bounded-lasso detection of
  strongly fair, ultimately periodic nontermination to sequential assertion
  reachability (Lemma 5) and use MUTANT to find an `OptimisticList`
  nontermination lasso. This is detection of a negative execution under an
  atomic shared-memory model, not a positive Treiber progress theorem, an
  RC11 result, or a proof-assistant certificate.
- Liang et al. (S53/PA42) directly prove Treiber linearizability and
  lock-freedom together in §4.3 and Figures 22--24, using their
  termination-preserving refinement of Definition 1. Their progress argument
  states that failure of the push/pop CAS must be caused by another thread's
  successful update. The atomic, exact-match strong-CAS result defeats broader
  wording about the first compositional Treiber safety-plus-progress proof,
  but has no RC11 semantics, compare-equal failure, primitive justice, or
  machine-checked artifact.
- Colvin and Groves (A32/PA43) report PVS-checked verification of a
  finite-process scalable elimination stack in an atomic interleaving model.
  The accessible companion derivation defines exact-match CAS and identifies
  the earlier I/O-automata/PVS result as preservation of linearizability; the
  verification lineage is not a progress proof. The exact SEFM paper remains
  access-limited for line-level confirmation, but the available primary
  evidence does not support calling its PVS result a lock-freedom theorem.
- Doherty's thesis (S54/PA44) gives PVS-checked nonblocking-data-structure
  verifications in Chapters 3, 4, and 6. Chapter 5 separately presents a
  lock-freedom-preserving transformation and applies it to Treiber under
  atomic exact-CAS semantics; the thesis does not identify that transformation
  as PVS-checked. Section 7.2.2 explicitly says relaxed consistency is not
  treated and that shared-memory operations are assumed atomic. It is strong
  classical verification lineage, not a mechanized weak-memory or weak-CAS
  justice result.
- RoboCop (S55/PA45) proves RC20 execution-graph robustness, a safety
  property, through Theorems 4.4 and 4.6 and the composition results of
  Theorems 6.1 and 6.2; Treiber appears in its evaluation. Its §5.4
  transformation removes independent failed CAS-loop iterations and replaces
  the final CAS with blocking CAS, with robustness preservation stated as
  Lemma 5.4. Appendix A's failure rule requires a value mismatch, and the
  archived Treiber input calls `atomic_compare_exchange_strong_explicit`.
  That abstraction deliberately does not preserve the retry behavior needed
  for genuine-weak-CAS liveness, so it supplies neither a progress theorem nor
  an all-spurious separation.
- Jung et al. (S56/PA46) use Algorithm 1's RCU-protected Treiber stack as an
  illustrative iRC11 safety argument whose relaxed-memory adaptation accounts
  for stale head messages. The archived Rocq development mechanizes the
  general-purpose RCU, Peterson mutex, Michael--Scott queue, and Harris-list
  clients, but its README and file inventory identify no Treiber development.
  Thus even the Treiber safety overlap is not machine-checked on the available
  artifact. The CAS is exact, and neither paper nor artifact proves Treiber
  termination, primitive justice, or response progress.
- Margalit et al. (S59/PA47) give RSan, a dynamic RC20 robustness verifier.
  Section 4.1, footnote 3 expressly says its weak CAS may fail after reading
  the expected value and that the development and tool support both weak and
  strong CAS. This is direct C11-style genuine-weak-CAS tool support and
  defeats any broader priority wording at that level. Theorem 3.1 concerns
  robustness, however, and §4.3's `BCAS` annotations omit failed CAS-loop
  attempts. The paper and audited artifact metadata state no Treiber theorem,
  positive liveness result, fairness factorization, primitive justice, or
  all-spurious progress separation. The 12.3 GB Docker image itself was not
  downloaded, so this audit makes no source-level absence claim about its
  contents.

Accordingly, PA42 narrows broad classical Treiber wording, PA45--PA46
substantially narrow relaxed-memory safety wording, and PA47 narrows genuine
weak-CAS tool wording. None of PA41--PA47 proves
genuinely weak-CAS Treiber progress, the three-way fairness separation, the
integrated all-spurious RC11 execution, or the full machine-checked
safety/liveness conjunction.

The same citation wave promoted four non-closest boundaries. Vafeiadis's CAV
overview (S57) displays exact CAS in weak-memory separation logics but gives no
Treiber liveness result. Mével and Jourdan (S58) Coq-check bounded-queue
functional correctness under the Multicore OCaml weak-memory model and
explicitly state that the queue has no nonblocking property. Baumann et al.
(S61) decide context-bounded fair nontermination and fair starvation for
dynamically spawned shared-memory threads without CAS or relaxed memory.
Dang's dissertation (S60) is retained as a version audit of the Compass/iRC11
lineage because it expands the mechanized relaxed-memory Treiber and
elimination-stack safety developments while remaining exact-CAS partial
correctness.

The PA47 citation follow-up added two older safety boundaries. Burckhardt and
Musuvathi's Sober work (S62) monitors TSO/store-buffer safety but has no CAS
result semantics or liveness theorem. Linden and Wolper (S63) verify cyclic
x86-TSO state reachability and synthesize fences; CAS is a barrier-bearing
exact operation and their algorithm-termination argument is not concurrent
program progress. Neither changes the surviving six-part conjunction.

### Pending-full-text closest additions (PA48--PA52)

Five resolved full texts materially narrow broad wording while leaving the
exact conjunction intact:

- Koval et al.'s CQS (S67/PA48) is a formally verified framework for fair and
  abortable synchronization. Its checked HeapLang/Iris development assumes
  sequential consistency and equality-guarded ordinary CAS; the paper's
  Appendix F.4 uses a modified Treiber stack for outer storage. The pinned
  live `cqs-proofs` branch contains 33 Coq files, but no liveness/fairness
  definition and none of the blocking-pool or outer-stack files referenced by
  the paper. CQS is therefore direct fair-synchronizer and
  Treiber-construction prior art, not a machine-checked Treiber progress
  result under weak memory or genuine weak CAS. The missing public files are
  an artifact-completeness limitation, not evidence that no fuller private
  development exists.
- Kokologiannakis and Vafeiadis's GenMC (S70/PA49) is prior C11/RC11-family
  model-checking infrastructure whose v0.6 regression suite includes a
  Treiber stack. The public header exposes weak compare-exchange, but the
  audited execution visitor decides success by value equality without using
  LLVM's weak flag, and the bundled Treiber input calls strong
  compare-exchange. GenMC checks bounded safety/error properties; it gives no
  positive liveness theorem, fairness factorization, primitive justice, or
  all-spurious separation. It defeats broad novelty wording about applying a
  weak-memory model checker to Treiber.
- Gao and Hesselink's 2004 reduction (S76/PA50) already combines a
  PVS-supported safety/refinement argument with classical lock-free liveness
  under strong fairness and a distinct eventual-valid-reservation premise for
  LL/SC. That extra premise is structurally analogous to primitive progress
  and defeats any claim that this project first recognized the need to
  supplement scheduler fairness. The paper has no Treiber instance, RC11
  semantics, genuine weak CAS, prefix-finite memory fairness, or integrated
  all-spurious counterexecution.
- Jacobs, Bošnački, and Kuiper (S78/PA51) use VeriFast to check termination of
  finite clients executing a direct Treiber-style push loop; pop is analogous.
  Under their sequentially consistent exact-CAS semantics, every retry
  witnesses another successful operation and transfers a termination
  permission. The concurrent stack example is tool-checked, while the
  separately advertised Coq companion covers generic termination theory
  rather than that stack. This defeats broad wording about the first formal or
  automated Treiber CAS-loop termination proof, but compare-equal spurious
  failure invalidates its central retry-as-interference step.
- Gao's 2005 thesis (S87/PA52) expands PA50's historical lineage. Its
  Chapter 4 adds a generic exact-CAS refinement and handwritten lock-freedom
  argument under strong fairness plus an eventual
  matching-indirection/success premise. The thesis explicitly reports PVS
  support for invariants and simulation while deferring liveness
  mechanization. It therefore reinforces the prior separation between
  scheduler fairness and an extra platform-success premise, but adds no
  Treiber instance, weak memory, genuine weak CAS, primitive justice, or
  all-spurious counterexecution.

Accordingly, the surviving contribution cannot be phrased as the first fair
synchronization proof, the first additional primitive-success premise beyond
scheduler fairness, the first formal Treiber retry-loop termination proof, or
the first weak-memory model checker with a Treiber benchmark. None of
PA48--PA52 supplies the combined RC11 Treiber model, genuine weak-CAS
spuriosity, three-way fairness separation, integrated all-spurious execution,
unbounded system-wide response, and machine-checked finite-prefix safety
composition.

### Exhaustive legacy-queue additions (PA89--PA118)

The completed record-by-record classification of the 1,167-work legacy
citation queue promoted 30 further theorem-level comparators. This larger set
does not create a subsuming result, but it materially changes which broad
claims are defensible.

PA89--PA93 add a release-acquire wait-free construction/lower-bound line,
generic contextual-refinement characterizations of safety and progress,
liveness-preserving atomicity abstraction for an elimination/Treiber-style
stack, and Fraser's early LL/SC premise that rules out infinitely many
spurious store-conditional failures. These are strong weak-memory,
progress-theory, and primitive-progress precedents, but no one work combines a
Treiber client, RC11, genuine weak CAS, primitive justice, and mechanization.

PA94--PA105 establish a dense pre-existing Treiber verification landscape:
bounded PAT and divergence-sensitive model checking; KIV linearizability;
Coq/FCSL, Diaframe, and ReLoC safety proofs; parameterized shape analysis;
coarse-grained abstraction; temporal logic; and automated CAVE/TVLA
linearizability. Several cover arbitrary threads or machine-checked client
reasoning, and PA95/PA105 check both linearizability and lock-freedom on
bounded models. They use sequentially consistent exact CAS and do not provide
the target weak-memory progress separation.

PA106--PA117 add mechanized RC11 RCU safety, CafeOBJ reclamation safety,
unbounded-thread shape/linearizability analyses, further FCSL and KIV stack
proofs, and an obstruction-freedom logic. PA110 is the strongest direct
liveness neighbor in this slice: Derrick, Schellhorn, and Wehrheim combine
stack linearizability with a well-founded termination condition for a fixed
two-process push/pop composition. The proof is handwritten, sequentially
consistent, and exact-CAS; it is neither an unbounded weak-memory result nor a
mechanized safety/liveness composition.

PA118, *Promising-ARM/RISC-V*, is the closest newly identified hardware-model
threat. Its Coq semantics exposes a store-exclusive failure step with no
mismatch or interference premise, and its supplement includes finite C++ and
Rust Treiber exploration inputs. The source-level Treiber programs use strong
compare-exchange, while the checked theorems concern operational/axiomatic
model equivalence, certification, promise computation, and RISC-V
deadlock-freedom. The work therefore defeats broad novelty wording about the
combination of a mechanized weak-memory model, independent exclusive failure,
and Treiber test cases. It supplies no primitive justice, all-spurious
separation theorem, unbounded Treiber response result, or machine-checked
Treiber safety-and-liveness composition.

### Final legacy-promotion additions (PA119--PA122)

The citation expansion of the 30 legacy promotions added four high-value
comparators:

- Groves and Colvin (S227/PA119) derive an exact-CAS elimination stack and, in
  the accessible 2007 precursor to the 2009 journal article, manually argue
  system lock-freedom conditional on fair internal choice between elimination
  and the central stack. The exact journal PDF remains subscription-restricted,
  so the liveness claim is attributed to the accessible precursor lineage,
  not silently to uninspected pages. The argument is SC, informal, and
  unmechanized.
- Morrison and Afek (S228/PA120) keep scheduling asynchronous while requiring
  every TSO store to become globally visible within a fixed real-time
  \(\Delta\). They derive wait-free fence-free hazard-pointer reclamation and
  bounded/nonblocking biased-lock behavior from that memory-service premise.
  This is a strong predecessor for separating scheduler and memory progress,
  but it is neither RC11 nor Treiber, uses exact atomics, and the proposed
  hardware bound is not proved for deployed processors.
- Liang and Feng's 2020 tutorial (S229/PA121) is an authoritative synthesis of
  exact-CAS Treiber safety/progress and explicit ordinary, strong, and weak
  scheduler fairness. It consolidates the authors' 2013--2018 results and is
  retained as a theorem map rather than an independent priority source.
- Their original partial-method paper (S230/PA122) and extended report apply
  generalized LiLi to an exact-CAS Treiber stack with a possibly blocking
  pop. The stack obtains linearizability plus partial deadlock-freedom under
  weak, and hence strong, fairness. The general logic supports partial
  starvation-freedom only under extra level-0 rely/guarantee premises; the
  Treiber application does not discharge those premises. The proof is
  handwritten and SC.

Across PA89--PA122, every row has `subsumes_candidate=no`. The strongest
pieces remain distributed across different works: weak-memory metatheory,
independently spurious hardware failure, bounded Treiber safety/progress,
classical exact-CAS liveness, explicit scheduler/memory progress premises,
and machine-checked Treiber safety. The target contribution survives only as
their exact six-part conjunction.

### Classical and SC Treiber progress

The mechanized lineage begins earlier than the initial matrix showed. Colvin
and Dongol's 2007 ICTAC paper reports a direct PVS-checked Treiber
lock-freedom proof using a global well-founded order: from every snapshot,
eventually some process reaches a designated progress set. The full paper is
access-controlled, so the exact theorem text still needs human confirmation,
but the publisher abstract and the primary-author thesis are already enough to
defeat any “first machine-checked Treiber lock-freedom” wording.

Their 2009 paper generalizes and supersedes the method, but it must not be
counted as a second completed Treiber mechanization. Its published checked
cases are the Michael–Scott and bounded-array queues. The author-hosted PVS
bundle contains a legacy `treiber.pvs`, but no `treiber.prf`; lines 401–412
mark two well-foundedness obligations “Will not prove.” The 2007 direct
Treiber result and the 2009 generic queue artifact are therefore distinct
evidence.

Tofan, Schellhorn, and Reif's 2011 KIV development proves memory safety, ABA
prevention, linearizability, and system lock-freedom for a Treiber stack with
hazard-pointer reclamation. Their later RGITL development gives a
KIV-mechanized linearizability and lock-freedom proof for a Treiber-derived
data/free-stack implementation with explicit memory reuse. Gotsman et al.,
Total-TaDA, quantitative lock-freedom work, CAVE, and Lilo add further
classical or SC-style Treiber progress results. All use strong CAS or an
equivalent failure-implies-interference rule.

These works establish that the contribution can only come from the weak-memory
and weak-CAS assumptions and their separation, not from Treiber progress by
itself.

Derrick, Schellhorn, and Wehrheim's 2008 KIV development supplies another
important boundary: it mechanically proves a Herlihy--Wing linearizability
result for a simplified, reclamation-free Treiber stack and an arbitrary
number of processes, but it proves no lock-freedom or termination theorem.
Parkinson, Bornat, and O'Hearn's earlier hazard-pointer stack proof is manual,
partial-correctness separation logic and explicitly disclaims both
linearizability and liveness. These works further narrow any safety or
mechanization claim without touching the target weak-CAS progress
conjunction.

Two quantitative results narrow progress wording. Petrank, Musuvathi, and
Steensgaard formally distinguish ordinary from bounded lock-freedom,
CHESS-check 2–6 one-shot harnesses for the Herlihy--Shavit
`LockFreeStack`—a standard Treiber-style strong-CAS stack—under explicit SC,
and manually prove a generic program/service progress-composition theorem.
CHESS does not symbolically prove the inferred all-\(n\) bound. The same paper
explicitly warns that spurious weak LL/SC failure can destroy lock-freedom
even while threads receive CPU steps. It does not connect that observation
to its stack model or formalize primitive justice. Pani, Weissenbacher, and
Zuleger later use Coachman and rely--guarantee bound analysis to infer
per-edge and polynomial total bounds for a symbolic-\(N\), one-operation-per-
thread Treiber client. That is a strong parameterized finite-batch result
under SC, exact-match CAS, and garbage collection, not an infinite-demand
response theorem.

Friggens's 2013 thesis supplies an additional direct boundary. It formulates
Treiber wait-/lock-freedom in LTL, makes weak scheduler fairness explicit, and
uses Spin to find the expected non-wait-free execution and verify
lock-freedom on fixed small instances. Its separate TVLA/3VMC development
establishes unbounded Treiber linearizability, but the thesis expressly says
that finite-execution canonical abstraction is unsuitable for progress. The
bounded liveness checks and unbounded safety analysis therefore do not form
an all-thread progress theorem.

Hoffmann, Marmar, and Shao give a stronger classical theorem: their
quantitative concurrent separation logic manually proves system-wide
lock-freedom for strong-CAS Treiber across arbitrary fixed finite thread
populations and finite client workloads, with a quantitative interference
bound and compatible memory-safety reasoning. Jia, Li, and Vafeiadis then
automate a corresponding unbounded system-response check with CAVE. Their
Coq bundle checks the generic instrumentation metatheory, not an end-to-end
Treiber certificate. Both arguments depend on a failed CAS certifying another
thread's successful update, so neither covers compare-equal spurious failure,
RC11, or the target three-way fairness split.

Several titles are less threatening than they first appear. Caires, Ferreira,
and Ravara's short *A Simple Proof System for Lock-Free Concurrency* and
Serra's expanded thesis prove only partial correctness for strong-LL/SC list
operations; termination and fairness remain open. Tofan et al.'s 2010 KIV
temporal method proves a Michael--Scott queue case, with later direct Treiber
descendants already represented above. Hendler, Shavit, and Yerushalmi
manually prove the elimination-backoff stack linearizable and lock-free, but
its central Treiber path again uses strong CAS and failure-as-interference.
Peterson, Cook, and Dechev mechanize descriptor-helping progress in Coq/VST
for a transactional list and wait-free queue, not Treiber or weak memory.

### TSO liveness decidability and unified-fairness version drift

Wang et al.'s final 2026 *Decidability of Liveness on the TSO Memory Model*
substantially expands the earlier SETTA result. In addition to the
undecidability of lock-, wait-, deadlock-, and starvation-freedom and the
decidability of obstruction-freedom, the final abstract reports decidability
of fixed-\(k\) bounded wait-freedom, non-primitive-recursive complexity, and a
TSO object that is wait-free but not \(k\)-bounded wait-free for any \(k\).
This is strong weak-memory liveness prior art, including a scheduler-fairness
formulation and a memory-flush robustness observation. Its generic
bounded-process libraries use exact-match CAS, not Treiber or genuinely weak
CAS, and the final theorem text still needs publisher-copy confirmation.

The 2024 extended version of Abdulla et al.'s unified-fairness work likewise
must not be silently treated as the short CAV paper. It expands the model to
additional speculative/racing-read behaviors and ARMv8/POWER, repairs
version-1 model issues, and generalizes verification to stutter-insensitive
omega-regular properties. It remains the same prior-art lineage, uses a
non-spurious atomic RMW, and contains no Treiber or machine-checked weak-CAS
justice theorem.

### Standards and early weak-primitive progress warnings

The practical need for a progress condition on spurious compare-exchange is
old. [WG21 N2427](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2007/n2427.html)
permitted spurious failure and presented an insert-only linked-list head loop
as informally lock-free; its `list_example_weak` label referred to weak memory
ordering, not to the later weak-CAS API.
[N2748](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2008/n2748.html)
then introduced the explicit weak/strong compare-exchange names.
[N3209](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3209.htm)
proposed non-binding encouragement against consistent weak-CAS failure;
[Library issue 2075](https://timsong-cpp.github.io/lwg-issues/2075)
separated scheduler isolation from implementation-level LL/SC progress and
noted that unrelated writes can induce target-object livelock; and
[N3927](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2014/n3927.html)
ultimately required only a solo-thread, obstruction-free floor while leaving
concurrent system-wide progress as a “should.”

These documents defeat any claim to have first recognized the problem or the
scheduler/primitive distinction. They do not make eventual non-spurious
success a theorem of ISO C++ executions, and they contain no RC11 Treiber
model, fairness separation, or mechanization. The candidate must be described
as a checked full conjunction, not as the origin of the weak-CAS progress
intuition.

### Relaxed- and persistent-memory Treiber safety

Compass, the OMO Proof Recipe, and the Isabelle C11-style refinement
development already mechanize Treiber safety, refinement, or linearizability
in RC11-family relaxed-memory settings. Their compare-and-exchange rules are
strong: failure requires a mismatch. None supplies a fairness-separated
weak-CAS liveness theorem.

The iRC11 relaxed-memory separation-logic development of Park et al. further
shows that mechanized logically atomic specifications are available for
Harris-style lists, a lock-free skiplist, and a skiplist priority queue under
RC11. Its artifact again gives CAS failure only on inequality. It contains no
Treiber client and no termination, fairness, or response theorem; “lock-free”
and “wait-free” in the paper describe algorithms rather than proved progress
properties.

Relinche narrows the RC11 safety boundary further: its GenMC-backed checker
automatically establishes bounded contextual refinement for Treiber variants
under RC11. Theorem 4.3 quantifies over clients respecting a fixed number of
method invocations and the implementation explores finite executions. It is a
strong automated safety neighbor, not an infinite-execution liveness theorem;
it has no scheduler fairness, prefix-finite memory fairness, weak-CAS justice,
or all-spurious separation.

Three persistent-memory works narrow the boundary further. Memento formalizes
detectable recoverability and erasure and implements a persistent Treiber
stack with an exact-match helping CAS, but does not machine-check the target
response-progress composition. Spirea Coq-mechanizes a durable Treiber case
under a view-based weak-persistent-memory semantics. Its CAS failure rule
requires inequality, and Section 6.3.2 explicitly states that the verified
specification implies neither linearizability nor LIFO. It proves thread and
crash safety, not liveness.

Spirea's unreviewed `high-nextgen-logic` branch, pinned at commit
[`925a8d7a`](https://github.com/logsem/spirea/tree/925a8d7a7c69c0c83163fe78d0d93f668e0558ca),
substantially strengthens the durable Treiber safety development and includes
it in the branch build list. The branch remains unprotected, has no pull
request or recorded CI checks, retains mismatch-only strong CAS, and still
supplies no fairness or termination theorem. It narrows the current safety
comparison but leaves the candidate liveness boundary unchanged.

Schellhorn et al.'s *Mirror is Not Strong* supplies genuine durable weak-CAS
prior art. KIV exposed that Mirror implements `compare_exchange_weak`, whose
failure action permits failure even when the stored and expected values are
equal. The 73-obligation lower Mirror-to-IMirror refinement is mechanized, but
the upper IMirror-to-PLib refinement is explicitly unfinished. The work has no
Treiber client, no RC11 carrier, no weak-CAS justice, and no progress theorem.
It defeats priority for mechanized discovery or modeling of genuine weak CAS,
not the exact algorithmic progress conjunction.

These results rule out broad wording about the first mechanized Treiber proof
under weak or persistent memory. Mirror supplies genuine weak CAS but no
Treiber or progress theorem; the Treiber results use exact-match CAS. None
combines genuine weak CAS with primitive justice, an all-spurious independence
execution, and unbounded system-response progress.

### Modern mechanized boundary cases and tool omissions

Several recent developments combine Treiber with a neighboring notion of
safety, cost, or liveness without proving operation progress:

- *Will It Fit?* Coq/Iris-mechanizes functional and heap-space specifications
  for a strong-CAS Treiber stack. Its Theorems 8.2–8.3 prove bounded-time
  allocation enablement after polling-point insertion, not push/pop response
  or lock-freedom.
- *Parcas* Coq/Iris-mechanizes Treiber linearizability and work/span bounds
  under fixed participant and finite operation budgets. The paper explicitly
  says this is not a formal lock-freedom proof.
- *Zoo* verifies functional correctness of three OCaml Treiber variants in
  Rocq/Iris under a sequentially consistent semantics. Relaxed memory is
  future work and no progress theorem is claimed.
- The modular safe-memory-reclamation development verifies logically atomic
  Treiber specifications with garbage collection, hazard pointers, and RCU,
  again under SC and without a stack progress theorem.
- Pöter's 2018 C++ thesis defines compare-equal spurious weak-CAS failure and
  informally argues that such failures do not spoil the lock-freedom of a
  non-Treiber Stamp-it queue. It predates the candidate but supplies neither a
  formal fairness premise nor a mechanized or RC11 theorem.

The Miri–GenMC thesis gives direct tool-boundary evidence. Its RC11 Treiber
benchmark uses strong Rust `compare_exchange`, removes reclamation, and is a
bounded safety/performance experiment. The thesis states that GenMC does not
explore compare-equal spurious failures and demonstrates a weak-CAS bug that
the integration misses; the cutoff-pinned GenMC source retains both that
omission and strong-CAS Treiber tests. This corroborates the semantic gap
rather than filling it.

Together with Dartagnan's current suffix-fairness implementation, these cases
show why “the tools do not support this” is too broad. Some tools cover RC11
Treiber safety, some express or constrain spurious failure, and some prove
Treiber progress under strong CAS. No inspected artifact composes all three
with the target finite-prefix safety and unbounded response theorem.

## The remaining defensible boundary

Until the audit reaches independent review, use a factual contribution
statement:

> We give a machine-checked progress and separation result for an explicit
> finite-thread, reclamation-free Treiber/RC11 model with genuinely weak CAS:
> weak thread fairness, prefix-finite memory visibility, and a separate
> weak-CAS justice assumption imply system-wide response progress; thread and
> memory fairness alone admit an RC11-valid all-spurious infinite execution;
> and every finite prefix satisfies the existing linearizability package.

If the remaining search and expert review find no defeating result, a
date-bounded priority qualifier may be tested:

> To the best of our knowledge as of 2026-07-31, this is the first proof of
> that full conjunction.

The words “full conjunction” are essential. Each major component separately
has substantial prior art.

## Remaining falsification work

The exact claim still fails if any source supplies:

- a weak-CAS Treiber theorem under RC11 or a model that directly subsumes it;
- a FOS/Lilo artifact theorem that actually connects `cas_weak` to Treiber;
- an earlier mechanized result with the same all-spurious independence
  witness and unbounded response conclusion;
- a scheduler or memory-fairness definition that already entails the project's
  primitive justice; or
- a stronger weak-memory result from an unindexed thesis, repository, or
  extended version.

The existing internal queues do not contain unscreened candidates. The
remaining work is to repair or replace the keyed OpenAlex and Semantic Scholar
discovery gaps, resolve missing identifiers and publisher-elided references,
and rerun citation expansion until the registered stopping rule records the
required protocol-complete waves rather than its current count of zero. The
human-confirmation fields for all decisions must then be adjudicated, the
partial-full-text S227 assessment and any other access-limited exclusions must
be independently checked, and domain experts must return explicit reviews of
the claim card and theorem-level matrix. Until those steps close, the exact
conjunction is a surviving N0–N1 hypothesis, not a certified priority result.
