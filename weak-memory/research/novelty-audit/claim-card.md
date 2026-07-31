# Claim Card: Fair Weak CAS under RC11

## Versioned subject

- **Artifact:** `Talha-Dmr/verified-systems-lab`
- **Model:** `WeakMemory.TreiberC11V1`
- **Public Lean surface:** `WeakMemory/WeakCASTreiberResult.lean`
- **Algorithm:** finite-thread, reclamation-free Treiber stack
- **Memory setting:** coherent infinite carrier with RC11-valid finite
  declarative prefixes
- **Primitive:** weak compare-and-exchange, including compare-equal spurious
  failure
- **Progress level:** system-wide response progress (lock-freedom), not
  per-operation starvation-freedom or wait-freedom

## Exact positive result

For every execution in the versioned model:

```text
weak thread fairness
  + prefix-finite from-read
  + primitive weak-CAS justice
  + the Treiber source/control and RC11-prefix contracts
  => system-wide response progress
```

Paired prefix-finite modification-order/from-read memory fairness is exposed
as a conventional corollary. Finite-prefix Herlihy--Wing linearizability
composes with the progress theorem. Under recurring pending push/pop demand,
responses occur arbitrarily late.

The main public aliases are:

- `treiberSystemResponseProgress_of_fromReadFairness`;
- `treiberSystemResponseProgress_of_memoryFairness`; and
- `treiberLinearizableLongRun_of_fromReadFairness`.

## Exact negative result

There exists one coherent infinite execution in the same
`InfiniteRC11Execution` carrier such that:

- every raw finite prefix is a valid declarative RC11 execution;
- weak thread fairness holds;
- paired memory fairness holds;
- pending push demand recurs;
- the supplying write and compared value remain stable;
- arbitrarily late compare-equal weak-CAS attempts all fail spuriously;
- primitive weak-CAS justice fails; and
- system-wide response progress fails.

The public alias is `treiberAllSpuriousSeparation`.

## Reuse evidence

The generic single-site system-progress rule is separately instantiated on a
Treiber-independent weak-CAS increment loop. The counter has both a
success-rich witness and an all-spurious separation execution. This is
evidence of logical reuse, not a second RC11 case study.

## Candidate novelty

The strongest candidate claim to test is:

> To the best of our knowledge as of the stated search cutoff, this is the
> first machine-checked proof of the full conjunction of: an explicit
> finite-thread, reclamation-free RC11 Treiber model; genuinely weak CAS;
> primitive weak-CAS justice distinct from scheduler and memory fairness; an
> RC11-valid all-spurious Treiber execution proving that distinction;
> unbounded system-wide response progress; and finite-prefix linearizability.

This wording is not approved for publication until the reproducible search
and independent expert review are complete.

The words “full conjunction” are mandatory. Fair Operational Semantics
already formalizes a fair weak-CAS primitive, and Lilo already mechanizes
termination-guaranteeing Treiber specifications under strong CAS. Neither
component is new by itself. Gao and Hesselink already separate scheduler
fairness from an additional reservation-success premise, Jacobs et al.
already tool-check exact-CAS Treiber-loop termination, CQS already combines
fair synchronization with a Treiber-derived construction at paper level, and
GenMC already carries a Treiber benchmark in a weak-memory model checker.
Promising-ARM/RISC-V already combines a mechanized weak-hardware-memory model
with an independently spurious store-exclusive rule and bounded C++/Rust
Treiber test inputs. The candidate therefore makes no broad claim to the first
mechanized model or tool containing both a spurious exclusive primitive and a
Treiber-shaped program.

Liang and Feng's partial-method result and 2020 tutorial already integrate
exact-CAS Treiber linearizability with scheduler-sensitive progress, including
partial deadlock-freedom for a blocking-pop variant. Groves and Colvin already
argue system lock-freedom for an exact-CAS elimination stack under fair
internal branch selection. Morrison and Afek already separate an asynchronous
scheduler from a hard memory-service deadline and derive bounded or wait-free
progress for non-Treiber algorithms. None of those ingredients is new in
isolation.

## Explicit exclusions

The artifact does not claim:

- the first Treiber safety or relaxed-memory linearizability proof;
- the first mechanized Treiber termination or liveness proof;
- the first formal fair weak-CAS primitive;
- the first weak-memory model or verification tool supporting genuine weak
  CAS;
- the first formal mechanism excluding an infinite all-spurious trace;
- the first weak-memory fairness or liveness formalism;
- the first framework capable of expressing custom primitive fairness;
- the first separation of scheduler fairness from an additional
  primitive/reservation-success premise;
- the first formal or tool-checked exact-CAS Treiber retry-loop termination
  proof;
- the first fair synchronization framework using a Treiber-derived
  construction;
- the first weak-memory model checker carrying a Treiber benchmark;
- the first mechanized weak-hardware-memory model with independently spurious
  exclusive failure and bounded Treiber examples;
- the first exact-CAS partial-Treiber proof combining linearizability with
  scheduler-sensitive partial deadlock-freedom;
- the first exact-CAS elimination-stack lock-freedom argument using a fair
  internal branch-choice premise;
- the first separation of scheduler asynchrony from a memory-service progress
  premise used to derive nonblocking or bounded algorithmic progress;
- a full ISO C semantics or an unconditional portable ISO C lock-freedom
  theorem;
- memory reclamation, address reuse, or ABA safety;
- per-thread starvation-freedom or wait-freedom;
- minimality of the justice assumption;
- necessity of full paired memory fairness;
- a site-indexed multi-location progress rule; or
- one projectively coherent linearization order for the entire infinite
  history.

## Novelty falsifiers

The candidate claim must be withdrawn or narrowed if prior work supplies any
of the following:

1. the same positive theorem for weak-CAS Treiber under RC11 or a strictly
   stronger memory model result that directly subsumes it;
2. the same scheduler/memory/primitive-fairness separation with an integrated
   all-spurious Treiber counterexecution;
3. a mechanized generic rule already instantiated on weak CAS and Treiber with
   the same unbounded progress conclusion;
4. an earlier formal artifact whose paper omits the result from its title or
   abstract; or
5. a definition under which the purported primitive-justice assumption
   already follows from the adopted scheduler or memory fairness.

## Questions for reviewers

1. Do you know an earlier theorem equivalent to, or stronger than, the exact
   candidate claim?
2. Does the model hide primitive progress inside another assumption?
3. Is prefix-finite from-read used in a way consistent with the closest RC11
   memory-fairness literature?
4. Does “system-wide response progress” match the claimed lock-freedom level?
5. Is any exclusion above too weak or missing?
