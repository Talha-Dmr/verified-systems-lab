# Publication Boundary for the Fair Weak-CAS Result

**Status:** internal adversarial audit passed; external expert review and a
submission-time literature search remain required
**Model version:** `TreiberC11V1`
**Review date:** 2026-07-31

**Post-review note:** the working tree now contains a conservative
site-indexed extension and a two-site validation client. Those later results
are exposed through `WeakCASSiteResult` and documented in
`site-indexed-progress-roadmap.md`; they are not silently folded into the
audited `TreiberC11V1` claim below.

## 1. Result in one sentence

For the repository's explicit finite-thread, reclamation-free Treiber model,
every coherent infinite execution whose finite prefixes are valid RC11
declarative executions has system-wide response progress under weak thread
fairness, prefix-finite `fr`, and a separate primitive weak-CAS justice
assumption; every finite prefix is also Herlihy--Wing linearizable, and the
standard paired prefix-finite `mo`/`fr` formulation follows as a corollary.

This is a conditional theorem about the versioned model. It is not an
unconditional ISO C or hardware progress theorem.

## 2. Kernel-checked theorem surface

`WeakMemory/WeakCASTreiberResult.lean` is the compact public entry point. It
re-exports the pieces below as documented theorem aliases and adds
`positiveAssumptionsJointlySatisfiable`, a single existential statement
bundling the concrete positive witness.

The integrated negative separation theorem is:

```lean
WeakMemory.TreiberC11V1.InfiniteSpurious
  .threadFair_memoryFair_do_not_imply_progress :
  ∃ candidate : InfiniteRC11Execution Unit 1,
    candidate.source.WeakThreadFair ∧
    candidate.MemoryFair ∧
    candidate.RecurringPushPopDemand ∧
    ¬ candidate.WeakCASJustice ∧
    ¬ candidate.SystemResponseProgress
```

The smaller `WeakCAS.AllSpurious` theorem remains as an independent
one-location sanity check.

The reusable logical rule is:

```lean
WeakMemory.WeakCAS.ProgressRule
  .systemResponseProgress_of_primitiveJustice
    (system : Interface Thread)
    (obligations : Obligations system)
    (justice : PrimitiveJustice system) :
    SystemResponseProgress system
```

The exact-assumption Treiber progress theorem is:

```lean
WeakMemory.TreiberC11V1.InfiniteRC11Execution
  .systemResponseProgress_of_fromReadFairness
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress
```

The conventional full-memory-fairness corollary is:

```lean
WeakMemory.TreiberC11V1.InfiniteRC11Execution
  .systemResponseProgress_of_fairness
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress
```

The safety/liveness composition is:

```lean
WeakMemory.TreiberC11V1.InfiniteRC11Execution
  .linearizableLongRun_of_fairness
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (recurring : execution.RecurringPushPopDemand)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees
```

An exact-assumption long-run variant,
`linearizableLongRun_of_fromReadFairness`, replaces `MemoryFair` by
`FromReadFair`. The displayed theorem above is retained because the paired
prefix-finite `mo`/`fr` condition is the standard declarative memory-fairness
interface used by the closest literature.

Here:

- `SystemResponseProgress` means that from every state containing an active
  operation, some method response occurs at a later or equal source position.
  This is system-wide lock-freedom, not wait-freedom and not per-operation
  starvation-freedom.
- `LinearizableLongRunGuarantees.lockFreedom.finitePrefixSafety` gives the
  complete finite `FullDeclarativeGuarantees` package at every prefix length.
  It does not select one projectively coherent linearization order for the
  whole infinite history.
- `RecurringPushPopDemand` says that a push or pop is pending at arbitrarily
  late states. A single permanently stuck call would satisfy this premise, so
  the premise does not assume the responses later derived by the theorem.

## 3. Non-vacuity and independence

`WeakMemory.TreiberC11V1.InfiniteWitness.execution` is a concrete one-thread
infinite execution. It repeatedly performs a fresh push with a relaxed load,
an immutable `next` write, a successful release weak CAS, and a response.
Lean proves all of the following for the same carrier:

```lean
execution.source.WeakThreadFair
execution.MemoryFair
execution.WeakCASJustice
execution.RecurringPushPopDemand
execution.LinearizableLongRunGuarantees
```

This witness establishes joint satisfiability of the positive theorem's
assumptions. Its justice proof is valid but success-rich: every suffix already
contains a successful CAS, so the bad no-success suffix premise is impossible.
The distinct all-spurious execution is what establishes that scheduler and
memory fairness do not by themselves imply primitive justice or progress.

`WeakMemory.TreiberC11V1.InfiniteSpurious.execution` is the matching integrated
negative witness. One thread invokes a push, performs its initial relaxed load
and immutable `next` write, and then alternates forever between an
equal-observation failed weak CAS and rewriting the same `next`. Every raw
source prefix, including mid-retry prefixes, is a full `DeclarativeExecution`;
all reads use the initializer, and global/finite modification order is empty.
Lean proves on this same carrier:

```lean
execution.source.WeakThreadFair
execution.MemoryFair
execution.RecurringPushPopDemand
¬ execution.WeakCASJustice
¬ execution.SystemResponseProgress
¬ execution.InfinitelyManyResponses
```

Thus the positive assumptions are jointly satisfiable when justice is
included, while removing justice admits a coherent, fair, genuinely
all-spurious Treiber/RC11 execution with a forever-pending push.

## 4. Second generic client

`WeakMemory/WeakCASCounter.lean` supplies a Treiber-independent client of
`WeakCAS.ProgressRule`. It models a one-location increment operation with
invocation, mismatch refresh, spurious failure, and successful increment
steps. Its central application is:

```lean
WeakMemory.WeakCASCounter.responseProgress_of_primitiveJustice
    (run : Run)
    (justice : PrimitiveJustice (interface run)) :
    SystemResponseProgress (interface run)
```

The file derives the generic algorithmic obligations from the counter
transition semantics, constructs a success-rich satisfying run, and constructs
an all-spurious run on which the obligations hold while primitive justice and
response progress fail.

This is evidence that the logical rule is not tied to Treiber definitions. It
is deliberately only a minimal second client: it has one thread, no RC11
graph, mandatory trace scheduling, and fuses successful CAS with method
response. It must not be presented as a second RC11 case study or a realistic
end-to-end counter library.

`ProgressRule.Interface` is system-wide and has no site index. Its justice
conclusion is some primitive success, which is exactly enough for the present
single-site lock-freedom clients. It is not yet a reusable per-site theorem
for algorithms with several independent CAS locations.

## 5. Where each assumption is used

| Assumption | Formal role |
|---|---|
| Coherent `InfiniteRC11Execution` | Ties one source run to global RF/MO data and restricts both exactly to every finite declarative prefix. |
| Finite-prefix `RC11.Valid` | Supplies RC11 consistency and the existing finite safety/linearizability path. |
| Client contract/order acyclicity | Supplies lifetime, payload, immutable-field, operation-identity, and real-time compatibility needed by the finite Herlihy--Wing bridge. |
| Weak thread fairness | Forces continuously active source threads through bounded local control work, retry boundaries, and post-commit responses. |
| Prefix-finite `fr` | Prevents a selected infinite retry subsequence from observing writes strictly before one fixed stable MO tail forever. |
| Prefix-finite `mo` | Is part of the adopted declarative memory-fairness contract; the current stable-tail proof consumes its `fr` component directly. |
| Weak-CAS justice | Excludes a suffix with no successful head modification and arbitrarily late compare-equal attempts by one thread. |
| Recurring push/pop demand | Converts one-step system response progress into responses at arbitrarily late positions. |

The fact that the present proof consumes `memoryFair.2` (`fr`
prefix-finiteness) rather than `memoryFair.1` should be stated openly. The
theorem accepts the standard paired `mo`/`fr` memory-fairness condition, but
this Treiber argument has not established that both components are minimal.

## 6. Semantic and implementation boundary

The theorem covers the hand-defined and versioned `TreiberC11V1` source and
declarative semantics. The C implementation is hash-pinned and checked
against an extracted Clang 18 AST descriptor, but there is no verified
compiler or proved refinement from full ISO C semantics to `TreiberC11V1`.

The trusted or assumed boundary includes:

- Lean's kernel and the imported Lean/Mathlib foundations;
- the model definitions and theorem statements themselves;
- the Clang AST extractor and its interpretation when making claims about
  `c/treiber.c`;
- the explicit thread, memory, weak-CAS, and client assumptions listed above;
  and
- the decision to model only the non-SC RC11 fragment used by this algorithm.

`#print axioms` reports only the standard Lean axioms used by the imported
development:

```text
propext
Classical.choice
Quot.sound
```

The main proof contains no project-specific axiom, `sorry`, or `admit`.

## 7. Excluded claims

The result does not establish:

- full ISO C11/C17/C2Y semantics or compilation correctness;
- portable lock-freedom without an implementation-level primitive progress
  contract;
- wait-freedom or starvation-freedom for each invocation;
- one coherent linearization of an infinite history;
- memory reclamation, `free`, address reuse, hazard pointers, or ABA safety;
- minimality or weakest-possible status of the justice condition;
- a site-indexed primitive-justice rule for multi-location algorithms;
- necessity of both `mo` and `fr` prefix-finiteness for this proof;
- a first general fairness framework, a first weak-memory liveness theory, a
  first Treiber safety proof, or a first language capable of expressing
  weak-CAS fairness; or
- publication priority merely from a negative literature search.

## 8. Reproducibility gate

A release candidate must pass:

```bash
./verify.sh
```

That command checks the pinned source descriptor, native sequential and stress
tests, all Lean targets and the demo, and bounded GenMC/Relinche harnesses.
The same commit must also be built from a clean clone on the MSI host using
the pinned Lean toolchain.

Before submission:

1. run `git diff --check`;
2. scan all result modules for `sorry`, `admit`, project axioms, and unsafe
   declarations;
3. record `#print axioms` for the negative theorem, reusable rule, Treiber
   theorem, and concrete witness application;
4. archive exact Lean, Clang, GenMC, and Relinche versions;
5. repeat the primary-source literature search;
6. obtain an external concurrency/formal-methods review of the definitions,
   not merely successful compilation; and
7. use the exact commit hash in every artifact and paper reference.

## 9. Claim wording

Preferred wording before external review:

> We give a machine-checked closure, for an explicit reclamation-free RC11
> Treiber model, of the weak-RMW fairness issue isolated by Lahav et al. The
> result separates primitive weak-CAS justice from scheduler and memory
> fairness inside one coherent Treiber/RC11 carrier, gives a full
> all-spurious independence execution, and proves that weak thread fairness,
> prefix-finite `fr`, and primitive justice compose with RC11-valid finite
> prefixes to derive system-wide response progress.

The date-bounded “first exact combination found” wording in
`open-problem-audit.md` remains a literature-search report, not a theorem and
not proof of priority.
