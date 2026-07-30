# GenMC Validation Boundary

The GenMC runs in this repository are bounded validation evidence. They are
not the execution frontend of the Lean theorem and do not establish that every
C11 execution of `c/treiber.c` is accepted by
`RawTreiberModelExecution.validate?`.

## Checks Run by the Repository

`run_genmc.sh` uses the pinned local GenMC v0.17.0 build under `--rc11` for:

- the one-producer/one-consumer publication harness;
- the two-thread push-then-pop safety harness;
- a Relinche most-parallel client with one `push(101)` and one `pop()`.

The Relinche harness includes the exact `c/treiber.c` translation unit and
uses GenMC ghost method-boundary labels. Its specification admits precisely
the two legal outcomes: the pop returns empty before the push linearizes, or
it returns `101` after the push linearizes.

## Weak Compare-Exchange Limitation

Clang 18 preserves both source compare-exchanges as LLVM `cmpxchg weak`.
However, the pinned GenMC interpreter's
`Interpreter::visitAtomicCmpXchgInst` in
`lli/Runtime/Execution.cpp` does not inspect
`AtomicCmpXchgInst::isWeak()`.

In the v0.17.0 source used by this repository:

- the compare result is computed only as `read value == expected`;
- an equal-valued comparison always emits the CAS write half;
- no equal-valued spurious-failure branch is explored;
- the CAS read half receives `getSuccessOrdering()`;
- `getFailureOrdering()` is not used by that interpreter path.

Consequently, the current GenMC runs cover a strong-CAS-like subset and cannot
support a claim about all C11 executions of the source's weak
compare-exchanges. The Lean control-flow semantics independently includes
spurious failures, including failures where expected and observed values are
equal.

## Why Text Graph Output Is Not a Frontend

`--print-exec-graphs` exposes event identifiers, read-from sources, raw
values, and per-location coherence order in an ad-hoc human-readable format.
It is insufficient for a stable translator because normal completed graphs:

- omit method-begin arguments;
- omit source and variable metadata;
- omit reads-before edges and a stable global schedule;
- use raw pointer encodings without allocation provenance;
- have no versioned JSON or CSV schema;
- do not cover blocked finite prefixes unless separately requested.

Ordinary C logging is not a substitute. A load value does not identify its
reads-from write when several writes store the same pointer, and C provides no
operation for observing atomic modification order. Shared logging also adds
events and can change the execution set.

## Required Frontend Work

A bounded GenMC observation frontend would require a pinned machine-readable
exporter that records, for every complete or retained prefix graph:

- tool, model, option, source, and transformed-LLVM identities;
- typed events, program order, addresses, values, and memory orders;
- complete reads-from and modification order;
- successful and failed CAS structure, including weak and failure-order data;
- non-atomic `next` accesses;
- method invocation, response, and client-order information;
- stable allocation identities rather than raw pointer bits.

A deterministic Treiber-specific normalizer could then collapse each
successful GenMC CAS read/write pair into one Lean RMW event and produce the
four raw validator fields. Those artifacts would remain untrusted inputs to
the Lean validator.

Even that exporter would cover only the selected bounded GenMC semantics. A
general source theorem additionally needs:

- correct weak-CAS and failure-order exploration;
- finite-prefix coverage;
- a proof or explicit trust boundary from the pinned C/LLVM program to the
  exported graphs;
- a precise client lifetime, initialization, no-reuse, and real-time
  contract.
