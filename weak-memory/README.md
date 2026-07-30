# 14G — Concurrent Algorithm Verification under Weak Memory

This project establishes the first verifiable foundation of the research route
using a Treiber stack without memory reclamation. The goal is not merely to
write a working stack, but to express the connection between its execution
model, sequential specification, and linearization points as explicit
theorems.

## Current Contents

- Treiber `push` and `pop` implemented with C11 atomics
- A native stress test using four threads and 80,000 distinct nodes
- Two small bounded C harnesses for GenMC
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
- `TreiberRC11.certifiedSchedule_linearizable`, composing a certified graph
  schedule with the operational RA proof

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
CAS attempts are stuttering steps that do not change shared state.

The remaining boundary is:

```text
full C11/RC11 execution graph
            ↓ not yet proved
operational RA Treiber execution
```

The current theorems establish the linearization-point core, not yet the full
Herlihy–Wing invocation/response definition. The stress test is not a proof,
and the project does not claim to verify the complete C11 semantics or the C
source directly.

The RC11-style layer now proves the following conditional path:

```text
well-formed graph + certified schedule
                  ↓
operational RA Treiber execution
                  ↓
legal sequential stack history
```

The remaining mathematical obligation is to construct that certified schedule
from graph well-formedness rather than receiving it as an assumption.

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

1. Builds the C code with warnings treated as errors.
2. Runs the sequential and multithreaded tests.
3. Builds the Lean project so the kernel checks all theorems.
4. Runs the bounded weak-memory harnesses when GenMC is available.

GenMC is optional. If its local binary is elsewhere:

```bash
GENMC_BIN=/absolute/path/to/genmc ./weak-memory/run_genmc.sh
```

## Next Precise Milestone

Extend the graph with the remaining RC11 coherence and release-sequence
conditions, then prove that every accepted finite graph admits a
`TreiberRC11.CertifiedSchedule`. Until that existence theorem is complete, the
project does not claim that the C Treiber stack is fully verified under RC11.
