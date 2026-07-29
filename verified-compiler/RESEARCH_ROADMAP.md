# Research Roadmap

The current project is the smallest complete core of a compiler-correctness
development. Each stage adds an executable definition first, then a
specification, and finally a Lean proof.

## 1. Completed Foundation

- Integer expression language
- Direct interpreter
- Fallible stack machine
- Expression compiler
- Semantic-preservation proof for arbitrary stacks and continuation code
- End-to-end correctness theorem from an empty stack

## 2. Variables and Environments

Add variables to the source language and a `load` instruction to the target
machine.

Main property to prove:

```text
run (compile e) stack env = some (eval e env :: stack)
```

This stage introduces contexts, environments, and variable resolution.

## 3. Constant-Folding Optimization

Add a transformation that evaluates subexpressions such as `2 + 3` before
compilation.

Two separate theorems are required:

```text
eval (foldConstants e) = eval e
run (compile (foldConstants e)) s = some (eval e :: s)
```

This stage separates optimization correctness from compiler correctness and
then composes them.

## 4. Statements, State, and Control Flow

Add assignment, sequencing, and conditionals. The target language gains jump
instructions and a program counter. Because programs may diverge, the semantics
must use execution traces or small-step transitions rather than only final
values.

Research-relevant topics:

- Termination and partial correctness
- Control-flow graphs
- Loop invariants
- Forward and backward simulation

## 5. Verified Optimization Passes

Model each optimization as an independent pass:

- Dead-code elimination
- Common-subexpression elimination
- Function inlining
- Loop transformations
- Register allocation

After proving every pass correct independently, obtain correctness of the
whole compiler pipeline by composition.

## 6. Research Frontier

When selecting one of the following directions, audit current primary
literature before formulating a precise problem that remains open:

- Correct compilation of concurrency under weak memory models
- Secure compilation and full abstraction
- Compilers that preserve side-channel properties
- Verification of JIT and self-modifying code
- Semantics-preserving compilation of probabilistic programs
- Proof-producing optimizations and verification-condition generation

This stage primarily intersects `68N20` with `68Q55`, `68Q60`, and `68V20`.
