# A Small Verified Compiler

This project is a small but end-to-end machine-checked example for
`68N20 — Theory of compilers and interpreters`.

The source language contains integer literals, addition, subtraction, and
multiplication. `Expr.eval` is the direct interpreter. `Compiler.compile`
translates an expression into stack-machine instructions, and `Machine.run`
executes those instructions.

## Proved Result

For every expression `e` and initial stack `s`,
`Compiler.correct_on_stack` proves:

```text
Machine.run (Compiler.compile e) s = some (Expr.eval e :: s)
```

Consequently:

- Compiled code never encounters stack underflow.
- The compiled program and direct interpreter produce the same value.
- The remainder of the initial stack is preserved unchanged.

The proof follows from the stronger `Compiler.correct_continuation` lemma,
which permits arbitrary machine code after the compiled expression.

## Verification

From the repository root:

```bash
./verified-compiler/verify.sh
```

The script builds the project with Lean 4.32.2 and runs the example program.

Example source expression:

```text
(2 + 3) * 4 - 7
```

The expected interpreter and machine result is `13`.

## Files

- `VerifiedCompiler.lean`: Language, interpreter, machine, compiler, and proofs.
- `Main.lean`: Executable example.
- `lakefile.lean`: Lean/Lake project definition.
- `lean-toolchain`: Pinned Lean version.
- `verify.sh`: Local build and execution script.
- `RESEARCH_ROADMAP.md`: Path from the toy compiler to research-level work.
