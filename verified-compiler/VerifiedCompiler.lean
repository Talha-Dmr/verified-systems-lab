namespace VerifiedCompiler

/-!
# A verified compiler for a tiny expression language

The source language contains integer literals and three binary operations.
It is interpreted directly by `Expr.eval` and compiled to a stack machine by
`Compiler.compile`.

The main result, `Compiler.correct`, states that running compiled code on any
initial stack always succeeds and leaves the interpreted value on top.
-/

inductive Expr where
  | lit : Int → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, DecidableEq

namespace Expr

/-- Direct interpreter for source expressions. -/
def eval : Expr → Int
  | .lit value => value
  | .add left right => eval left + eval right
  | .sub left right => eval left - eval right
  | .mul left right => eval left * eval right

end Expr

abbrev Stack := List Int

inductive Instr where
  | push : Int → Instr
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

abbrev Code := List Instr

namespace Machine

/--
Execute one instruction.

Binary instructions consume the right operand first and the left operand
second because the compiler pushes the left value before the right value.
-/
def step : Instr → Stack → Option Stack
  | .push value, stack => some (value :: stack)
  | .add, right :: left :: stack => some ((left + right) :: stack)
  | .sub, right :: left :: stack => some ((left - right) :: stack)
  | .mul, right :: left :: stack => some ((left * right) :: stack)
  | _, _ => none

/-- Execute a sequence of stack-machine instructions. -/
def run : Code → Stack → Option Stack
  | [], stack => some stack
  | instruction :: code, stack =>
      match step instruction stack with
      | none => none
      | some nextStack => run code nextStack

/--
Sequentially running `firstCode ++ suffix` is the same as running `firstCode`
first and then continuing with `suffix`.
-/
theorem run_append (firstCode suffix : Code) (stack : Stack) :
    run (firstCode ++ suffix) stack =
      match run firstCode stack with
      | none => none
      | some nextStack => run suffix nextStack := by
  induction firstCode generalizing stack with
  | nil =>
      rfl
  | cons instruction firstCode inductionHypothesis =>
      simp only [List.cons_append, run]
      cases step instruction stack <;> simp [inductionHypothesis]

end Machine

namespace Compiler

/-- Compile a source expression to stack-machine code. -/
def compile : Expr → Code
  | .lit value => [.push value]
  | .add left right => compile left ++ compile right ++ [.add]
  | .sub left right => compile left ++ compile right ++ [.sub]
  | .mul left right => compile left ++ compile right ++ [.mul]

/--
Strengthened compiler-correctness theorem.

Compiled code may start on an arbitrary stack and may be followed by arbitrary
continuation code. It behaves exactly like pushing the interpreted source
value and then running that continuation.
-/
theorem correct_continuation (expression : Expr) (continuation : Code)
    (stack : Stack) :
    Machine.run (compile expression ++ continuation) stack =
      Machine.run continuation (expression.eval :: stack) := by
  induction expression generalizing continuation stack with
  | lit value =>
      rfl
  | add left right leftHypothesis rightHypothesis =>
      simp [compile, Expr.eval, List.append_assoc, leftHypothesis,
        rightHypothesis, Machine.run, Machine.step]
  | sub left right leftHypothesis rightHypothesis =>
      simp [compile, Expr.eval, List.append_assoc, leftHypothesis,
        rightHypothesis, Machine.run, Machine.step]
  | mul left right leftHypothesis rightHypothesis =>
      simp [compile, Expr.eval, List.append_assoc, leftHypothesis,
        rightHypothesis, Machine.run, Machine.step]

/--
Running compiled code never underflows and pushes the source expression's
interpreted value on top of any initial stack.
-/
theorem correct_on_stack (expression : Expr) (stack : Stack) :
    Machine.run (compile expression) stack =
      some (expression.eval :: stack) := by
  simpa [Machine.run] using correct_continuation expression [] stack

/-- End-to-end compiler correctness from an empty initial stack. -/
theorem correct (expression : Expr) :
    Machine.run (compile expression) [] = some [expression.eval] := by
  simpa using correct_on_stack expression []

end Compiler

end VerifiedCompiler
