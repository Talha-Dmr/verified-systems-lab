import WeakMemory.InfiniteExecution

namespace WeakMemory.Liveness

/-!
# Finite prefixes of infinite executions

This module connects the generic infinite-run vocabulary to ordinary finite
action lists.  It remains independent of Treiber's stack and of any particular
memory model.
-/

/-- A finite sequence of transitions labelled by an action list. -/
inductive FiniteRun
    {State Action : Type}
    (step : State → Action → State → Prop) :
    State → List Action → State → Prop where
  | nil (state : State) :
      FiniteRun step state [] state
  | cons
      {initial middle final : State}
      (action : Action)
      (rest : List Action)
      (first : step initial action middle)
      (later : FiniteRun step middle rest final) :
      FiniteRun step initial (action :: rest) final

namespace FiniteRun

/-- Concatenate two finite runs whose boundary states agree. -/
theorem append
    {State Action : Type}
    {step : State → Action → State → Prop}
    {initial middle final : State}
    {leading trailing : List Action}
    (first : FiniteRun step initial leading middle)
    (later : FiniteRun step middle trailing final) :
    FiniteRun step initial (leading ++ trailing) final := by
  induction first with
  | nil state =>
      simpa using later
  | cons action rest head tail inductionHypothesis =>
      simp only [List.cons_append]
      exact
        .cons action (rest ++ trailing) head
          (inductionHypothesis later)

/-- Extend a finite run by one final transition. -/
theorem snoc
    {State Action : Type}
    {step : State → Action → State → Prop}
    {initial middle final : State}
    {actions : List Action}
    {action : Action}
    (run : FiniteRun step initial actions middle)
    (last : step middle action final) :
    FiniteRun step initial (actions ++ [action]) final :=
  run.append
    (.cons action [] last (.nil final))

end FiniteRun

namespace InfiniteRun

/-- The first `length` actions of an infinite run, in execution order. -/
def actionPrefix
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (length : Nat) : List Action :=
  List.ofFn fun index : Fin length =>
    run.action index.val

@[simp] theorem actionPrefix_zero
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step) :
    run.actionPrefix 0 = [] := by
  simp [actionPrefix]

/-- The action prefix has exactly its requested length. -/
@[simp] theorem length_actionPrefix
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (length : Nat) :
    (run.actionPrefix length).length = length := by
  simp [actionPrefix]

/-- Indexing an action prefix returns the corresponding infinite-run action. -/
@[simp] theorem getElem_actionPrefix
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (length index : Nat)
    (inBounds : index < (run.actionPrefix length).length) :
    (run.actionPrefix length)[index] = run.action index := by
  simp [actionPrefix]

/-- Extending a prefix by one action appends the next run action. -/
theorem actionPrefix_succ
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (length : Nat) :
    run.actionPrefix (length + 1) =
      run.actionPrefix length ++ [run.action length] := by
  unfold actionPrefix
  rw [List.ofFn_succ_last]
  congr

/--
Every finite action prefix of an infinite run is a valid finite run from the
initial state to the state at the prefix boundary.
-/
theorem prefixValid
    {State Action : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (length : Nat) :
    FiniteRun step
      (run.state 0)
      (run.actionPrefix length)
      (run.state length) := by
  induction length with
  | zero =>
      simpa using
        (FiniteRun.nil (step := step) (run.state 0))
  | succ length inductionHypothesis =>
      rw [actionPrefix_succ]
      exact
        inductionHypothesis.snoc
          (run.valid length)

end InfiniteRun

end WeakMemory.Liveness
