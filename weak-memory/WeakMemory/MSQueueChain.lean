import WeakMemory.MSQueueSpec

namespace WeakMemory.MSQueue.Chain

/-!
# Finite Michael--Scott chain invariant

This is the memory-model-independent safety kernel used by the later RC11
replay.  `nodes` is the permanent linked chain beginning with the dummy;
`payloads[i]` belongs to `nodes[i + 1]`.  Head and Tail are indices into that
chain.  Tail may lag the last node by at most one position.
-/

structure State (Value : Type) where
  nodes : List NodeId
  payloads : List Value
  head : Nat
  tail : Nat
  deriving Repr, DecidableEq

namespace State

/-- FIFO contents are the payloads strictly after the Head node. -/
def contents (state : State Value) : List Value :=
  state.payloads.drop state.head

def initial (dummy : NodeId) : State Value where
  nodes := [dummy]
  payloads := []
  head := 0
  tail := 0

end State

structure WellFormed (state : State Value) : Prop where
  aligned : state.nodes.length = state.payloads.length + 1
  nodesNodup : state.nodes.Nodup
  headValid : state.head < state.nodes.length
  tailValid : state.tail < state.nodes.length
  headBeforeTail : state.head ≤ state.tail
  tailAtEnd : state.nodes.length ≤ state.tail + 2

/-- The first permanent node retains the selected dummy identity. -/
def Rooted (dummy : NodeId) (state : State Value) : Prop :=
  state.nodes.head? = some dummy

theorem initial_wellFormed (dummy : NodeId) :
    WellFormed (State.initial (Value := Value) dummy) := by
  exact {
    aligned := rfl
    nodesNodup := by simp [State.initial]
    headValid := by simp [State.initial]
    tailValid := by simp [State.initial]
    headBeforeTail := Nat.le_refl 0
    tailAtEnd := by simp [State.initial]
  }

theorem initial_rooted (dummy : NodeId) :
    Rooted dummy (State.initial (Value := Value) dummy) := by
  rfl

/-!
Only successful structural CAS effects and a validated empty point appear in
this replay relation.  Loads and failed CAS labels are checked by the RC11
frontend; they do not mutate the chain.
-/
inductive Step :
    State Value → Option (Commit Value) → State Value → Prop where
  | link
      (before : State Value)
      (node : NodeId)
      (value : Value)
      (fresh : node ∉ before.nodes)
      (tailWasLast : before.tail + 1 = before.nodes.length) :
      Step before (some (.enqueue value)) {
        before with
        nodes := before.nodes ++ [node]
        payloads := before.payloads ++ [value]
      }
  | advanceTail
      (before : State Value)
      (hasNext : before.tail + 1 < before.nodes.length) :
      Step before none { before with tail := before.tail + 1 }
  | advanceHead
      (before : State Value)
      (value : Value)
      (headBeforeTail : before.head < before.tail)
      (payload : before.payloads[before.head]? = some value) :
      Step before (some (.dequeueValue value)) {
        before with head := before.head + 1
      }
  | empty
      (state : State Value)
      (headWasLast : state.head + 1 = state.nodes.length) :
      Step state (some .dequeueEmpty) state

namespace WellFormed

theorem headWithinPayloads
    {state : State Value}
    (wellFormed : WellFormed state)
    (headBeforeTail : state.head < state.tail) :
    state.head < state.payloads.length := by
  have aligned := wellFormed.aligned
  have tailValid := wellFormed.tailValid
  omega

theorem headAtLast_iff_contents_empty
    {state : State Value}
    (wellFormed : WellFormed state) :
    state.head + 1 = state.nodes.length ↔
      state.contents = [] := by
  rw [State.contents, List.drop_eq_nil_iff]
  have aligned := wellFormed.aligned
  have headValid := wellFormed.headValid
  omega

end WellFormed

/-- Every structural step preserves the fresh acyclic chain invariant. -/
theorem Step.preservesWellFormed
    {before after : State Value}
    {commit : Option (Commit Value)}
    (step : Step before commit after)
    (wellFormed : WellFormed before) :
    WellFormed after := by
  cases step with
  | link node value fresh tailWasLast =>
      refine {
        aligned := by simp [wellFormed.aligned]
        nodesNodup := by
          rw [List.nodup_append]
          refine ⟨wellFormed.nodesNodup, by simp, ?_⟩
          intro existing existingMember appended appendedMember
          simp at appendedMember
          subst appended
          intro same
          apply fresh
          rwa [← same]
        headValid := by
          simpa using Nat.lt_succ_of_lt wellFormed.headValid
        tailValid := by
          simpa using Nat.lt_succ_of_lt wellFormed.tailValid
        headBeforeTail := wellFormed.headBeforeTail
        tailAtEnd := by simp; omega
      }
  | advanceTail hasNext =>
      exact {
        aligned := wellFormed.aligned
        nodesNodup := wellFormed.nodesNodup
        headValid := wellFormed.headValid
        tailValid := by simpa using hasNext
        headBeforeTail := Nat.le_trans wellFormed.headBeforeTail
          (Nat.le_succ _)
        tailAtEnd := by
          change before.nodes.length ≤ (before.tail + 1) + 2
          have tailAtEnd := wellFormed.tailAtEnd
          omega
      }
  | advanceHead value headBeforeTail payload =>
      exact {
        aligned := wellFormed.aligned
        nodesNodup := wellFormed.nodesNodup
        headValid := Nat.lt_of_le_of_lt
          (Nat.succ_le_of_lt headBeforeTail)
          wellFormed.tailValid
        tailValid := wellFormed.tailValid
        headBeforeTail := Nat.succ_le_of_lt headBeforeTail
        tailAtEnd := wellFormed.tailAtEnd
      }
  | empty headWasLast => exact wellFormed

/-- Every committing structural step is exactly one FIFO specification step. -/
theorem Step.commitStep
    {before after : State Value}
    {commit : Commit Value}
    (step : Step before (some commit) after)
    (wellFormed : WellFormed before) :
    CommitStep before.contents commit after.contents := by
  cases step with
  | link node value fresh tailWasLast =>
      change CommitStep
        (before.payloads.drop before.head) (.enqueue value)
        ((before.payloads ++ [value]).drop before.head)
      have headWithin : before.head ≤ before.payloads.length := by
        have aligned := wellFormed.aligned
        have headValid := wellFormed.headValid
        omega
      rw [List.drop_append_of_le_length headWithin]
      exact CommitStep.enqueue _ _
  | advanceHead value headBeforeTail payload =>
      have headValid := wellFormed.headWithinPayloads headBeforeTail
      change CommitStep
        (before.payloads.drop before.head) (.dequeueValue value)
        (before.payloads.drop (before.head + 1))
      rw [List.drop_eq_getElem?_toList_append, payload]
      exact CommitStep.dequeueValue _ _
  | empty headWasLast =>
      have emptyContents : before.contents = [] :=
        (wellFormed.headAtLast_iff_contents_empty).mp headWasLast
      rw [emptyContents]
      exact CommitStep.dequeueEmpty

theorem Step.silent_contents
    {before after : State Value}
    (step : Step before none after) :
    before.contents = after.contents := by
  cases step
  rfl

theorem Step.preservesRooted
    {before after : State Value}
    {commit : Option (Commit Value)}
    (step : Step before commit after)
    {dummy : NodeId}
    (rooted : Rooted dummy before) :
    Rooted dummy after := by
  cases step with
  | link node value fresh tailWasLast =>
      cases nodesShape : before.nodes with
      | nil => simp [Rooted, nodesShape] at rooted
      | cons first rest => simpa [Rooted, nodesShape] using rooted
  | advanceTail => exact rooted
  | advanceHead => exact rooted
  | empty => exact rooted

/-- Finite structural replay with Tail-helping steps erased from commits. -/
inductive Replay :
    State Value → List (Commit Value) → State Value → Prop where
  | nil (state : State Value) :
      Replay state [] state
  | silent
      {before middle after : State Value}
      {commits : List (Commit Value)}
      (first : Step before none middle)
      (later : Replay middle commits after) :
      Replay before commits after
  | commit
      {before middle after : State Value}
      (commit : Commit Value)
      (commits : List (Commit Value))
      (first : Step before (some commit) middle)
      (later : Replay middle commits after) :
      Replay before (commit :: commits) after

theorem Replay.finalWellFormed
    {initial final : State Value}
    {commits : List (Commit Value)}
    (replay : Replay initial commits final)
    (wellFormed : WellFormed initial) :
    WellFormed final := by
  induction replay with
  | nil => exact wellFormed
  | silent first later inductionHypothesis =>
      exact inductionHypothesis (first.preservesWellFormed wellFormed)
  | commit commit commits first later inductionHypothesis =>
      exact inductionHypothesis (first.preservesWellFormed wellFormed)

theorem Replay.preservesRooted
    {initial final : State Value}
    {commits : List (Commit Value)}
    (replay : Replay initial commits final)
    {dummy : NodeId}
    (rooted : Rooted dummy initial) :
    Rooted dummy final := by
  induction replay with
  | nil => exact rooted
  | silent first later inductionHypothesis =>
      exact inductionHypothesis (first.preservesRooted rooted)
  | commit commit commits first later inductionHypothesis =>
      exact inductionHypothesis (first.preservesRooted rooted)

/-- The commit projection of every invariant-preserving replay is FIFO. -/
theorem Replay.commitTrace
    {initial final : State Value}
    {commits : List (Commit Value)}
    (replay : Replay initial commits final)
    (wellFormed : WellFormed initial) :
    CommitTrace initial.contents commits final.contents := by
  induction replay with
  | nil => exact CommitTrace.nil _
  | silent first later inductionHypothesis =>
      rw [first.silent_contents]
      exact inductionHypothesis (first.preservesWellFormed wellFormed)
  | commit commit commits first later inductionHypothesis =>
      exact CommitTrace.cons commit commits
        (first.commitStep wellFormed)
        (inductionHypothesis (first.preservesWellFormed wellFormed))

theorem Replay.linearizable
    {initial final : State Value}
    {commits : List (Commit Value)}
    (replay : Replay initial commits final)
    (wellFormed : WellFormed initial) :
    QueueSpec.Legal initial.contents
      (completedHistory commits) final.contents :=
  commitTrace_linearizable (replay.commitTrace wellFormed)

end WeakMemory.MSQueue.Chain
