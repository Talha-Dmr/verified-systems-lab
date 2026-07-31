import WeakMemory

namespace WeakMemory

/-!
# Sequential specification and abstract commits for Michael--Scott queue

This file starts the realistic multi-location client without importing the
site-progress rule or any RC11 validation layer.  It fixes the FIFO sequential
specification, logical atomic sites, and abstract linearization commits that
later source and execution-graph developments must refine.
-/

namespace QueueSpec

inductive Operation (Value : Type) where
  | enqueue (value : Value)
  | dequeue
  deriving Repr, DecidableEq

inductive Response (Value : Type) where
  | enqueued
  | dequeued (value : Option Value)
  deriving Repr, DecidableEq

structure CompletedOperation (Value : Type) where
  operation : Operation Value
  response : Response Value
  deriving Repr, DecidableEq

/-- A list stores FIFO contents from the oldest to the newest value. -/
def step :
    List Value → Operation Value →
      Response Value × List Value
  | queue, .enqueue value =>
      (.enqueued, queue ++ [value])
  | [], .dequeue =>
      (.dequeued none, [])
  | value :: rest, .dequeue =>
      (.dequeued (some value), rest)

/-- A completed history is legal when it follows the FIFO state machine. -/
inductive Legal :
    List Value →
      List (CompletedOperation Value) →
      List Value → Prop where
  | nil (queue : List Value) :
      Legal queue [] queue
  | cons
      {before middle after : List Value}
      (entry : CompletedOperation Value)
      (rest : List (CompletedOperation Value))
      (headStep :
        step before entry.operation =
          (entry.response, middle))
      (tailLegal : Legal middle rest after) :
      Legal before (entry :: rest) after

end QueueSpec

namespace MSQueue

/-- Allocation identity; the first model never reuses an identifier. -/
abbrev NodeId := Nat

/--
Logical atomic sites of Michael--Scott queue.  `next node` is generation-aware
because `NodeId` is unique in the reclamation-free model.
-/
inductive Site where
  | head
  | tail
  | next (node : NodeId)
  deriving Repr, DecidableEq

/--
Abstract linearization commits.  Tail-helping CAS events are deliberately
absent because they are abstract stuttering steps.
-/
inductive Commit (Value : Type) where
  | enqueue (value : Value)
  | dequeueValue (value : Value)
  | dequeueEmpty
  deriving Repr, DecidableEq

namespace Commit

def completed :
    Commit Value → QueueSpec.CompletedOperation Value
  | .enqueue value =>
      { operation := .enqueue value
        response := .enqueued }
  | .dequeueValue value =>
      { operation := .dequeue
        response := .dequeued (some value) }
  | .dequeueEmpty =>
      { operation := .dequeue
        response := .dequeued none }

end Commit

/-- Each abstract commit performs exactly one FIFO specification step. -/
inductive CommitStep :
    List Value → Commit Value → List Value → Prop where
  | enqueue (queue : List Value) (value : Value) :
      CommitStep queue (.enqueue value) (queue ++ [value])
  | dequeueValue (value : Value) (rest : List Value) :
      CommitStep (value :: rest) (.dequeueValue value) rest
  | dequeueEmpty :
      CommitStep ([] : List Value) .dequeueEmpty []

theorem commitStep_matchesSpec
    {before after : List Value}
    {commit : Commit Value}
    (step : CommitStep before commit after) :
    QueueSpec.step before commit.completed.operation =
      (commit.completed.response, after) := by
  cases step <;> rfl

/-- A chronological sequence of queue linearization commits. -/
inductive CommitTrace :
    List Value → List (Commit Value) → List Value → Prop where
  | nil (queue : List Value) :
      CommitTrace queue [] queue
  | cons
      {before middle after : List Value}
      (commit : Commit Value)
      (rest : List (Commit Value))
      (headStep : CommitStep before commit middle)
      (tailTrace : CommitTrace middle rest after) :
      CommitTrace before (commit :: rest) after

def completedHistory
    (commits : List (Commit Value)) :
    List (QueueSpec.CompletedOperation Value) :=
  commits.map Commit.completed

/--
The base linearizability lemma: every abstract commit trace is a legal FIFO
history.  Later operational and RC11 layers only need to extract this trace
and preserve operation identity and real time.
-/
theorem commitTrace_linearizable
    {initial final : List Value}
    {commits : List (Commit Value)}
    (trace : CommitTrace initial commits final) :
    QueueSpec.Legal initial (completedHistory commits) final := by
  induction trace with
  | nil queue =>
      exact QueueSpec.Legal.nil queue
  | cons commit rest headStep tailTrace inductionHypothesis =>
      exact
        QueueSpec.Legal.cons
          commit.completed
          (completedHistory rest)
          (commitStep_matchesSpec headStep)
          inductionHypothesis

namespace Example

def commits : List (Commit Nat) :=
  [.enqueue 10, .enqueue 20,
    .dequeueValue 10, .dequeueValue 20,
    .dequeueEmpty]

theorem trace : CommitTrace [] commits [] := by
  exact
    CommitTrace.cons (.enqueue 10) _
      (CommitStep.enqueue [] 10)
      (CommitTrace.cons (.enqueue 20) _
        (CommitStep.enqueue [10] 20)
        (CommitTrace.cons (.dequeueValue 10) _
          (CommitStep.dequeueValue 10 [20])
          (CommitTrace.cons (.dequeueValue 20) _
            (CommitStep.dequeueValue 20 [])
            (CommitTrace.cons .dequeueEmpty []
              CommitStep.dequeueEmpty
              (CommitTrace.nil [])))))

theorem legal :
    QueueSpec.Legal [] (completedHistory commits) [] :=
  commitTrace_linearizable trace

end Example

end MSQueue

end WeakMemory
