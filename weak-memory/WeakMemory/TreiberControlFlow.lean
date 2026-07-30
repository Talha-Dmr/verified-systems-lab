import WeakMemory.TreiberGeneration

namespace WeakMemory.TreiberRC11.ControlFlow

/-!
# Per-thread Treiber control flow

This module models the invocation and retry control flow visible in
`c/treiber.c`. It deliberately does not construct program-order, reads-from,
modification-order, or extended-coherence edges.

Every invocation receives an operation identifier that remains attached to
its local state and emitted labels. Initial head loads are explicit atomic
actions: push uses a relaxed load, while pop and `isEmpty` use acquire loads.
An initially empty pop completes at its `popLoad none` event.

A failed weak compare-exchange always updates the local expected value to the
observed actual value. Equal values are permitted, representing spurious
failure. If a failed pop compare-exchange observes `none`, the source function
returns immediately; it does not execute another load or emit a later
`popEmpty` action.
-/

/-- Identity of one source-level push, pop, or `isEmpty` invocation. -/
abbrev OperationId := Nat

/--
The local state of one thread.

`reserved` is the node retained by one in-progress push invocation. This is a
local reservation only; uniqueness across threads remains an allocator-table
obligation in `TreiberGeneration`.

The loading states separate source invocation from the initial atomic load.
An active pop stores a non-null pointer because an empty load, or a failed CAS
that observes null, completes the invocation immediately.
-/
inductive LocalState (α : Type) where
  | idle
  | pushLoading
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
  | pushing
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected : Option TreiberRA.NodeId)
  | popLoading
      (operation : OperationId)
  | popping
      (operation : OperationId)
      (expected : TreiberRA.NodeId)
  | checkingEmpty
      (operation : OperationId)
  deriving Repr, DecidableEq

/--
Observable labels of the local control-flow machine.

Invocation labels preserve source-level operation identity. Atomic labels
retain that identity while carrying exactly the existing operational action,
including the source function's initial head load.
-/
inductive Label (α : Type) where
  | invokePush
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
  | invokePop
      (operation : OperationId)
  | invokeIsEmpty
      (operation : OperationId)
  | atomic
      (operation : OperationId)
      (action : TreiberRA.Action α)
  deriving Repr, DecidableEq

namespace Label

/-- The invocation owning a control-flow label. -/
def operation : Label α → OperationId
  | .invokePush operation .. => operation
  | .invokePop operation => operation
  | .invokeIsEmpty operation => operation
  | .atomic operation _ => operation

/-- Project an atomic label to its operational action. -/
def action? : Label α → Option (TreiberRA.Action α)
  | .invokePush .. => none
  | .invokePop .. => none
  | .invokeIsEmpty .. => none
  | .atomic _ action => some action

end Label

/-- Erase invocation labels and operation identifiers from a local trace. -/
def projectedActions : List (Label α) → List (TreiberRA.Action α)
  | [] => []
  | label :: rest =>
      match label.action? with
      | none => projectedActions rest
      | some action => action :: projectedActions rest

/--
One source-shaped local transition for a fixed thread.

Heap validity, successful-CAS enablement, allocator provenance, and graph
relations are intentionally checked by later layers.
-/
inductive LocalStep (thread : Nat) :
    LocalState α →
    Label α →
    LocalState α →
    Prop where
  | beginPush
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α) :
      LocalStep thread
        .idle
        (.invokePush operation reserved value)
        (.pushLoading operation reserved value)
  | pushLoad
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (observed : Option TreiberRA.NodeId) :
      LocalStep thread
        (.pushLoading operation reserved value)
        (.atomic operation (.pushLoad thread observed))
        (.pushing operation reserved value observed)
  | beginPop
      (operation : OperationId) :
      LocalStep thread
        .idle
        (.invokePop operation)
        (.popLoading operation)
  | popLoadEmpty
      (operation : OperationId) :
      LocalStep thread
        (.popLoading operation)
        (.atomic operation (.popLoad thread none))
        .idle
  | popLoadNonempty
      (operation : OperationId)
      (observed : TreiberRA.NodeId) :
      LocalStep thread
        (.popLoading operation)
        (.atomic operation (.popLoad thread (some observed)))
        (.popping operation observed)
  | beginIsEmpty
      (operation : OperationId) :
      LocalStep thread
        .idle
        (.invokeIsEmpty operation)
        (.checkingEmpty operation)
  | isEmptyLoad
      (operation : OperationId)
      (observed : Option TreiberRA.NodeId) :
      LocalStep thread
        (.checkingEmpty operation)
        (.atomic operation (.isEmptyLoad thread observed))
        .idle
  | pushFailure
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected actual : Option TreiberRA.NodeId) :
      LocalStep thread
        (.pushing operation reserved value expected)
        (.atomic operation
          (.pushFailure thread reserved value expected actual))
        (.pushing operation reserved value actual)
  | pushSuccess
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected : Option TreiberRA.NodeId) :
      LocalStep thread
        (.pushing operation reserved value expected)
        (.atomic operation
          (.pushSuccess thread reserved value expected))
        .idle
  | popFailureRetry
      (operation : OperationId)
      (expected actual : TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected)
        (.atomic operation
          (.popFailure thread (some expected) (some actual)))
        (.popping operation actual)
  | popFailureEmpty
      (operation : OperationId)
      (expected : TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected)
        (.atomic operation
          (.popFailure thread (some expected) none))
        .idle
  | popSuccess
      (operation : OperationId)
      (expected : TreiberRA.NodeId)
      (value : α)
      (next : Option TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected)
        (.atomic operation
          (.popSuccess thread expected value next))
        .idle

/-- Extract the owning thread from an operational Treiber action. -/
def actionThread : TreiberRA.Action α → Nat
  | .pushLoad thread .. => thread
  | .popLoad thread .. => thread
  | .isEmptyLoad thread .. => thread
  | .pushSuccess thread .. => thread
  | .pushFailure thread .. => thread
  | .popSuccess thread .. => thread
  | .popFailure thread .. => thread
  | .popEmpty thread => thread

/-- Every atomic label emitted by a local step belongs to its fixed thread. -/
theorem LocalStep.atomicActionThread_eq
    {thread : Nat}
    {before after : LocalState α}
    {operation : OperationId}
    {action : TreiberRA.Action α}
    (step :
      LocalStep thread before (.atomic operation action) after) :
    actionThread action = thread := by
  cases step <;> rfl

/-- Idle threads can only begin one of the three public operations. -/
theorem LocalStep.fromIdle
    {thread : Nat}
    {label : Label α}
    {after : LocalState α}
    (step : LocalStep thread .idle label after) :
    (∃ operation reserved value,
      label = .invokePush operation reserved value ∧
        after = .pushLoading operation reserved value) ∨
    (∃ operation,
      label = .invokePop operation ∧
        after = .popLoading operation) ∨
    ∃ operation,
      label = .invokeIsEmpty operation ∧
        after = .checkingEmpty operation := by
  cases step with
  | beginPush =>
      exact Or.inl ⟨_, _, _, rfl, rfl⟩
  | beginPop =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | beginIsEmpty =>
      exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)

/-- A pending push performs exactly its source-level relaxed head load. -/
theorem LocalStep.fromPushLoading
    {thread : Nat}
    {operation : OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.pushLoading operation reserved value)
        label
        after) :
    ∃ observed,
      label = .atomic operation (.pushLoad thread observed) ∧
        after = .pushing operation reserved value observed := by
  cases step with
  | pushLoad =>
      exact ⟨_, rfl, rfl⟩

/--
A pending pop performs exactly its acquire head load. Null completes the
operation; a non-null pointer enters the compare-exchange loop.
-/
theorem LocalStep.fromPopLoading
    {thread : Nat}
    {operation : OperationId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.popLoading operation)
        label
        after) :
    (label = .atomic operation (.popLoad thread none) ∧
      after = .idle) ∨
    ∃ observed,
      label = .atomic operation (.popLoad thread (some observed)) ∧
        after = .popping operation observed := by
  cases step with
  | popLoadEmpty =>
      exact Or.inl ⟨rfl, rfl⟩
  | popLoadNonempty =>
      exact Or.inr ⟨_, rfl, rfl⟩

/-- An `isEmpty` invocation completes at its acquire head load. -/
theorem LocalStep.fromCheckingEmpty
    {thread : Nat}
    {operation : OperationId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.checkingEmpty operation)
        label
        after) :
    ∃ observed,
      label = .atomic operation (.isEmptyLoad thread observed) ∧
        after = .idle := by
  cases step with
  | isEmptyLoad =>
      exact ⟨_, rfl, rfl⟩

/--
A push retry preserves its operation, reserved node, and value and replaces
only the expected head. A successful push completes the invocation.
-/
theorem LocalStep.fromPushing
    {thread : Nat}
    {operation : OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.pushing operation reserved value expected)
        label
        after) :
    (label =
        .atomic operation
          (.pushSuccess thread reserved value expected) ∧
      after = .idle) ∨
    ∃ actual,
      label =
          .atomic operation
            (.pushFailure
              thread reserved value expected actual) ∧
        after =
          .pushing operation reserved value actual := by
  cases step with
  | pushFailure =>
      exact Or.inr ⟨_, rfl, rfl⟩
  | pushSuccess =>
      exact Or.inl ⟨rfl, rfl⟩

/--
An active nonempty pop either succeeds, retries with an observed non-null
pointer, or completes empty when its failed compare-exchange observes null.
-/
theorem LocalStep.fromNonemptyPop
    {thread : Nat}
    {operation : OperationId}
    {expected : TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.popping operation expected)
        label
        after) :
    (∃ value next,
      label =
          .atomic operation
            (.popSuccess thread expected value next) ∧
        after = .idle) ∨
    (∃ actual,
      label =
        .atomic operation
            (.popFailure
              thread (some expected) (some actual)) ∧
        after = .popping operation actual) ∨
    (label =
        .atomic operation
          (.popFailure thread (some expected) none) ∧
      after = .idle) := by
  cases step with
  | popFailureRetry =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | popFailureEmpty =>
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | popSuccess =>
      exact Or.inl ⟨_, _, rfl, rfl⟩

/-- A weak push compare-exchange may fail spuriously without changing expected. -/
theorem pushSpuriousFailure
    (thread : Nat)
    (operation : OperationId)
    (reserved : TreiberRA.NodeId)
    (value : α)
    (expected : Option TreiberRA.NodeId) :
    LocalStep thread
      (.pushing operation reserved value expected)
      (.atomic operation
        (.pushFailure
          thread reserved value expected expected))
      (.pushing operation reserved value expected) :=
  .pushFailure operation reserved value expected expected

/-- A weak pop compare-exchange may fail spuriously and retry the same node. -/
theorem popSpuriousFailure
    (thread : Nat)
    (operation : OperationId)
    (expected : TreiberRA.NodeId) :
    LocalStep thread
      (.popping operation expected : LocalState α)
      (.atomic operation
        (.popFailure
          thread (some expected) (some expected)))
      (.popping operation expected) :=
  .popFailureRetry operation expected expected

/--
A pop CAS failure that observes null completes immediately and emits only that
failed CAS observation.
-/
theorem failedPopObservingEmpty_completes
    (thread : Nat)
    (operation : OperationId)
    (expected : TreiberRA.NodeId) :
    LocalStep thread
      (.popping operation expected : LocalState α)
      (.atomic operation
        (.popFailure thread (some expected) none))
      .idle :=
  .popFailureEmpty operation expected

/-- The completing failed-pop action linearizes as an empty pop. -/
theorem failedPopObservingEmpty_commitsPopEmpty
    (thread expected : Nat) :
    TreiberRA.Action.commit?
      (.popFailure thread (some expected) none :
        TreiberRA.Action α) =
      some .popEmpty :=
  rfl

/-- An initially null pop load is itself the empty-pop commit. -/
theorem emptyPopLoad_commitsPopEmpty
    (thread : Nat) :
    TreiberRA.Action.commit?
      (.popLoad thread none : TreiberRA.Action α) =
      some .popEmpty :=
  rfl

/--
A finite local execution retaining invocation and operation identity.

Executions may end in a non-idle state, representing a finite prefix with a
pending invocation.
-/
inductive Execution (thread : Nat) :
    LocalState α →
    List (Label α) →
    LocalState α →
    Prop where
  | nil (state : LocalState α) :
      Execution thread state [] state
  | cons
      {initial middle final : LocalState α}
      (label : Label α)
      (rest : List (Label α))
      (first : LocalStep thread initial label middle)
      (later : Execution thread middle rest final) :
      Execution thread initial (label :: rest) final

/-- Every atomic label in a local execution is tagged with its thread. -/
theorem Execution.atomicLabelsHaveThread
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)}
    (execution : Execution thread initial labels final) :
    ∀ operation action,
      Label.atomic operation action ∈ labels →
      actionThread action = thread := by
  induction execution with
  | nil state =>
      intro operation action member
      simp at member
  | cons label rest first later inductionHypothesis =>
      intro operation action member
      simp only [List.mem_cons] at member
      rcases member with isFirst | inRest
      · subst label
        exact first.atomicActionThread_eq
      · exact inductionHypothesis operation action inRest

/-- Every projected action comes from an atomic label in the original trace. -/
theorem exists_atomic_of_mem_projectedActions
    {labels : List (Label α)}
    {action : TreiberRA.Action α}
    (member : action ∈ projectedActions labels) :
    ∃ operation,
      Label.atomic operation action ∈ labels := by
  induction labels with
  | nil =>
      simp [projectedActions] at member
  | cons label rest inductionHypothesis =>
      cases label with
      | invokePush operation reserved value =>
          obtain ⟨owner, ownerMember⟩ :=
            inductionHypothesis (by
              simpa [projectedActions, Label.action?] using member)
          exact ⟨owner, by simp [ownerMember]⟩
      | invokePop operation =>
          obtain ⟨owner, ownerMember⟩ :=
            inductionHypothesis (by
              simpa [projectedActions, Label.action?] using member)
          exact ⟨owner, by simp [ownerMember]⟩
      | invokeIsEmpty operation =>
          obtain ⟨owner, ownerMember⟩ :=
            inductionHypothesis (by
              simpa [projectedActions, Label.action?] using member)
          exact ⟨owner, by simp [ownerMember]⟩
      | atomic operation first =>
          simp only [projectedActions, Label.action?,
            List.mem_cons] at member
          rcases member with isFirst | inRest
          · subst action
            exact ⟨operation, by simp⟩
          · obtain ⟨owner, ownerMember⟩ :=
              inductionHypothesis inRest
            exact ⟨owner, by simp [ownerMember]⟩

/-- Every action projected from a local execution belongs to its fixed thread. -/
theorem Execution.projectedActionsHaveThread
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)}
    (execution : Execution thread initial labels final) :
    ∀ action,
      action ∈ projectedActions labels →
      actionThread action = thread := by
  intro action member
  obtain ⟨operation, atomicMember⟩ :=
    exists_atomic_of_mem_projectedActions member
  exact execution.atomicLabelsHaveThread
    operation action atomicMember

/-!
This layer proves only source-control-flow shape. It does not show that an
observation is permitted by RC11, that a successful CAS is enabled, or that a
pop payload matches an allocated node. Those remain obligations of the graph,
typing, and replay layers.
-/

end WeakMemory.TreiberRC11.ControlFlow
