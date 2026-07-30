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

A push writes `node->next` before every compare-exchange attempt. A nonempty
pop reads `observed->next` before every compare-exchange attempt. These
non-atomic field accesses are explicit source labels but are erased from the
single-location atomic-head graph.

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
The field-access states ensure that every compare-exchange is preceded by the
corresponding source-level `node->next` write or read. An active pop stores a
non-null pointer because an empty load, or a failed CAS that observes null,
completes the invocation immediately.
-/
inductive LocalState (α : Type) where
  | idle
  | pushLoading
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
  | pushWriting
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected : Option TreiberRA.NodeId)
  | pushing
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected : Option TreiberRA.NodeId)
  | popLoading
      (operation : OperationId)
  | popReading
      (operation : OperationId)
      (observed : TreiberRA.NodeId)
  | popping
      (operation : OperationId)
      (expected : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId)
  | checkingEmpty
      (operation : OperationId)
  deriving Repr, DecidableEq

/--
Observable labels of the local control-flow machine.

Invocation labels preserve source-level operation identity. Atomic labels
retain that identity while carrying exactly the existing operational action,
including the source function's initial head load. `writeNext` and `readNext`
retain the non-atomic node-field accesses needed for the publication proof.
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
  | writeNext
      (operation : OperationId)
      (node : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId)
  | readNext
      (operation : OperationId)
      (node : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId)
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
  | .writeNext operation .. => operation
  | .readNext operation .. => operation
  | .atomic operation _ => operation

/-- Project an atomic label to its operational action. -/
def action? : Label α → Option (TreiberRA.Action α)
  | .invokePush .. => none
  | .invokePop .. => none
  | .invokeIsEmpty .. => none
  | .writeNext .. => none
  | .readNext .. => none
  | .atomic _ action => some action

end Label

/-- Project a source trace to its atomic-head operational actions. -/
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
        (.pushWriting operation reserved value observed)
  | writeNext
      (operation : OperationId)
      (reserved : TreiberRA.NodeId)
      (value : α)
      (expected : Option TreiberRA.NodeId) :
      LocalStep thread
        (.pushWriting operation reserved value expected)
        (.writeNext operation reserved expected)
        (.pushing operation reserved value expected)
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
        (.popReading operation observed)
  | readNext
      (operation : OperationId)
      (observed : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId) :
      LocalStep thread
        (.popReading operation observed)
        (.readNext operation observed next)
        (.popping operation observed next)
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
        (.pushWriting operation reserved value actual)
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
      (expected actual : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected next)
        (.atomic operation
          (.popFailure thread (some expected) (some actual)))
        (.popReading operation actual)
  | popFailureEmpty
      (operation : OperationId)
      (expected : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected next)
        (.atomic operation
          (.popFailure thread (some expected) none))
        .idle
  | popSuccess
      (operation : OperationId)
      (expected : TreiberRA.NodeId)
      (value : α)
      (next : Option TreiberRA.NodeId) :
      LocalStep thread
        (.popping operation expected next)
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
        after = .pushWriting operation reserved value observed := by
  cases step with
  | pushLoad =>
      exact ⟨_, rfl, rfl⟩

/-- Every push attempt writes its desired node's `next` field before its CAS. -/
theorem LocalStep.fromPushWriting
    {thread : Nat}
    {operation : OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.pushWriting operation reserved value expected)
        label
        after) :
    label = .writeNext operation reserved expected ∧
      after = .pushing operation reserved value expected := by
  cases step
  exact ⟨rfl, rfl⟩

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
        after = .popReading operation observed := by
  cases step with
  | popLoadEmpty =>
      exact Or.inl ⟨rfl, rfl⟩
  | popLoadNonempty =>
      exact Or.inr ⟨_, rfl, rfl⟩

/-- Every non-null pop observation is followed by a matching `next` read. -/
theorem LocalStep.fromPopReading
    {thread : Nat}
    {operation : OperationId}
    {observed : TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.popReading operation observed)
        label
        after) :
    ∃ next,
      label = .readNext operation observed next ∧
        after = .popping operation observed next := by
  cases step with
  | readNext =>
      exact ⟨_, rfl, rfl⟩

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
          .pushWriting operation reserved value actual := by
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
    {next : Option TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.popping operation expected next)
        label
        after) :
    (∃ value,
      label =
          .atomic operation
            (.popSuccess thread expected value next) ∧
        after = .idle) ∨
    (∃ actual,
      label =
        .atomic operation
            (.popFailure
              thread (some expected) (some actual)) ∧
        after = .popReading operation actual) ∨
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
      exact Or.inl ⟨_, rfl, rfl⟩

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
      (.pushWriting operation reserved value expected) :=
  .pushFailure operation reserved value expected expected

/-- A weak pop compare-exchange may fail spuriously and retry the same node. -/
theorem popSpuriousFailure
    (thread : Nat)
    (operation : OperationId)
    (expected : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId) :
    LocalStep thread
      (.popping operation expected next : LocalState α)
      (.atomic operation
        (.popFailure
          thread (some expected) (some expected)))
      (.popReading operation expected) :=
  .popFailureRetry operation expected expected next

/--
A pop CAS failure that observes null completes immediately and emits only that
failed CAS observation.
-/
theorem failedPopObservingEmpty_completes
    (thread : Nat)
    (operation : OperationId)
    (expected : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId) :
    LocalStep thread
      (.popping operation expected next : LocalState α)
      (.atomic operation
        (.popFailure thread (some expected) none))
      .idle :=
  .popFailureEmpty operation expected next

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

/--
The acquire atomic observation that authorizes the following non-atomic
`node->next` read in one pop iteration.
-/
inductive AuthorizesReadNext
    (thread : Nat)
    (node : TreiberRA.NodeId) :
    TreiberRA.Action α → Prop where
  | popLoad :
      AuthorizesReadNext thread node
        (.popLoad thread (some node))
  | popFailure (expected : TreiberRA.NodeId) :
      AuthorizesReadNext thread node
        (.popFailure thread (some expected) (some node))

/--
At a selected `readNext` occurrence, either the execution prefix itself starts
in the matching read-ready state, or its immediately preceding label is the
acquire load/failed-CAS observation that supplied the non-null node.

The first alternative is useful for suffixes. For executions starting in
`idle`, it is impossible and every field read therefore has a concrete atomic
predecessor.
-/
theorem Execution.readNext_predecessor
    {thread : Nat}
    {initial final : LocalState α}
    {labels leading suffix : List (Label α)}
    {operation : OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (execution : Execution thread initial labels final)
    (shape :
      labels =
        leading ++ .readNext operation node next :: suffix) :
    (leading = [] ∧
      initial = .popReading operation node) ∨
    ∃ earlier action,
      leading = earlier ++ [.atomic operation action] ∧
        AuthorizesReadNext thread node action := by
  induction execution generalizing leading with
  | nil state =>
      simp at shape
  | @cons initial middle final label rest first later
      inductionHypothesis =>
      cases leading with
      | nil =>
          simp only [List.nil_append] at shape
          have labelShape :
              label = .readNext operation node next :=
            (List.cons.inj shape).1
          subst label
          cases first
          exact Or.inl ⟨rfl, rfl⟩
      | cons prefixHead prefixTail =>
          simp only [List.cons_append] at shape
          have labelsMatch := List.cons.inj shape
          have restShape :
              rest =
                prefixTail ++
                  .readNext operation node next :: suffix :=
            labelsMatch.2
          rcases inductionHypothesis restShape with startsReady | prior
          · rcases startsReady with
              ⟨prefixTailEmpty, middleReady⟩
            subst prefixTail
            subst middle
            have labelShape : label = prefixHead :=
              labelsMatch.1
            subst prefixHead
            cases first with
            | popLoadNonempty =>
                exact Or.inr
                  ⟨[], _, by simp,
                    AuthorizesReadNext.popLoad⟩
            | popFailureRetry operation expected actual next =>
                exact Or.inr
                  ⟨[],
                    .popFailure thread (some expected) (some node),
                    by simp,
                    AuthorizesReadNext.popFailure expected⟩
          · rcases prior with
              ⟨earlier, action, prefixTailShape, authorized⟩
            exact Or.inr
              ⟨prefixHead :: earlier, action,
                by simp [prefixTailShape],
                authorized⟩

/--
Every selected `readNext` occurrence in an invocation trace starting from
`idle` is immediately preceded by its acquire observer.
-/
theorem Execution.readNext_hasObserver
    {thread : Nat}
    {final : LocalState α}
    {labels leading suffix : List (Label α)}
    {operation : OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (execution : Execution thread .idle labels final)
    (shape :
      labels =
        leading ++ .readNext operation node next :: suffix) :
    ∃ earlier action,
      leading = earlier ++ [.atomic operation action] ∧
        AuthorizesReadNext thread node action := by
  rcases execution.readNext_predecessor shape with
    startsReady | observer
  · cases startsReady.2
  · exact observer

/--
At a selected successful-push occurrence, either the execution prefix starts
in the matching CAS-ready state, or the immediately preceding source label is
the exact `node->next` write used by that release CAS.
-/
theorem Execution.pushSuccess_predecessor
    {thread : Nat}
    {initial final : LocalState α}
    {labels leading suffix : List (Label α)}
    {operation : OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    (execution : Execution thread initial labels final)
    (shape :
      labels =
        leading ++
          .atomic operation
            (.pushSuccess thread reserved value expected) ::
          suffix) :
    (leading = [] ∧
      initial =
        .pushing operation reserved value expected) ∨
    ∃ earlier,
      leading =
        earlier ++ [.writeNext operation reserved expected] := by
  induction execution generalizing leading with
  | nil state =>
      simp at shape
  | @cons initial middle final label rest first later
      inductionHypothesis =>
      cases leading with
      | nil =>
          simp only [List.nil_append] at shape
          have labelShape :
              label =
                .atomic operation
                  (.pushSuccess
                    thread reserved value expected) :=
            (List.cons.inj shape).1
          subst label
          cases first
          exact Or.inl ⟨rfl, rfl⟩
      | cons leadingHead leadingTail =>
          simp only [List.cons_append] at shape
          have labelsMatch := List.cons.inj shape
          have restShape :
              rest =
                leadingTail ++
                  .atomic operation
                    (.pushSuccess
                      thread reserved value expected) ::
                    suffix :=
            labelsMatch.2
          rcases inductionHypothesis restShape with startsReady | prior
          · rcases startsReady with
              ⟨leadingTailEmpty, middleReady⟩
            subst leadingTail
            subst middle
            have labelShape : label = leadingHead :=
              labelsMatch.1
            subst leadingHead
            cases first
            exact Or.inr ⟨[], by simp⟩
          · rcases prior with ⟨earlier, leadingTailShape⟩
            exact Or.inr
              ⟨leadingHead :: earlier,
                by simp [leadingTailShape]⟩

/-- Every successful push in an idle-started trace has its source field write. -/
theorem Execution.pushSuccess_hasNextWrite
    {thread : Nat}
    {final : LocalState α}
    {labels leading suffix : List (Label α)}
    {operation : OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    (execution : Execution thread .idle labels final)
    (shape :
      labels =
        leading ++
          .atomic operation
            (.pushSuccess thread reserved value expected) ::
          suffix) :
    ∃ earlier,
      leading =
        earlier ++ [.writeNext operation reserved expected] := by
  rcases execution.pushSuccess_predecessor shape with
    startsReady | fieldWrite
  · cases startsReady.2
  · exact fieldWrite

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
      | writeNext operation node next =>
          obtain ⟨owner, ownerMember⟩ :=
            inductionHypothesis (by
              simpa [projectedActions, Label.action?] using member)
          exact ⟨owner, by simp [ownerMember]⟩
      | readNext operation node next =>
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
