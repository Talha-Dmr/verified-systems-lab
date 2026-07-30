import WeakMemory.TreiberHistory
import WeakMemory.TreiberNodeAccessDerivation

namespace WeakMemory.TreiberRC11

/-!
# Projecting source labels to client histories

This module contains only the finite, identity-preserving projections needed
by the later Herlihy–Wing completion proof. Invocation and response labels
form the client history. Atomic labels that carry an abstract commit form the
candidate completed-operation list. All implementation-internal labels are
discarded by the corresponding projection.
-/

/-- Project one source label to a client-visible history event. -/
def sourceHistoryEvent?
    (owned : EventGraph.OwnedLabel α) :
    Option (HerlihyWing.HistoryEvent α) :=
  match owned.label with
  | .invokePush operation _ value =>
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .push value
      })
  | .invokePop operation =>
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .pop
      })
  | .invokeIsEmpty operation =>
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .isEmpty
      })
  | .respond operation response =>
      some (.respond {
        thread := owned.thread
        id := operation
        response := response
      })
  | .writeNext .. | .readNext .. | .atomic .. =>
      none

/-- Client-visible source history in global source-label order. -/
def sourceHistory
    (skeleton : EventGraph.Skeleton α) :
    HerlihyWing.History α :=
  skeleton.labels.filterMap sourceHistoryEvent?

/--
Attach source identity and thread ownership to one abstract Treiber commit.
-/
def identifiedCommit
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    HerlihyWing.IdentifiedCompleted α where
  thread := thread
  id := operation
  operation := commit.completed.operation
  response := commit.completed.response

/-- Project one linearizing atomic source label to its completed operation. -/
def sourceCommit?
    (owned : EventGraph.OwnedLabel α) :
    Option (HerlihyWing.IdentifiedCompleted α) :=
  match owned.label with
  | .atomic operation action =>
      match action.commit? with
      | none => none
      | some commit =>
          some (identifiedCommit owned.thread operation commit)
  | _ => none

/-- Abstract operations committed by the source skeleton, in source order. -/
def sourceCommittedOperations
    (skeleton : EventGraph.Skeleton α) :
    List (HerlihyWing.IdentifiedCompleted α) :=
  skeleton.labels.filterMap sourceCommit?

@[simp] theorem sourceHistory_empty :
    sourceHistory
      ({ labels := [] } : EventGraph.Skeleton α) = [] :=
  rfl

@[simp] theorem sourceHistory_cons
    (owned : EventGraph.OwnedLabel α)
    (labels : List (EventGraph.OwnedLabel α)) :
    sourceHistory
        ({ labels := owned :: labels } :
          EventGraph.Skeleton α) =
      match sourceHistoryEvent? owned with
      | none =>
          sourceHistory
            ({ labels := labels } : EventGraph.Skeleton α)
      | some event =>
          event ::
            sourceHistory
              ({ labels := labels } : EventGraph.Skeleton α) := by
  unfold sourceHistory
  rw [List.filterMap_cons]
  cases sourceHistoryEvent? owned <;> rfl

@[simp] theorem sourceCommittedOperations_empty :
    sourceCommittedOperations
      ({ labels := [] } : EventGraph.Skeleton α) = [] :=
  rfl

@[simp] theorem sourceCommittedOperations_cons
    (owned : EventGraph.OwnedLabel α)
    (labels : List (EventGraph.OwnedLabel α)) :
    sourceCommittedOperations
        ({ labels := owned :: labels } :
          EventGraph.Skeleton α) =
      match sourceCommit? owned with
      | none =>
          sourceCommittedOperations
            ({ labels := labels } : EventGraph.Skeleton α)
      | some entry =>
          entry ::
            sourceCommittedOperations
              ({ labels := labels } : EventGraph.Skeleton α) := by
  unfold sourceCommittedOperations
  rw [List.filterMap_cons]
  cases sourceCommit? owned <;> rfl

@[simp] theorem identifiedCommit_thread
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    (identifiedCommit thread operation commit).thread = thread :=
  rfl

@[simp] theorem identifiedCommit_id
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    (identifiedCommit thread operation commit).id = operation :=
  rfl

@[simp] theorem identifiedCommit_operation
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    (identifiedCommit thread operation commit).operation =
      commit.completed.operation :=
  rfl

@[simp] theorem identifiedCommit_response
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    (identifiedCommit thread operation commit).response =
      commit.completed.response :=
  rfl

@[simp] theorem identifiedCommit_erase
    (thread : Nat)
    (operation : ControlFlow.OperationId)
    (commit : Treiber.Commit α) :
    (identifiedCommit thread operation commit).erase =
      commit.completed :=
  rfl

@[simp] theorem sourceHistoryEvent?_invokePush
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    (labelShape :
      owned.label = .invokePush operation reserved value) :
    sourceHistoryEvent? owned =
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .push value
      }) := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_invokePop
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    (labelShape :
      owned.label = .invokePop operation) :
    sourceHistoryEvent? owned =
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .pop
      }) := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_invokeIsEmpty
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    (labelShape :
      owned.label = .invokeIsEmpty operation) :
    sourceHistoryEvent? owned =
      some (.invoke {
        thread := owned.thread
        id := operation
        operation := .isEmpty
      }) := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_respond
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {response : StackSpec.Response α}
    (labelShape :
      owned.label = .respond operation response) :
    sourceHistoryEvent? owned =
      some (.respond {
        thread := owned.thread
        id := operation
        response := response
      }) := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_writeNext
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (labelShape :
      owned.label = .writeNext operation node next) :
    sourceHistoryEvent? owned = none := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_readNext
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (labelShape :
      owned.label = .readNext operation node next) :
    sourceHistoryEvent? owned = none := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceHistoryEvent?_atomic
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (labelShape :
      owned.label = .atomic operation action) :
    sourceHistoryEvent? owned = none := by
  simp [sourceHistoryEvent?, labelShape]

@[simp] theorem sourceCommit?_atomic
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (labelShape :
      owned.label = .atomic operation action) :
    sourceCommit? owned =
      action.commit?.map
        (identifiedCommit owned.thread operation) := by
  simp [sourceCommit?, labelShape]
  cases action.commit? <;> rfl

@[simp] theorem sourceCommit?_invokePush
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    (labelShape :
      owned.label = .invokePush operation reserved value) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

@[simp] theorem sourceCommit?_invokePop
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    (labelShape :
      owned.label = .invokePop operation) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

@[simp] theorem sourceCommit?_invokeIsEmpty
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    (labelShape :
      owned.label = .invokeIsEmpty operation) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

@[simp] theorem sourceCommit?_writeNext
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (labelShape :
      owned.label = .writeNext operation node next) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

@[simp] theorem sourceCommit?_readNext
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (labelShape :
      owned.label = .readNext operation node next) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

@[simp] theorem sourceCommit?_respond
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {response : StackSpec.Response α}
    (labelShape :
      owned.label = .respond operation response) :
    sourceCommit? owned = none := by
  simp [sourceCommit?, labelShape]

theorem sourceCommit?_eq_some_of_atomic
    (owned : EventGraph.OwnedLabel α)
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    {commit : Treiber.Commit α}
    (labelShape :
      owned.label = .atomic operation action)
    (commits : action.commit? = some commit) :
    sourceCommit? owned =
      some (identifiedCommit owned.thread operation commit) := by
  simp [sourceCommit?, labelShape, commits]

theorem mem_sourceHistory
    {skeleton : EventGraph.Skeleton α}
    {event : HerlihyWing.HistoryEvent α} :
    event ∈ sourceHistory skeleton ↔
      ∃ owned,
        owned ∈ skeleton.labels ∧
          sourceHistoryEvent? owned = some event := by
  simp [sourceHistory]

theorem mem_sourceCommittedOperations
    {skeleton : EventGraph.Skeleton α}
    {entry : HerlihyWing.IdentifiedCompleted α} :
    entry ∈ sourceCommittedOperations skeleton ↔
      ∃ owned,
        owned ∈ skeleton.labels ∧
          sourceCommit? owned = some entry := by
  simp [sourceCommittedOperations]

end WeakMemory.TreiberRC11
