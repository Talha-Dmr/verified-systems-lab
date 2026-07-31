import WeakMemory.MSQueueHistory
import WeakMemory.MSQueueRecordScheduling

namespace WeakMemory.MSQueue.Source

/-!
# Source histories and identified Michael--Scott commits

This module is the finite identity-preserving bridge from the source-shaped
Michael--Scott trace to `MSQueue.HW`.  Client invocations and responses retain
their position in source order.  Separately, structural commit records retain
the thread and operation identity attached to each abstract FIFO commit.

The structural atom schedule changes only the order of those completed
operations.  The permutation theorems below show that scheduling neither
invents nor loses a source commit; later modules can add completion,
per-thread equivalence, and client real-time arguments.
-/

/-- Project one source event to a client-visible history event. -/
def sourceHistoryEvent?
    (event : TraceEvent Value) :
    Option (MSQueue.HW.HistoryEvent Value) :=
  match event with
  | .invokeEnqueue thread operation _ value =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .enqueue value
      })
  | .invokeDequeue thread operation =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .dequeue
      })
  | .respondEnqueue thread operation =>
      some (.respond {
        thread := thread
        id := operation
        response := .enqueued
      })
  | .respondDequeue thread operation result =>
      some (.respond {
        thread := thread
        id := operation
        response := .dequeued result
      })
  | .initializePayload .. | .atomic .. | .readPayload .. =>
      none

/-- Client-visible history in global source-trace order. -/
def sourceHistory
    (trace : List (TraceEvent Value)) : MSQueue.HW.History Value :=
  trace.filterMap sourceHistoryEvent?

/-- Attach source operation identity to one abstract commit record. -/
def identifiedCommit
    (record : AtomicOccurrence.CommitRecord Value) :
    MSQueue.HW.IdentifiedCompleted Value where
  thread := record.thread
  id := record.operation
  operation := record.commit.completed.operation
  response := record.commit.completed.response

/-- Completed source operations in source-trace order. -/
def sourceCompletedOperations
    (trace : List (TraceEvent Value)) :
    List (MSQueue.HW.IdentifiedCompleted Value) :=
  (trace.filterMap TraceEvent.commitRecord?).map identifiedCommit

@[simp] theorem sourceHistoryEvent?_invokeEnqueue
    (thread : ThreadId)
    (operation : OperationId)
    (node : NodeId)
    (value : Value) :
    sourceHistoryEvent?
        (.invokeEnqueue thread operation node value) =
      some (.invoke {
        thread := thread
        id := operation
        operation := .enqueue value
      }) :=
  rfl

@[simp] theorem sourceHistoryEvent?_initializePayload
    (thread : ThreadId)
    (operation : OperationId)
    (node : NodeId)
    (value : Value) :
    sourceHistoryEvent?
        (.initializePayload thread operation node value) = none :=
  rfl

@[simp] theorem sourceHistoryEvent?_invokeDequeue
    {Value : Type}
    (thread : ThreadId)
    (operation : OperationId) :
    sourceHistoryEvent? (Value := Value)
        (.invokeDequeue thread operation) =
      (some (.invoke {
        thread := thread
        id := operation
        operation := .dequeue
      }) : Option (MSQueue.HW.HistoryEvent Value)) :=
  rfl

@[simp] theorem sourceHistoryEvent?_atomic
    (occurrence : AtomicOccurrence Value) :
    sourceHistoryEvent? (.atomic occurrence) = none :=
  rfl

@[simp] theorem sourceHistoryEvent?_readPayload
    (thread : ThreadId)
    (operation : OperationId)
    (node : NodeId)
    (value : Value) :
    sourceHistoryEvent?
        (.readPayload thread operation node value) = none :=
  rfl

@[simp] theorem sourceHistoryEvent?_respondEnqueue
    {Value : Type}
    (thread : ThreadId)
    (operation : OperationId) :
    sourceHistoryEvent? (Value := Value)
        (.respondEnqueue thread operation) =
      (some (.respond {
        thread := thread
        id := operation
        response := .enqueued
      }) : Option (MSQueue.HW.HistoryEvent Value)) :=
  rfl

@[simp] theorem sourceHistoryEvent?_respondDequeue
    (thread : ThreadId)
    (operation : OperationId)
    (result : Option Value) :
    sourceHistoryEvent?
        (.respondDequeue thread operation result) =
      some (.respond {
        thread := thread
        id := operation
        response := .dequeued result
      }) :=
  rfl

@[simp] theorem sourceHistory_nil :
    sourceHistory ([] : List (TraceEvent Value)) = [] :=
  rfl

@[simp] theorem sourceHistory_cons
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    sourceHistory (event :: rest) =
      match sourceHistoryEvent? event with
      | none => sourceHistory rest
      | some visible => visible :: sourceHistory rest := by
  unfold sourceHistory
  rw [List.filterMap_cons]
  cases sourceHistoryEvent? event <;> rfl

/-- Membership in the projected client history has an exact source witness. -/
theorem mem_sourceHistory
    {trace : List (TraceEvent Value)}
    {visible : MSQueue.HW.HistoryEvent Value} :
    visible ∈ sourceHistory trace ↔
      ∃ event,
        event ∈ trace ∧ sourceHistoryEvent? event = some visible := by
  simp [sourceHistory]

@[simp] theorem identifiedCommit_thread
    (record : AtomicOccurrence.CommitRecord Value) :
    (identifiedCommit record).thread = record.thread :=
  rfl

@[simp] theorem identifiedCommit_id
    (record : AtomicOccurrence.CommitRecord Value) :
    (identifiedCommit record).id = record.operation :=
  rfl

@[simp] theorem identifiedCommit_operation
    (record : AtomicOccurrence.CommitRecord Value) :
    (identifiedCommit record).operation =
      record.commit.completed.operation :=
  rfl

@[simp] theorem identifiedCommit_response
    (record : AtomicOccurrence.CommitRecord Value) :
    (identifiedCommit record).response =
      record.commit.completed.response :=
  rfl

@[simp] theorem identifiedCommit_erase
    (record : AtomicOccurrence.CommitRecord Value) :
    (identifiedCommit record).erase = record.commit.completed :=
  rfl

@[simp] theorem sourceCompletedOperations_nil :
    sourceCompletedOperations ([] : List (TraceEvent Value)) = [] :=
  rfl

@[simp] theorem sourceCompletedOperations_cons
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    sourceCompletedOperations (event :: rest) =
      match event.commitRecord? with
      | none => sourceCompletedOperations rest
      | some record =>
          identifiedCommit record :: sourceCompletedOperations rest := by
  unfold sourceCompletedOperations
  simp only [List.filterMap_cons]
  cases event.commitRecord? <;> rfl

/-- Membership in source completed operations has an exact commit record. -/
theorem mem_sourceCompletedOperations
    {trace : List (TraceEvent Value)}
    {entry : MSQueue.HW.IdentifiedCompleted Value} :
    entry ∈ sourceCompletedOperations trace ↔
      ∃ record,
        record ∈ trace.filterMap TraceEvent.commitRecord? ∧
          identifiedCommit record = entry := by
  simp [sourceCompletedOperations]

namespace Structural

namespace AtomSchedule

/-- Identified completed operations in structural atom-schedule order. -/
def scheduledOperations
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    List (MSQueue.HW.IdentifiedCompleted Value) :=
  ((recordsOn trace schedule.atoms).filterMap Record.commitRecord?).map
    Source.identifiedCommit

/-- Membership in the scheduled projection has an exact commit record. -/
theorem mem_scheduledOperations
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {entry : MSQueue.HW.IdentifiedCompleted Value} :
    entry ∈ schedule.scheduledOperations ↔
      ∃ record,
        record ∈
            (recordsOn trace schedule.atoms).filterMap
              Record.commitRecord? ∧
          Source.identifiedCommit record = entry := by
  simp [scheduledOperations]

/-- Scheduled commit records are exactly the source commit records, reordered. -/
theorem scheduledCommitRecords_perm_source
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    ((recordsOn trace schedule.atoms).filterMap Record.commitRecord?).Perm
      (trace.filterMap TraceEvent.commitRecord?) := by
  have reordered := schedule.recordsOn_perm.filterMap Record.commitRecord?
  rw [structuralCommitRecords] at reordered
  exact reordered

/-- Atom scheduling reorders, but neither loses nor invents, source operations. -/
theorem scheduledOperations_perm_source
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    schedule.scheduledOperations.Perm
      (Source.sourceCompletedOperations trace) := by
  exact schedule.scheduledCommitRecords_perm_source.map
    Source.identifiedCommit

end AtomSchedule

namespace Certificate

/-- Identity erasure commutes with commit-record extraction from any record list. -/
private theorem eraseIdentities_filterMap_commitRecords
    (records : List (Record Value)) :
    MSQueue.HW.eraseIdentities
        ((records.filterMap Record.commitRecord?).map
          Source.identifiedCommit) =
      completedHistory (records.filterMap Record.commit?) := by
  induction records with
  | nil =>
      rfl
  | cons record rest inductionHypothesis =>
      rcases record with ⟨occurrence, point, validation, action⟩
      cases action <;>
        simp [Record.commitRecord?, Record.commit?,
          Source.identifiedCommit,
          MSQueue.HW.IdentifiedCompleted.erase,
          Commit.completed, completedHistory, inductionHypothesis]

/-- Certificate commit records are the records used by scheduled operations. -/
theorem scheduledOperations_eq_commitRecords_map
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    certificate.atomSchedule.scheduledOperations =
      certificate.commitRecords.map Source.identifiedCommit :=
  rfl

/-- The certificate-side identified projection covers every source commit. -/
theorem scheduledOperations_perm_source
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    certificate.atomSchedule.scheduledOperations.Perm
      (Source.sourceCompletedOperations trace) := by
  rw [certificate.scheduledOperations_eq_commitRecords_map,
    Source.sourceCompletedOperations]
  exact certificate.commitRecords_perm_source.map Source.identifiedCommit

/--
Erasing schedule-side source identities gives exactly the anonymous FIFO
history already certified by structural replay.
-/
theorem eraseIdentities_scheduledOperations
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    MSQueue.HW.eraseIdentities
        certificate.atomSchedule.scheduledOperations =
      completedHistory certificate.commits := by
  rw [certificate.scheduledOperations_eq_commitRecords_map]
  exact eraseIdentities_filterMap_commitRecords
    (recordsOn trace certificate.atomSchedule.atoms)

end Certificate

end Structural

end WeakMemory.MSQueue.Source
