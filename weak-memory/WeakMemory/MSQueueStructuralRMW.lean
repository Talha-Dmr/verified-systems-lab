import WeakMemory.MSQueueSourceVisibility

namespace WeakMemory.MSQueue.Source.Structural

/-!
# RMW classification of structural queue points

The source-to-chain extraction has two kinds of points: successful CAS events
and the earlier null `next` load used by an empty dequeue.  This module states
that distinction explicitly and packages the reads-from/immediate-MO witness
available for every CAS-backed structural record.
-/

namespace Action

/-- Exactly the structural actions whose point is a successful source CAS. -/
def IsCAS : Action Value → Prop
  | .link .. | .advanceTail .. | .advanceHead .. => True
  | .empty .. => False

@[simp] theorem link_isCAS
    (tail node : NodeId) (value : Value) :
    (Action.link tail node value).IsCAS :=
  trivial

@[simp] theorem advanceTail_isCAS
    (expected desired : NodeId) :
    (Action.advanceTail (Value := Value) expected desired).IsCAS :=
  trivial

@[simp] theorem advanceHead_isCAS
    (expected desired : NodeId) (value : Value) :
    (Action.advanceHead expected desired value).IsCAS :=
  trivial

@[simp] theorem empty_not_isCAS
    (head : NodeId) :
    ¬ (Action.empty (Value := Value) head).IsCAS := by
  simp [IsCAS]

/-- `IsCAS` is exactly the complement of the empty-dequeue action shape. -/
theorem isCAS_iff_not_empty (action : Action Value) :
    action.IsCAS ↔
      ∀ head, action ≠ .empty head := by
  cases action <;> simp [IsCAS]

end Action

/-- A selected CAS-backed structural record reconstructs an RMW point atom. -/
theorem pointAtom_isRMW_of_selected
    {occurrence : AtomicOccurrence Value}
    {record : Record Value}
    (selected : structuralRecordOfOccurrence? occurrence = some record)
    (casPoint : record.action.IsCAS) :
    record.pointAtom.IsRMW := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp [Action.IsCAS] at casPoint
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial

/-- Every extracted non-empty (CAS-backed) structural record has an RMW point. -/
theorem pointAtom_isRMW_of_structuralRecord
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    (casPoint : record.action.IsCAS) :
    record.pointAtom.IsRMW := by
  rcases List.mem_filterMap.mp member with
    ⟨event, _eventMember, selected⟩
  cases event with
  | atomic occurrence =>
      exact pointAtom_isRMW_of_selected selected casPoint
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected

/-- An RMW point cannot be the synthetic null-load point of an empty action. -/
theorem action_isCAS_of_pointAtom_isRMW
    (record : Record Value)
    (isRMW : record.pointAtom.IsRMW) :
    record.action.IsCAS := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;>
    simp [Action.IsCAS, Record.pointAtom, Record.pointOccurrence,
      AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.IsRMW,
      MultiLocationRC11.Access.IsRMW, AtomicAction.access] at isRMW ⊢

/-- Exact classification: among extracted records, precisely the non-empty
CAS-backed actions reconstruct RMW point atoms. -/
theorem pointAtom_isRMW_iff_action_isCAS
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom.IsRMW ↔ record.action.IsCAS := by
  constructor
  · exact action_isCAS_of_pointAtom_isRMW record
  · exact pointAtom_isRMW_of_structuralRecord member

/--
Every CAS-backed structural point has an RF source, and RC11 RMW atomicity
makes that source the point's immediate modification-order predecessor.
-/
theorem pointReadsFromImmediate
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    (casPoint : record.action.IsCAS) :
    ∃ source,
      MultiLocationRC11.RF execution.candidate source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom := by
  obtain ⟨source, readsFrom⟩ :=
    AtomSchedule.pointReadsFrom (execution := execution) member
  exact ⟨source, readsFrom,
    execution.valid.rmwReadsImmediatePredecessor readsFrom
      (pointAtom_isRMW_of_structuralRecord member casPoint)⟩

namespace AtomSchedule

/-- The scheduled form additionally records that the RF source is the latest
visible source before the successful structural CAS. -/
theorem pointRMWLatestSource
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    (casPoint : record.action.IsCAS) :
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom := by
  obtain ⟨source, readsFrom, immediate⟩ :=
    pointReadsFromImmediate (execution := execution) member casPoint
  exact ⟨source, schedule.latestSource_of_readsFrom readsFrom, immediate⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
