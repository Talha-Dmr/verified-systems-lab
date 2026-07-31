import WeakMemory.MSQueueSourceDependencies
import WeakMemory.MSQueueSourceHeadDependencies

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Record-level source dependencies

The source provenance layer states some dependencies at the exact atomic
event that completed an attempt.  Structural replay, however, consumes
`Record`s.  This module transports those results to selected structural
records without weakening either record identity or atom-schedule order.
-/

namespace AtomSchedule

/-- A selected Tail-advance record has an exact earlier link record for the
edge it traverses. -/
theorem advanceTailRecord_has_priorLink
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {expected desired : NodeId}
    (actionShape : record.action = .advanceTail expected desired) :
    ∃ link value,
      link ∈ structuralRecords trace ∧
        link.action = .link expected desired value ∧
        MultiLocationRC11.IdBefore
          link.point record.point schedule.ids :=
  schedule.advanceTail_has_priorLink member actionShape

/-- A selected successful Head-advance record traverses an exact link record
whose point is earlier in every admitted atom schedule.  The link payload is
left existential here: identifying it with the dequeue's non-atomic payload
read is the separate publication/HB obligation. -/
theorem advanceHeadRecord_has_priorLink
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {expected desired : NodeId}
    {dequeued : Value}
    (actionShape :
      record.action = .advanceHead expected desired dequeued) :
    ∃ link value,
      link ∈ structuralRecords trace ∧
        link.action = .link expected desired value ∧
        MultiLocationRC11.IdBefore
          link.point record.point schedule.ids := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  have notMalformed :=
    execution.sourceWellFormed.atomic_not_malformedSuccess eventMember
  rcases occurrence with ⟨casId, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueHelpTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueFinishTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHelpTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadCAS thread operation sourceExpected sourceDesired value
      observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.advanceHead.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl, rfl⟩
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          exact schedule.dequeueHeadCAS_linkDependency eventMember

/-- A selected empty record's retroactive null-read point takes its latest
source directly from that node's `next` initializer. -/
theorem emptyRecord_has_nullInitializer
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {head : NodeId}
    (actionShape : record.action = .empty head) :
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        execution.candidate.InitializerAt (.next head) source := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  rcases occurrence with ⟨validationId, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation sourceHead nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp only [Action.empty.injEq] at actionShape
      subst sourceHead
      simpa [Record.pointAtom, Record.pointOccurrence,
        AtomicAction.thread, AtomicAction.operation] using
        (schedule.dequeueEmpty_nullInitializer eventMember)
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
