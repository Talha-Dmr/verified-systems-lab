import WeakMemory.MSQueueSourceControlProvenance
import WeakMemory.MSQueueSourcePredecessors

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Scheduled source observations behind structural records

The RMW predecessor lemmas identify the value overwritten by a structural
CAS.  Queue replay also needs the stable source observations that justified
choosing that CAS site.  This module packages those observations at record
level, without replacing their exact RC11 reads-from sources.
-/

namespace AtomSchedule

/-- A successful link retains the stable Tail validation from its own
attempt.  That validation reads either the dummy initializer or the exact
earlier Tail advance that installed the link's owner. -/
theorem linkRecord_tailObservation
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {tail node : NodeId}
    {value : Value}
    (actionShape : record.action = .link tail node value) :
    ∃ source validation,
      LatestSource schedule source validation ∧
        MultiLocationRC11.IdBefore
          validation.id record.point schedule.ids ∧
        ((source = tailInitializer dummy ∧ dummy = tail) ∨
          ∃ earlier previous,
            earlier ∈ structuralRecords trace ∧
              earlier.action = .advanceTail previous tail ∧
              earlier.pointAtom = source) := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  rcases occurrence with ⟨linkId, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation sourceTail sourceNode sourceValue
      observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.link.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl, rfl⟩
          have notMalformed :=
            execution.sourceWellFormed.atomic_not_malformedSuccess eventMember
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          obtain ⟨tailLoadId, nextLoadId, validationId,
              _tailNextPO, _nextValidationPO, validationLinkPO⟩ :=
            execution.enqueueLinkSuccess_programOrder eventMember
          let validation : MultiLocationRC11.Atom Site Ptr :=
            (⟨validationId,
              .enqueueTailValidate thread operation (.node sourceTail)⟩ :
                AtomicOccurrence Value).toRC11Atom
          obtain ⟨source, readsFrom, origin⟩ :=
            tailNodeRead_hasOrigin execution
              validationLinkPO.closed.1 rfl rfl
          refine ⟨source, validation,
            schedule.latestSource_of_readsFrom readsFrom,
            ?_, origin⟩
          change MultiLocationRC11.IdBefore validationId linkId
            (schedule.atoms.map MultiLocationRC11.Atom.id)
          exact schedule.respectsProgramOrder validationLinkPO
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
  | dequeueHeadValidateEmpty =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadCAS thread operation expected desired dequeued observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
