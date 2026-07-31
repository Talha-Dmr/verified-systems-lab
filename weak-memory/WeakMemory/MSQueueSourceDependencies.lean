import WeakMemory.MSQueueSourcePredecessors
import WeakMemory.MSQueueSourceControlProvenance

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Structural source dependencies

This layer connects control-flow provenance to RC11 read origins.  In
particular, advancing `Tail` to a node is never an orphan structural effect:
the node was first installed by a successful link at the expected node, and
that link precedes the Tail CAS in every schedule respecting `PO` and `ECO`.
-/

namespace AtomSchedule

/-- Every successful Tail advance depends on the link that installed its
desired node at `expected.next`. -/
theorem advanceTail_has_priorLink
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
        MultiLocationRC11.IdBefore link.point record.point schedule.ids := by
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
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.advanceTail.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl⟩
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          obtain ⟨tailLoadId, nextLoadId, validationId,
              _tailBeforeNext, nextBeforeValidation,
              validationBeforeCAS⟩ :=
            execution.enqueueHelpTailSuccess_programOrder eventMember
          obtain ⟨source, link, value, readsFrom, linkMember,
              linkShape, linkExact⟩ :=
            nextNodeRead_hasLinkOrigin execution
              nextBeforeValidation.closed.1 rfl rfl
          have linkBeforeNext := schedule.readsFrom_before readsFrom
          rw [← linkExact] at linkBeforeNext
          have nextBeforeValidation' :=
            schedule.respectsProgramOrder nextBeforeValidation
          have validationBeforeCAS' :=
            schedule.respectsProgramOrder validationBeforeCAS
          refine ⟨link, value, linkMember, linkShape, ?_⟩
          simpa [AtomicOccurrence.toRC11Atom] using
            (MultiLocationRC11.IdBefore.transitive linkBeforeNext
              (MultiLocationRC11.IdBefore.transitive
                nextBeforeValidation' validationBeforeCAS'))
  | enqueueFinishTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.advanceTail.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl⟩
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          obtain ⟨value, _leading, linkId, _trailing, _threadShape,
              linkEventMember, linkBeforeCAS⟩ :=
            execution.sourceWellFormed.enqueueFinishTailSuccess_provenance
              eventMember
          let linkOccurrence : AtomicOccurrence Value :=
            ⟨linkId,
              .enqueueLinkCAS thread operation sourceExpected sourceDesired value
                .null true⟩
          let link : Record Value :=
            ⟨linkOccurrence, linkId, linkId,
              .link sourceExpected sourceDesired value⟩
          have linkMember : link ∈ structuralRecords trace := by
            apply List.mem_filterMap.mpr
            refine ⟨TraceEvent.atomic linkOccurrence,
              linkEventMember, ?_⟩
            rfl
          have linkOccurrenceMember :
              linkOccurrence ∈ atomicOccurrences trace :=
            atomicOccurrence_mem_of_atomicEvent_mem linkEventMember
          have tailOccurrenceMember :
              (⟨casId,
                AtomicAction.enqueueFinishTailCAS thread operation
                  sourceExpected sourceDesired (.node sourceExpected) true⟩ :
                    AtomicOccurrence Value) ∈ atomicOccurrences trace :=
            occurrenceMember
          have programOrder :=
            execution.programOrder_of_atomicIdBefore
              linkOccurrenceMember tailOccurrenceMember rfl linkBeforeCAS
          refine ⟨link, value, linkMember, rfl, ?_⟩
          exact schedule.respectsProgramOrder programOrder
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
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.advanceTail.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl⟩
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          obtain ⟨headLoadId, tailLoadId, nextLoadId, validationId,
              _headBeforeTail, _tailBeforeNext, nextBeforeValidation,
              validationBeforeCAS⟩ :=
            execution.dequeueHelpTailSuccess_programOrder eventMember
          obtain ⟨source, link, value, readsFrom, linkMember,
              linkShape, linkExact⟩ :=
            nextNodeRead_hasLinkOrigin execution
              nextBeforeValidation.closed.1 rfl rfl
          have linkBeforeNext := schedule.readsFrom_before readsFrom
          rw [← linkExact] at linkBeforeNext
          have nextBeforeValidation' :=
            schedule.respectsProgramOrder nextBeforeValidation
          have validationBeforeCAS' :=
            schedule.respectsProgramOrder validationBeforeCAS
          refine ⟨link, value, linkMember, linkShape, ?_⟩
          simpa [AtomicOccurrence.toRC11Atom] using
            (MultiLocationRC11.IdBefore.transitive linkBeforeNext
              (MultiLocationRC11.IdBefore.transitive
                nextBeforeValidation' validationBeforeCAS'))
  | dequeueHeadCAS thread operation sourceExpected sourceDesired value
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
