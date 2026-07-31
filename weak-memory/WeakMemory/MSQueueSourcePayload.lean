import WeakMemory.MSQueueSourceRecordDependencies
import WeakMemory.MSQueueSourceReservation

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Payload association for successful Head advances

The structural dependency layer already identifies the exact link traversed
by a successful Head CAS, but leaves the link payload existential.  This
module discharges that gap at the source boundary.  A successful dequeue's
local run contains an exact payload-read event; `payloadReadInitialized`
finds the earlier payload initializer, and reservation freshness identifies
that initializer's enqueue invocation with the invocation behind the link.

The result is value-sensitive: the link traversed by a Head advance carries
exactly the value returned by that advance.
-/

/-- Membership of an event supplies its exact position in `zipIdx`. -/
private theorem exists_zipIdx_of_mem
    {event : TraceEvent Value}
    {trace : List (TraceEvent Value)}
    (member : event ∈ trace) :
    ∃ index, (event, index) ∈ trace.zipIdx := by
  rw [← List.zipIdx_map_fst 0 trace] at member
  obtain ⟨⟨selected, index⟩, selectedMember, selectedEq⟩ :=
    List.mem_map.mp member
  simp only at selectedEq
  subst selected
  exact ⟨index, selectedMember⟩

/-- A `filterMap` with duplicate-free outputs has unique retained inputs. -/
private theorem eq_of_filterMap_nodup
    {extract : β → Option γ}
    {items : List β}
    (noDuplicates : (items.filterMap extract).Nodup)
    {first second : β}
    {retained : γ}
    (firstMember : first ∈ items)
    (secondMember : second ∈ items)
    (firstExtracts : extract first = some retained)
    (secondExtracts : extract second = some retained) :
    first = second := by
  induction items generalizing first second with
  | nil => simp at firstMember
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp firstMember with
          firstIsHead | firstInRest
      · subst first
        rcases List.mem_cons.mp secondMember with
            secondIsHead | secondInRest
        · exact secondIsHead.symm
        · have retainedMember :
              retained ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr
              ⟨second, secondInRest, secondExtracts⟩
          have shapedNodup :
              (retained :: rest.filterMap extract).Nodup := by
            simpa [firstExtracts] using noDuplicates
          exact ((List.nodup_cons.mp shapedNodup).1
            retainedMember).elim
      · rcases List.mem_cons.mp secondMember with
            secondIsHead | secondInRest
        · subst second
          have retainedMember :
              retained ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr
              ⟨first, firstInRest, firstExtracts⟩
          have shapedNodup :
              (retained :: rest.filterMap extract).Nodup := by
            simpa [secondExtracts] using noDuplicates
          exact ((List.nodup_cons.mp shapedNodup).1
            retainedMember).elim
        · have restNodup :
              (rest.filterMap extract).Nodup :=
            ((List.sublist_cons_self head rest).filterMap extract).nodup
              noDuplicates
          exact inductionHypothesis restNodup
            firstInRest secondInRest firstExtracts secondExtracts

/-- Reservation freshness makes the enqueue invocation for one node unique,
including its immutable payload. -/
theorem SourceWellFormed.enqueueInvocation_eq_of_same_node
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {firstThread secondThread : ThreadId}
    {firstOperation secondOperation : OperationId}
    {node : NodeId}
    {firstValue secondValue : Value}
    (firstMember :
      TraceEvent.invokeEnqueue firstThread firstOperation node firstValue ∈
        trace)
    (secondMember :
      TraceEvent.invokeEnqueue secondThread secondOperation node secondValue ∈
        trace) :
    TraceEvent.invokeEnqueue firstThread firstOperation node firstValue =
      TraceEvent.invokeEnqueue secondThread secondOperation node secondValue := by
  exact eq_of_filterMap_nodup wellFormed.reservedNodesNodup
    firstMember secondMember rfl rfl

/-- The payload read immediately before a successful Head CAS belongs to an
enqueue invocation that reserved the exact desired node. -/
theorem SourceWellFormed.dequeueHeadPayload_hasInvocation
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation expected desired : Nat}
    {dequeued : Value}
    {observed : Ptr}
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation expected desired dequeued
          observed true⟩ ∈ trace) :
    ∃ owner invocation initializationIndex readIndex,
      initializationIndex < readIndex ∧
        (TraceEvent.initializePayload owner invocation desired dequeued,
          initializationIndex) ∈ trace.zipIdx ∧
        TraceEvent.invokeEnqueue owner invocation desired dequeued ∈ trace := by
  have observedExpected : observed = .node expected := by
    obtain ⟨before, after, step⟩ := wellFormed.atomicGenerated member
    cases step
    rfl
  subst observed
  obtain ⟨_leading, _headLoadId, _tailLoadId, _nextLoadId,
      _validationId, _tail, _trailing, _different, _threadShape,
      _headLoadMember, _tailLoadMember, _nextLoadMember,
      _validationMember, payloadMember, _headBeforeTail,
      _tailBeforeNext, _nextBeforeValidation, _validationBeforeCas⟩ :=
    wellFormed.dequeueHeadSuccess_provenance member
  obtain ⟨readIndex, readSelected⟩ :=
    exists_zipIdx_of_mem payloadMember
  obtain ⟨owner, invocation, initializationIndex, earlier,
      initializationSelected⟩ :=
    wellFormed.payloadReadInitialized readSelected
  have initializationMember :
      TraceEvent.initializePayload owner invocation desired dequeued ∈ trace :=
    List.fst_mem_of_mem_zipIdx initializationSelected
  exact ⟨owner, invocation, initializationIndex, readIndex, earlier,
    initializationSelected,
    wellFormed.payloadInitializationMatches initializationMember⟩

/-- Source payload provenance and reservation uniqueness identify the payload
of any link that installs the successful dequeue's desired node. -/
theorem SourceWellFormed.dequeueHeadPayload_eq_linkPayload
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation expected desired : Nat}
    {dequeued linked : Value}
    {observed : Ptr}
    (headMember :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation expected desired dequeued
          observed true⟩ ∈ trace)
    {link : Record Value}
    (linkMember : link ∈ structuralRecords trace)
    (linkShape : link.action = .link expected desired linked) :
    dequeued = linked := by
  obtain ⟨payloadOwner, payloadOperation, _initializationIndex,
      _readIndex, _earlier, _initializationSelected, payloadInvocation⟩ :=
    SourceWellFormed.dequeueHeadPayload_hasInvocation wellFormed headMember
  obtain ⟨_linkId, linkThread, linkOperation, _occurrenceShape,
      linkInvocation⟩ :=
    linkReservationOrigin wellFormed linkMember linkShape
  have invocationEq :=
    SourceWellFormed.enqueueInvocation_eq_of_same_node wellFormed
      payloadInvocation linkInvocation
  injection invocationEq with _threadEq _operationEq _nodeEq valueEq

namespace AtomSchedule

/-- Event-level exact payload dependency: the link traversed by a successful
Head CAS carries precisely the value read and returned by that CAS. -/
theorem dequeueHeadCAS_exactPayloadLink
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {thread casId operation expected desired : Nat}
    {dequeued : Value}
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation expected desired dequeued
          (.node expected) true⟩ ∈ trace) :
    ∃ link,
      link ∈ structuralRecords trace ∧
        link.action = .link expected desired dequeued ∧
        MultiLocationRC11.IdBefore link.point casId schedule.ids := by
  obtain ⟨link, linked, linkMember, linkShape, linkBeforeCas⟩ :=
    schedule.dequeueHeadCAS_linkDependency member
  have payloadEq :=
    SourceWellFormed.dequeueHeadPayload_eq_linkPayload
      execution.sourceWellFormed member linkMember linkShape
  subst linked
  exact ⟨link, linkMember, linkShape, linkBeforeCas⟩

/-- Record-level replay interface: every extracted Head advance has one exact
earlier link carrying its dequeued value. -/
theorem advanceHeadRecord_has_exactPayloadLink
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
    ∃ link,
      link ∈ structuralRecords trace ∧
        link.action = .link expected desired dequeued ∧
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
          exact schedule.dequeueHeadCAS_exactPayloadLink eventMember

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
