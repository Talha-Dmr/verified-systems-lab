import WeakMemory.MSQueueSourceControlProvenance
import WeakMemory.MSQueueSourceWriteOrigins

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Reservation provenance and freshness of successful links

The source machine retains the node reserved by an enqueue invocation in
every local state from payload initialization through the successful link.
This module connects that local fact to extracted structural records.  The
global reservation discipline then shows that a node can be installed by at
most one successful link and that the dummy node is never installed.
-/

/-- Local states that still carry one exact enqueue reservation. -/
def InFlightEnqueue
    (state : LocalState Value)
    (operation : OperationId)
    (node : NodeId)
    (value : Value) : Prop :=
  state = .enqueueWritingPayload operation node value ∨
  state = .enqueueInitializingNext operation node value ∨
  state = .enqueueLoadingTail operation node value ∨
  (∃ tail,
    state = .enqueueLoadingNext operation node value tail) ∨
  (∃ tail next,
    state = .enqueueValidatingTail operation node value tail next) ∨
  (∃ tail,
    state = .enqueueLinking operation node value tail) ∨
  (∃ expected desired,
    state = .enqueueHelpingTail operation node value expected desired) ∨
  (∃ expected,
    state = .enqueueFinishingTail operation node value expected)

/-- Entering an in-flight enqueue state either preserves the exact
reservation or is the invocation that created it. -/
theorem LocalStep.inFlightEnqueue_predecessor
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    {operation : OperationId}
    {node : NodeId}
    {value : Value}
    (step : LocalStep thread before event after)
    (active : InFlightEnqueue after operation node value) :
    InFlightEnqueue before operation node value ∨
      event = .invokeEnqueue thread operation node value := by
  cases step <;>
    simp [InFlightEnqueue] at active ⊢
  all_goals exact active

namespace Run

/-- A successful link belongs to the enqueue reservation already active at
the start of the supplied run, or to the exact invocation inside that run. -/
theorem successfulLink_active_or_invoked
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    {id operation owner node : Nat}
    {value : Value}
    {observed : Ptr}
    (run : Run thread initial events final)
    (member :
      TraceEvent.atomic
          ⟨id,
            .enqueueLinkCAS thread operation owner node value observed true⟩ ∈
        events) :
    InFlightEnqueue initial operation node value ∨
      TraceEvent.invokeEnqueue thread operation node value ∈ events := by
  induction run with
  | nil state => simp at member
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with isFirst | inRest
      · subst event
        cases first
        exact Or.inl (by simp [InFlightEnqueue])
      · rcases inductionHypothesis inRest with
          middleActive | invokedLater
        · rcases
            WeakMemory.MSQueue.Source.Structural.LocalStep.inFlightEnqueue_predecessor
              first middleActive with
            initialActive | isInvocation
          · exact Or.inl initialActive
          · exact Or.inr (by simp [isInvocation])
        · exact Or.inr (by simp [invokedLater])

end Run

namespace SourceWellFormed

/-- Every successful source link has the exact enqueue invocation that
reserved its installed node and payload. -/
theorem successfulLink_hasInvocation
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {id thread operation owner node : Nat}
    {value : Value}
    {observed : Ptr}
    (member :
      TraceEvent.atomic
          ⟨id,
            .enqueueLinkCAS thread operation owner node value observed true⟩ ∈
        trace) :
    TraceEvent.invokeEnqueue thread operation node value ∈ trace := by
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have projectedMember :
      TraceEvent.atomic
          ⟨id,
            .enqueueLinkCAS thread operation owner node value observed true⟩ ∈
        threadTrace trace thread := by
    apply List.mem_filter.mpr
    exact ⟨member, by
      simp [TraceEvent.thread, AtomicAction.thread]⟩
  rcases
      WeakMemory.MSQueue.Source.Structural.Run.successfulLink_active_or_invoked
        run projectedMember with
      active | invoked
  · simp [InFlightEnqueue] at active
  · exact (List.mem_filter.mp invoked).1

end SourceWellFormed

/-! ## Exact origin of an extracted link -/

/-- Inverting extraction of a link record recovers its exact successful
source occurrence, including the invoking thread and operation. -/
theorem linkRecord_occurrence
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    {owner node : NodeId}
    {value : Value}
    (member : record ∈ structuralRecords trace)
    (actionShape : record.action = .link owner node value) :
    ∃ id thread operation observed,
      record =
        ⟨⟨id,
            .enqueueLinkCAS thread operation owner node value observed true⟩,
          id, id, .link owner node value⟩ := by
  obtain ⟨occurrence, _occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail desired payload observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp at actionShape
          rcases actionShape with ⟨rfl, rfl, rfl⟩
          exact ⟨id, thread, operation, observed, rfl⟩
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
  | dequeueHeadCAS thread operation expected desired payload observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape

/-- Every extracted link installs the node reserved by its exact enqueue
invocation.  The record occurrence and invocation are retained together for
later representation proofs. -/
theorem linkReservationOrigin
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    {owner node : NodeId}
    {value : Value}
    (member : record ∈ structuralRecords trace)
    (actionShape : record.action = .link owner node value) :
    ∃ id thread operation,
      record =
          ⟨⟨id,
              .enqueueLinkCAS thread operation owner node value .null true⟩,
            id, id, .link owner node value⟩ ∧
        TraceEvent.invokeEnqueue thread operation node value ∈ trace := by
  obtain ⟨id, thread, operation, observed, recordShape⟩ :=
    linkRecord_occurrence member actionShape
  subst record
  have pointMember :=
    pointOccurrence_mem_of_structuralRecord wellFormed member
  have eventMember := atomicEvent_mem_of_atomicOccurrence_mem pointMember
  have observedNull : observed = .null := by
    obtain ⟨before, after, step⟩ :=
      wellFormed.atomicGenerated eventMember
    cases step
    rfl
  subst observed
  refine ⟨id, thread, operation, rfl, ?_⟩
  exact
    WeakMemory.MSQueue.Source.Structural.SourceWellFormed.successfulLink_hasInvocation
      wellFormed eventMember

/-- A node installed by a link occurs in the global reservation projection. -/
theorem linkedNode_mem_reservedNodes
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    {owner node : NodeId}
    {value : Value}
    (member : record ∈ structuralRecords trace)
    (actionShape : record.action = .link owner node value) :
    node ∈ reservedNodes trace := by
  obtain ⟨id, thread, operation, occurrenceShape, invocation⟩ :=
    linkReservationOrigin wellFormed member actionShape
  exact List.mem_filterMap.mpr
    ⟨TraceEvent.invokeEnqueue thread operation node value,
      invocation, rfl⟩

/-- The distinguished dummy node can never be installed by a successful
link. -/
theorem linkedNode_ne_dummy
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    {owner node : NodeId}
    {value : Value}
    (member : record ∈ structuralRecords trace)
    (actionShape : record.action = .link owner node value) :
    node ≠ dummy := by
  intro same
  subst node
  exact wellFormed.dummyNotReserved
    (linkedNode_mem_reservedNodes wellFormed member actionShape)

/-! ## At-most-once publication of a reservation -/

/-- Successful link occurrences retained with their full source labels. -/
private def successfulLinkOccurrence? :
    TraceEvent Value → Option (AtomicOccurrence Value)
  | .atomic occurrence@⟨_, .enqueueLinkCAS _ _ _ _ _ _ true⟩ =>
      some occurrence
  | _ => none

private def successfulLinkOccurrences
    (events : List (TraceEvent Value)) :
    List (AtomicOccurrence Value) :=
  events.filterMap successfulLinkOccurrence?

private theorem successfulLinkOccurrences_cons
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    successfulLinkOccurrences (event :: rest) =
      successfulLinkOccurrences [event] ++
        successfulLinkOccurrences rest := by
  change List.filterMap successfulLinkOccurrence? (event :: rest) =
    List.filterMap successfulLinkOccurrence? [event] ++
      List.filterMap successfulLinkOccurrence? rest
  rw [show event :: rest = [event] ++ rest by rfl,
    List.filterMap_append]

private theorem invocationIds_cons_append
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    invocationIds (event :: rest) =
      invocationIds [event] ++ invocationIds rest := by
  change List.filterMap TraceEvent.invocationId? (event :: rest) =
    List.filterMap TraceEvent.invocationId? [event] ++
      List.filterMap TraceEvent.invocationId? rest
  rw [show event :: rest = [event] ++ rest by rfl,
    List.filterMap_append]

/-
An enqueue has one unit of link credit until its successful link consumes
that credit.  Tail finishing and response states occur only after the credit
has been consumed.
-/
private def linkCredit
    (target : OperationId) : LocalState Value → Nat
  | .enqueueWritingPayload operation _ _
  | .enqueueInitializingNext operation _ _
  | .enqueueLoadingTail operation _ _
  | .enqueueLoadingNext operation _ _ _
  | .enqueueValidatingTail operation _ _ _ _
  | .enqueueLinking operation _ _ _
  | .enqueueHelpingTail operation _ _ _ _ =>
      if operation = target then 1 else 0
  | _ => 0

private theorem localStep_linkAccounting
    {thread : ThreadId}
    {initial final : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread initial event final)
    (target : OperationId) :
    List.count target
        ((successfulLinkOccurrences [event]).map
          (fun occurrence => occurrence.action.operation)) +
        linkCredit target final ≤
      List.count target (invocationIds [event]) +
        linkCredit target initial := by
  cases step <;>
    simp [successfulLinkOccurrences, successfulLinkOccurrence?,
      linkCredit, invocationIds, TraceEvent.invocationId?,
      AtomicAction.operation, List.count_cons] <;> omega

private theorem run_linkAccounting
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    (target : OperationId) :
    List.count target
        ((successfulLinkOccurrences events).map
          (fun occurrence => occurrence.action.operation)) +
        linkCredit target final ≤
      List.count target (invocationIds events) +
        linkCredit target initial := by
  induction run with
  | nil state => simp [successfulLinkOccurrences, invocationIds]
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      have firstAccounting := localStep_linkAccounting first target
      have laterAccounting := inductionHypothesis
      rw [successfulLinkOccurrences_cons,
        invocationIds_cons_append, List.map_append,
        List.count_append, List.count_append]
      omega

private theorem invocationIds_threadTrace_sublist
    (trace : List (TraceEvent Value))
    (thread : ThreadId) :
    (invocationIds (threadTrace trace thread)).Sublist
      (invocationIds trace) := by
  exact (List.filter_sublist
    (p := fun event => event.thread == thread)
    (l := trace)).filterMap TraceEvent.invocationId?

private theorem successfulLinkOperationsNodup
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    (thread : ThreadId) :
    ((successfulLinkOccurrences (threadTrace trace thread)).map
      (fun occurrence => occurrence.action.operation)).Nodup := by
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  apply List.nodup_iff_count.mpr
  intro operation
  have accounting := run_linkAccounting run operation
  have localInvocationNodup :
      (invocationIds (threadTrace trace thread)).Nodup :=
    (invocationIds_threadTrace_sublist trace thread).nodup
      wellFormed.invocationIdsNodup
  have invocationBound :=
    (List.nodup_iff_count.mp localInvocationNodup) operation
  simp [linkCredit] at accounting
  omega

private theorem successfulLinkOccurrence_mem_thread
    {trace : List (TraceEvent Value)}
    {id thread operation owner node : Nat}
    {value : Value}
    {observed : Ptr}
    (member :
      TraceEvent.atomic
          ⟨id,
            .enqueueLinkCAS thread operation owner node value observed true⟩ ∈
        trace) :
    (⟨id,
      .enqueueLinkCAS thread operation owner node value observed true⟩ :
        AtomicOccurrence Value) ∈
      successfulLinkOccurrences (threadTrace trace thread) := by
  apply List.mem_filterMap.mpr
  refine ⟨TraceEvent.atomic
    ⟨id,
      .enqueueLinkCAS thread operation owner node value observed true⟩,
    ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨member, by
    simp [TraceEvent.thread, AtomicAction.thread]⟩

private theorem eq_of_mem_of_map_nodup
    {items : List Item}
    {key : Item → Point}
    (keysNodup : (items.map key).Nodup)
    {left right : Item}
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameKey : key left = key right) :
    left = right := by
  induction items generalizing left right with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp keysNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (nodupParts.1
            (List.mem_map.mpr ⟨right, rightMember, sameKey.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (nodupParts.1
            (List.mem_map.mpr ⟨left, leftMember, sameKey⟩))
        · exact inductionHypothesis nodupParts.2
            leftMember rightMember sameKey

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

/-- One enqueue operation can emit at most one successful link occurrence. -/
private theorem successfulLinkOccurrence_eq
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {firstId secondId thread operation : Nat}
    {firstOwner secondOwner firstNode secondNode : NodeId}
    {firstValue secondValue : Value}
    {firstObserved secondObserved : Ptr}
    (firstMember :
      TraceEvent.atomic
          ⟨firstId,
            .enqueueLinkCAS thread operation firstOwner firstNode
              firstValue firstObserved true⟩ ∈ trace)
    (secondMember :
      TraceEvent.atomic
          ⟨secondId,
            .enqueueLinkCAS thread operation secondOwner secondNode
              secondValue secondObserved true⟩ ∈ trace) :
    (⟨firstId,
      .enqueueLinkCAS thread operation firstOwner firstNode
        firstValue firstObserved true⟩ : AtomicOccurrence Value) =
    ⟨secondId,
      .enqueueLinkCAS thread operation secondOwner secondNode
        secondValue secondObserved true⟩ := by
  apply eq_of_mem_of_map_nodup
    (items := successfulLinkOccurrences (threadTrace trace thread))
    (key := fun occurrence => occurrence.action.operation)
    (successfulLinkOperationsNodup wellFormed thread)
    (successfulLinkOccurrence_mem_thread firstMember)
    (successfulLinkOccurrence_mem_thread secondMember)
  rfl

/-- Reservation freshness lifts to structural links: two extracted links
cannot install the same node, even at different `next` locations. -/
theorem linkRecord_eq_of_same_node
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {first second : Record Value}
    {firstOwner secondOwner node : NodeId}
    {firstValue secondValue : Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace)
    (firstAction : first.action = .link firstOwner node firstValue)
    (secondAction : second.action = .link secondOwner node secondValue) :
    first = second := by
  obtain ⟨firstId, firstThread, firstOperation,
      firstShape, firstInvocation⟩ :=
    linkReservationOrigin wellFormed firstMember firstAction
  obtain ⟨secondId, secondThread, secondOperation,
      secondShape, secondInvocation⟩ :=
    linkReservationOrigin wellFormed secondMember secondAction
  have invocationEq :
      TraceEvent.invokeEnqueue firstThread firstOperation node firstValue =
        TraceEvent.invokeEnqueue secondThread secondOperation node secondValue :=
    eq_of_filterMap_nodup wellFormed.reservedNodesNodup
      firstInvocation secondInvocation rfl rfl
  injection invocationEq with threadEq operationEq _ valueEq
  subst secondThread
  subst secondOperation
  subst secondValue
  have firstLinkMember :
      TraceEvent.atomic
          ⟨firstId,
            .enqueueLinkCAS firstThread firstOperation firstOwner node
              firstValue .null true⟩ ∈ trace := by
    have pointMember :=
      pointOccurrence_mem_of_structuralRecord wellFormed firstMember
    rw [firstShape] at pointMember
    exact atomicEvent_mem_of_atomicOccurrence_mem pointMember
  have secondLinkMember :
      TraceEvent.atomic
          ⟨secondId,
            .enqueueLinkCAS firstThread firstOperation secondOwner node
              firstValue .null true⟩ ∈ trace := by
    have pointMember :=
      pointOccurrence_mem_of_structuralRecord wellFormed secondMember
    rw [secondShape] at pointMember
    exact atomicEvent_mem_of_atomicOccurrence_mem pointMember
  have occurrenceEq := successfulLinkOccurrence_eq wellFormed
    firstLinkMember secondLinkMember
  injection occurrenceEq with idEq ownerEq
  subst secondId
  cases ownerEq
  exact firstShape.trans secondShape.symm

/-- The same-node uniqueness theorem also identifies the predecessor site and
payload: publishing one reservation twice with different link data is
impossible. -/
theorem linkData_eq_of_same_node
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {first second : Record Value}
    {firstOwner secondOwner node : NodeId}
    {firstValue secondValue : Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace)
    (firstAction : first.action = .link firstOwner node firstValue)
    (secondAction : second.action = .link secondOwner node secondValue) :
    first = second ∧
      firstOwner = secondOwner ∧
      firstValue = secondValue := by
  have recordEq := linkRecord_eq_of_same_node wellFormed
    firstMember secondMember firstAction secondAction
  have actionEq :
      (Action.link firstOwner node firstValue : Action Value) =
        .link secondOwner node secondValue :=
    firstAction.symm.trans
      ((congrArg Record.action recordEq).trans secondAction)
  injection actionEq with ownerEq _ valueEq
  exact ⟨recordEq, ownerEq, valueEq⟩

end WeakMemory.MSQueue.Source.Structural
