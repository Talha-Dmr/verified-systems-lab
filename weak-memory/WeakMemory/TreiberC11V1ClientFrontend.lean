import WeakMemory.TreiberC11V1SourceFrontend
import WeakMemory.TreiberRealTime
import WeakMemory.TreiberSourceCompletion

namespace WeakMemory.TreiberC11V1.ClientFrontend

open SourceFrontend

/-!
# Client-side refinement for the independent Treiber semantics

This module isolates the client-history, node-lifetime, and real-time parts of
the eventual C11 frontend.  It does not depend on a concrete atom-to-target
graph projection.  The two target-facing theorems therefore accept exact
projection equalities, which the source and relation frontends can discharge.
-/

/-! ## Direct consequences of the independent client contract -/

namespace ClientContract

/-- A push invocation carries the candidate's fixed node payload. -/
theorem payload_of_invokePush
    {candidate : RC11.Candidate α}
    (contract : ClientContract candidate)
    {thread operation node}
    {value : α}
    (member :
      TraceEvent.invokePush thread operation node value ∈
        candidate.trace) :
    candidate.payload node = value := by
  simpa [PayloadAgrees] using
    contract.payloadAgreement _ member

/-- Every push CAS annotation carries the candidate's fixed node payload. -/
theorem payload_of_pushCas
    {candidate : RC11.Candidate α}
    (contract : ClientContract candidate)
    {id thread operation node}
    {value : α}
    {expected observed : Ptr}
    {succeeded : Bool}
    (member :
      TraceEvent.atomic
          ⟨id,
            .pushCas thread operation node value
              expected observed succeeded⟩ ∈
        candidate.trace) :
    candidate.payload node = value := by
  simpa [PayloadAgrees] using
    contract.payloadAgreement _ member

/-- Every pop CAS annotation carries the popped node's fixed payload. -/
theorem payload_of_popCas
    {candidate : RC11.Candidate α}
    (contract : ClientContract candidate)
    {id thread operation expected}
    {value : α}
    {next observed : Ptr}
    {succeeded : Bool}
    (member :
      TraceEvent.atomic
          ⟨id,
            .popCas thread operation expected value
              next observed succeeded⟩ ∈
        candidate.trace) :
    candidate.payload expected = value := by
  simpa [PayloadAgrees] using
    contract.payloadAgreement _ member

/--
Every selected immutable-link read has a successful push publisher in its
strict trace prefix, with exactly the payload and link read by the pop.
-/
theorem readNext_hasPriorPublisher
    {candidate : RC11.Candidate α}
    (contract : ClientContract candidate)
    (leading trailing : List (TraceEvent α))
    (thread : ThreadId)
    (operation : OperationId)
    (node : NodeId)
    (next : Ptr)
    (shape :
      candidate.trace =
        leading ++
          .readNext thread operation node next :: trailing) :
    ∃ id publisherThread publisherOperation,
      TraceEvent.atomic
          ⟨id,
            .pushCas publisherThread publisherOperation
              node (candidate.payload node)
              next next true⟩ ∈
        leading :=
  contract.immutableNextReads
    leading trailing thread operation node next shape

end ClientContract

/-!
## Projection of unique client identities and node reservations

These lemmas deliberately accept equality of finite projections.  The concrete
source frontend instantiates them with its chronology-preserving `List.map`.
-/

theorem sourceSkeleton_of_projection
    {candidate : RC11.Candidate α}
    (contract : ClientContract candidate)
    {initial : TreiberRA.State α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (locallyValid :
      TreiberRC11.Interleaving.LocallyValid skeleton)
    (operationProjection :
      TreiberRC11.Interleaving.invocationOperations
          skeleton.labels =
        invocationIds candidate.trace)
    (reservationProjection :
      TreiberRC11.Interleaving.pushReservations
          skeleton.labels =
        pushNodes candidate.trace)
    (initialFresh :
      ∀ node : NodeId, initial.heap node = none) :
    TreiberRC11.Interleaving.SourceSkeleton initial skeleton where
  toLocallyValid :=
    locallyValid
  operationIdsNodup := by
    rw [operationProjection]
    exact contract.invocationIdsNodup
  reservationsNodup := by
    rw [reservationProjection]
    exact contract.pushNodesNodup
  reservationsFresh := by
    intro reserved _
    exact initialFresh reserved

/-! ## Independent client history -/

/-- Project an independent trace event to its abstract client-history event. -/
def clientHistoryEvent?
    (payload : NodeId → α) :
    TraceEvent α →
      Option (HerlihyWing.HistoryEvent α)
  | .invokePush thread operation _ value =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .push value
      })
  | .invokePop thread operation =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .pop
      })
  | .invokeIsEmpty thread operation =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .isEmpty
      })
  | .respondPush thread operation =>
      some (.respond {
        thread := thread
        id := operation
        response := .pushed
      })
  | .respondPop thread operation .null =>
      some (.respond {
        thread := thread
        id := operation
        response := .popped none
      })
  | .respondPop thread operation (.node node) =>
      some (.respond {
        thread := thread
        id := operation
        response := .popped (some (payload node))
      })
  | .respondIsEmpty thread operation result =>
      some (.respond {
        thread := thread
        id := operation
        response := .checkedEmpty result
      })
  | .writeNext ..
  | .readNext ..
  | .atomic .. =>
      none

/-- Client invocation/response history in independent source chronology. -/
def clientHistory
    (candidate : RC11.Candidate α) :
    HerlihyWing.History α :=
  candidate.trace.filterMap
    (clientHistoryEvent? candidate.payload)

/-- The concrete source projection commutes with client-history extraction. -/
@[simp] theorem sourceHistoryEvent?_toOwnedLabel
    (payload : NodeId → α)
    (event : TraceEvent α) :
    TreiberRC11.sourceHistoryEvent?
        (event.toOwnedLabel payload) =
      clientHistoryEvent? payload event := by
  cases event with
  | respondPop thread operation result =>
      cases result <;>
        rfl
  | _ =>
      rfl

/-- Thread/operation key retained by a target completed operation. -/
def completedKey
    (entry : HerlihyWing.IdentifiedCompleted α) :
    ClientOperation :=
  (entry.thread, entry.id)

/-- Exact target metadata carried by one independent atomic occurrence. -/
private def occurrenceMetadata
    (sourceOccurrence : AtomicOccurrence α) :
    TreiberRC11.AtomicSourceMetadata α where
  thread :=
    sourceOccurrence.action.thread
  operation :=
    sourceOccurrence.action.operation
  action :=
    sourceOccurrence.action.toTarget

/--
Canonical occurrence identifiers make target metadata lookup recover the exact
source occurrence, including its operation identifier.
-/
private theorem findAtomicSourceMetadata?_projectedOccurrence
    [DecidableEq α]
    (payload : NodeId → α)
    (trace : List (TraceEvent α))
    (next : EventId)
    (canonical :
      (trace.filterMap RC11.atomOfTraceEvent?).map
          RC11.Atom.id =
        List.range' next
          (trace.filterMap RC11.atomOfTraceEvent?).length)
    {sourceOccurrence : AtomicOccurrence α}
    (member :
      TraceEvent.atomic sourceOccurrence ∈ trace) :
    TreiberRC11.findAtomicSourceMetadata?
        next
        (TreiberRC11.atomicSourceMetadata
          (projectedOwnedLabels payload trace))
        (RC11.Atom.occurrence sourceOccurrence).toTarget =
      some (occurrenceMetadata sourceOccurrence) := by
  induction trace generalizing next with
  | nil =>
      simp at member
  | cons event rest inductionHypothesis =>
      cases event with
      | invokePush =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | invokePop =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | invokeIsEmpty =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | writeNext =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | readNext =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | atomic headOccurrence =>
          rcases headOccurrence with ⟨headId, headAction⟩
          have canonicalShape :
              headId = next ∧
                (rest.filterMap RC11.atomOfTraceEvent?).map
                    RC11.Atom.id =
                  List.range' (next + 1)
                    (rest.filterMap
                      RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?, RC11.Atom.id,
              List.range'_succ] using canonical
          rcases canonicalShape with
            ⟨headIdShape, restCanonical⟩
          have memberShape :
              sourceOccurrence =
                  (⟨headId, headAction⟩ :
                    AtomicOccurrence α) ∨
                TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          rcases memberShape with sameOccurrence | restMember
          · subst sourceOccurrence
            subst headId
            simp [projectedOwnedLabels,
              TreiberRC11.atomicSourceMetadata,
              TreiberRC11.atomicSourceMetadata?,
              TreiberRC11.findAtomicSourceMetadata?,
              TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel,
              TraceEvent.thread, AtomicAction.thread,
              occurrenceMetadata, RC11.Atom.toTarget]
          · have atomMember :
                RC11.Atom.occurrence sourceOccurrence ∈
                  rest.filterMap RC11.atomOfTraceEvent? :=
              List.mem_filterMap.mpr
                ⟨.atomic sourceOccurrence, restMember,
                  by simp [RC11.atomOfTraceEvent?]⟩
            have identifierMember :
                sourceOccurrence.id ∈
                  (rest.filterMap RC11.atomOfTraceEvent?).map
                    RC11.Atom.id :=
              List.mem_map.mpr
                ⟨.occurrence sourceOccurrence, atomMember, rfl⟩
            rw [restCanonical] at identifierMember
            have lowerBound :
                next + 1 ≤ sourceOccurrence.id :=
              (List.mem_range'_1.mp identifierMember).1
            have differentEvent :
                TreiberRC11.Event.mk next
                    (.algorithm headAction.toTarget) ≠
                  (RC11.Atom.occurrence
                    sourceOccurrence).toTarget := by
              intro sameEvent
              have sameId :=
                congrArg TreiberRC11.Event.id sameEvent
              have strict :
                  next < sourceOccurrence.id :=
                Nat.lt_of_lt_of_le
                  (Nat.lt_succ_self next) lowerBound
              have identifierShape :
                  next = sourceOccurrence.id := by
                simpa [RC11.Atom.toTarget] using sameId
              rw [identifierShape] at strict
              exact (Nat.lt_irrefl _ strict).elim
            have later :=
              inductionHypothesis
                (next + 1) restCanonical restMember
            subst headId
            have metadataShape :
                TreiberRC11.atomicSourceMetadata
                    (projectedOwnedLabels payload
                      (TraceEvent.atomic
                          ⟨next, headAction⟩ :: rest)) =
                  occurrenceMetadata
                      (⟨next, headAction⟩ :
                        AtomicOccurrence α) ::
                    TreiberRC11.atomicSourceMetadata
                      (projectedOwnedLabels payload rest) := by
              simp [projectedOwnedLabels,
                TreiberRC11.atomicSourceMetadata,
                TreiberRC11.atomicSourceMetadata?,
                TraceEvent.toOwnedLabel,
                TraceEvent.toTargetLabel, TraceEvent.thread,
                AtomicAction.thread, occurrenceMetadata]
            rw [metadataShape]
            rw [TreiberRC11.findAtomicSourceMetadata?]
            simp only [occurrenceMetadata]
            rw [if_neg differentEvent]
            exact later
      | respondPush =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | respondPop =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember
      | respondIsEmpty =>
          have restMember :
              TraceEvent.atomic sourceOccurrence ∈ rest := by
            simpa using member
          have restCanonical :
              (rest.filterMap RC11.atomOfTraceEvent?).map
                  RC11.Atom.id =
                List.range' next
                  (rest.filterMap
                    RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?] using canonical
          simpa [projectedOwnedLabels,
            TreiberRC11.atomicSourceMetadata,
            TreiberRC11.atomicSourceMetadata?,
            TraceEvent.toOwnedLabel, TraceEvent.toTargetLabel] using
              inductionHypothesis next restCanonical restMember

/-- The logical initializer never selects source atomic metadata. -/
private theorem findAtomicSourceMetadata?_initial
    [DecidableEq α]
    (next : EventId)
    (metadata : List (TreiberRC11.AtomicSourceMetadata α)) :
    TreiberRC11.findAtomicSourceMetadata?
        next metadata
        (TreiberRC11.EventGraph.Skeleton.initialEvent :
          TreiberRC11.Event α) =
      none := by
  induction metadata generalizing next with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      simp [TreiberRC11.findAtomicSourceMetadata?,
        TreiberRC11.EventGraph.Skeleton.initialEvent]

/--
Exact metadata lookup on a concrete projected atom recovers precisely the
independent thread/operation commit key.
-/
theorem identifiedEventCommit?_atom_toTarget_key
    [DecidableEq α]
    (execution : SupportedExecution α)
    (atom : RC11.Atom α)
    (member : atom ∈ execution.candidate.atoms) :
    (TreiberRC11.identifiedEventCommit?
        execution.toControlledSource.skeleton
        atom.toTarget).map completedKey =
      atom.commitOperation? := by
  cases atom with
  | initial =>
      simp [TreiberRC11.identifiedEventCommit?,
        RC11.Atom.toTarget,
        findAtomicSourceMetadata?_initial,
        RC11.Atom.commitOperation?]
  | occurrence sourceOccurrence =>
      have traceMember :
          TraceEvent.atomic sourceOccurrence ∈
            execution.candidate.trace :=
        execution.candidate.atomic_mem_trace_of_mem_atoms
          member
      have canonicalShape :
          0 ::
              execution.candidate.nonInitialAtoms.map
                RC11.Atom.id =
            0 ::
              (List.range
                execution.candidate.nonInitialAtoms.length).map
                  Nat.succ := by
        simpa [RC11.Candidate.atomIds,
          RC11.Candidate.atoms, RC11.Atom.id,
          List.range_succ_eq_map] using
            execution.rc11.atomIdsCanonical
      have tailIds :
          execution.candidate.nonInitialAtoms.map
              RC11.Atom.id =
            (List.range
              execution.candidate.nonInitialAtoms.length).map
                Nat.succ :=
        (List.cons.inj canonicalShape).2
      have tailCanonical :
          (execution.candidate.trace.filterMap
              RC11.atomOfTraceEvent?).map RC11.Atom.id =
            List.range' 1
              (execution.candidate.trace.filterMap
                RC11.atomOfTraceEvent?).length := by
        have rangeShape :
            execution.candidate.nonInitialAtoms.map
                RC11.Atom.id =
              List.range' 1
                execution.candidate.nonInitialAtoms.length := by
          rw [List.range'_eq_map_range]
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            tailIds
        simpa [RC11.Candidate.nonInitialAtoms] using rangeShape
      have lookup :
          TreiberRC11.findAtomicSourceMetadata?
              1
              (TreiberRC11.atomicSourceMetadata
                execution.toControlledSource.skeleton.labels)
              (RC11.Atom.occurrence
                sourceOccurrence).toTarget =
            some (occurrenceMetadata sourceOccurrence) := by
        simpa using
          findAtomicSourceMetadata?_projectedOccurrence
            execution.candidate.payload
            execution.candidate.trace 1
            tailCanonical traceMember
      rw [TreiberRC11.identifiedEventCommit?, lookup]
      simpa [TreiberRC11.metadataCommit?,
        occurrenceMetadata, completedKey,
        TreiberRC11.identifiedCommit, Function.comp_def] using
          (RC11.Atom.projectedCommitKey?_eq_commitOperation?
            (RC11.Atom.occurrence sourceOccurrence))

private theorem filterMap_map_eq
    {items : List β}
    {project : β → γ}
    {left : γ → Option δ}
    {right : β → Option δ}
    (commutes :
      ∀ item,
        item ∈ items →
          left (project item) = right item) :
    (items.map project).filterMap left =
      items.filterMap right := by
  induction items generalizing left right with
  | nil =>
      rfl
  | cons item rest inductionHypothesis =>
      have head :=
        commutes item (by simp)
      have tail :=
        inductionHypothesis
          (fun later member =>
            commutes later (by simp [member]))
      simp only [List.map_cons, List.filterMap_cons, head, tail]

/--
Scheduling the concrete projected atoms preserves exactly the independent
committed-operation keys, in the chosen compatible order.

Only equality of the controlled source skeleton is required from the eventual
atomic-execution construction; relation and allocator fields are irrelevant to
this metadata statement.
-/
theorem scheduledOperations_keys_toTarget
    [DecidableEq α]
    (execution : SupportedExecution α)
    {initial : TreiberRA.State α}
    (atomicExecution :
      TreiberRC11.SourceAtomicExecution initial)
    (sourceSkeleton :
      atomicExecution.source.skeleton =
        execution.toControlledSource.skeleton) :
    (TreiberRC11.scheduledOperations atomicExecution
        (execution.order.schedule.map
          RC11.Atom.toTarget)).map completedKey =
      committedOperations execution.order.schedule := by
  unfold TreiberRC11.scheduledOperations committedOperations
  rw [sourceSkeleton, List.map_filterMap]
  apply filterMap_map_eq
  intro atom scheduleMember
  have candidateMember :
      atom ∈ execution.candidate.atoms :=
    (execution.order.exactAtoms.mem_iff).mp scheduleMember
  exact identifiedEventCommit?_atom_toTarget_key
    execution atom candidateMember

/--
Any chronology-preserving source-label projection whose per-event history
projection commutes yields exactly the target `sourceHistory`.
-/
theorem sourceHistory_eq_clientHistory_of_projection
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (project :
      TraceEvent α →
        TreiberRC11.EventGraph.OwnedLabel α)
    (labelsProjection :
      skeleton.labels = candidate.trace.map project)
    (historyProjection :
      ∀ event,
        event ∈ candidate.trace →
          TreiberRC11.sourceHistoryEvent? (project event) =
            clientHistoryEvent? candidate.payload event) :
    TreiberRC11.sourceHistory skeleton =
      clientHistory candidate := by
  unfold TreiberRC11.sourceHistory clientHistory
  rw [labelsProjection]
  exact filterMap_map_eq historyProjection

/--
The controlled source constructed by the concrete source frontend has exactly
the independently defined invocation/response history.
-/
theorem sourceHistory_toControlledSource
    (execution : SupportedExecution α) :
    TreiberRC11.sourceHistory
        execution.toControlledSource.skeleton =
      clientHistory execution.candidate := by
  apply sourceHistory_eq_clientHistory_of_projection
    (project :=
      fun event =>
        event.toOwnedLabel execution.candidate.payload)
  · exact execution.toControlledSource_labels
  · intro event _
    exact sourceHistoryEvent?_toOwnedLabel
      execution.candidate.payload event

/-! ## Recovering source real time from the filtered history -/

private theorem before_cons_iff
    {first second head : β}
    {rest : List β} :
    HerlihyWing.Before first second (head :: rest) ↔
      (head = first ∧ second ∈ rest) ∨
        HerlihyWing.Before first second rest := by
  constructor
  · rintro ⟨leading, between, trailing, shape⟩
    cases leading with
    | nil =>
        change
          head :: rest =
            first :: between ++ second :: trailing
          at shape
        have headShape := (List.cons.inj shape).1
        have restShape := (List.cons.inj shape).2
        exact Or.inl ⟨headShape, by
          rw [restShape]
          simp⟩
    | cons leadingHead remaining =>
        change
          head :: rest =
            leadingHead ::
              remaining ++ first :: between ++ second :: trailing
          at shape
        have restShape := (List.cons.inj shape).2
        exact Or.inr
          ⟨remaining, between, trailing, restShape⟩
  · rintro (⟨rfl, secondMember⟩ | ordered)
    · obtain ⟨between, trailing, restShape⟩ :=
        List.append_of_mem secondMember
      exact ⟨[], between, trailing, by
        simp [restShape]⟩
    · obtain ⟨leading, between, trailing, restShape⟩ :=
        ordered
      exact ⟨head :: leading, between, trailing, by
        simp [restShape]⟩

private theorem occursBefore_cons
    (head : β)
    {first second : β}
    {rest : List β}
    (before : OccursBefore first second rest) :
    OccursBefore first second (head :: rest) := by
  obtain ⟨leading, between, trailing, shape⟩ :=
    before
  exact ⟨head :: leading, between, trailing, by
    simp [shape]⟩

/-- Order in a filtered list has ordered preimages in the original list. -/
private theorem exists_preimages_of_before_filterMap
    {items : List β}
    {project : β → Option γ}
    {first second : γ}
    (before :
      HerlihyWing.Before first second
        (items.filterMap project)) :
    ∃ sourceFirst sourceSecond,
      project sourceFirst = some first ∧
        project sourceSecond = some second ∧
        OccursBefore sourceFirst sourceSecond items := by
  induction items with
  | nil =>
      simp [HerlihyWing.Before] at before
  | cons item rest inductionHypothesis =>
      cases projected : project item with
      | none =>
          simp only [List.filterMap_cons, projected] at before
          obtain ⟨sourceFirst, sourceSecond,
              firstProjects, secondProjects, ordered⟩ :=
            inductionHypothesis before
          exact ⟨sourceFirst, sourceSecond,
            firstProjects, secondProjects,
            occursBefore_cons item ordered⟩
      | some output =>
          simp only [List.filterMap_cons, projected] at before
          rcases (before_cons_iff.mp before) with
            headCase | tailCase
          · rcases headCase with ⟨outputShape, secondMember⟩
            obtain ⟨sourceSecond, sourceMember,
                secondProjects⟩ :=
              List.mem_filterMap.mp secondMember
            obtain ⟨between, trailing, restShape⟩ :=
              List.append_of_mem sourceMember
            refine ⟨item, sourceSecond, ?_, secondProjects, ?_⟩
            · simpa [outputShape] using projected
            · exact ⟨[], between, trailing, by
                simp [restShape]⟩
          · obtain ⟨sourceFirst, sourceSecond,
                firstProjects, secondProjects, ordered⟩ :=
              inductionHypothesis tailCase
            exact ⟨sourceFirst, sourceSecond,
              firstProjects, secondProjects,
              occursBefore_cons item ordered⟩

private theorem response_key_of_history_projection
    (payload : NodeId → α)
    (event : TraceEvent α)
    (entry : HerlihyWing.IdentifiedCompleted α)
    (projects :
      clientHistoryEvent? payload event =
        some (.respond entry.returned)) :
    responseOperation? event =
      some (completedKey entry) := by
  cases event <;>
    simp [clientHistoryEvent?, responseOperation?,
      completedKey, HerlihyWing.IdentifiedCompleted.returned] at projects ⊢
  all_goals
    try { cases projects }
  all_goals
    try { rename_i result; cases result <;> simp_all }

private theorem invocation_key_of_history_projection
    (payload : NodeId → α)
    (event : TraceEvent α)
    (entry : HerlihyWing.IdentifiedCompleted α)
    (projects :
      clientHistoryEvent? payload event =
        some (.invoke entry.invocation)) :
    invocationOperation? event =
      some (completedKey entry) := by
  cases event with
  | invokePush thread operation node value =>
      simp [clientHistoryEvent?, invocationOperation?,
        completedKey, HerlihyWing.IdentifiedCompleted.invocation]
          at projects ⊢
      exact ⟨projects.1, projects.2.1⟩
  | invokePop thread operation =>
      simp [clientHistoryEvent?, invocationOperation?,
        completedKey, HerlihyWing.IdentifiedCompleted.invocation]
          at projects ⊢
      exact ⟨projects.1, projects.2.1⟩
  | invokeIsEmpty thread operation =>
      simp [clientHistoryEvent?, invocationOperation?,
        completedKey, HerlihyWing.IdentifiedCompleted.invocation]
          at projects ⊢
      exact ⟨projects.1, projects.2.1⟩
  | respondPop thread operation result =>
      cases result <;> simp [clientHistoryEvent?] at projects
  | writeNext | readNext | atomic
  | respondPush | respondIsEmpty =>
      simp [clientHistoryEvent?] at projects

/--
A classical cross-thread return-before-invocation edge in the independent
history is exactly backed by a source-trace `RealTimeEdge`.
-/
theorem realTimeEdge_of_clientHistory
    {candidate : RC11.Candidate α}
    {first second : HerlihyWing.IdentifiedCompleted α}
    (differentThread :
      first.thread ≠ second.thread)
    (realTime :
      HerlihyWing.RealTimePrecedes
        (clientHistory candidate) first second) :
    RealTimeEdge candidate.trace
      (completedKey first) (completedKey second) := by
  obtain ⟨response, invocation,
      responseProjects, invocationProjects, ordered⟩ :=
    exists_preimages_of_before_filterMap realTime
  refine ⟨differentThread, response, invocation, ?_, ?_, ordered⟩
  · exact response_key_of_history_projection
      candidate.payload response first responseProjects
  · exact invocation_key_of_history_projection
      candidate.payload invocation second invocationProjects

/-! ## Lifting the independent compatible order to target real time -/

private theorem eq_of_mem_of_map_nodup
    {items : List β}
    {project : β → γ}
    (projectedNodup : (items.map project).Nodup)
    {left right : β}
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameProjection : project left = project right) :
    left = right := by
  induction items with
  | nil =>
      simp at leftMember
  | cons first rest inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp projectedNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · subst left
        rcases rightMember with rightHead | rightTail
        · exact rightHead.symm
        · exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨right, rightTail, sameProjection.symm⟩)
      · rcases rightMember with rightHead | rightTail
        · subst right
          exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨left, leftTail, sameProjection⟩)
        · exact inductionHypothesis nodupParts.2
            leftTail rightTail

/--
The target schedule cannot contain two completed operations with the same
thread/operation key.  This follows from source invocation uniqueness and the
schedule permutation theorem; it is not an extra frontend assumption.
-/
theorem scheduledOperations_keyInjective
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : TreiberRC11.SourceAtomicExecution initial)
    {schedule : List (TreiberRC11.Event α)}
    (respects :
      TreiberRC11.RespectsGraph
        execution.relations.graph schedule)
    {left right : HerlihyWing.IdentifiedCompleted α}
    (leftMember :
      left ∈ TreiberRC11.scheduledOperations execution schedule)
    (rightMember :
      right ∈ TreiberRC11.scheduledOperations execution schedule)
    (sameKey : completedKey left = completedKey right) :
    left = right := by
  have sourceIdsNodup :
      ((TreiberRC11.sourceCommittedOperations
          execution.source.skeleton).map
        HerlihyWing.IdentifiedCompleted.id).Nodup :=
    execution.source.valid.sourceCompletion.operationIdsNodup
  have scheduledIdsNodup :
      ((TreiberRC11.scheduledOperations execution schedule).map
        HerlihyWing.IdentifiedCompleted.id).Nodup := by
    exact
      ((TreiberRC11.sourceCommittedOperations_perm_scheduledOperations
          execution respects).map
        HerlihyWing.IdentifiedCompleted.id).nodup
          sourceIdsNodup
  apply eq_of_mem_of_map_nodup
      scheduledIdsNodup leftMember rightMember
  exact congrArg Prod.snd sameKey

private theorem mem_of_occursBefore_left
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items) :
    first ∈ items := by
  obtain ⟨leading, between, trailing, shape⟩ := before
  rw [shape]
  simp

private theorem mem_of_occursBefore_right
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items) :
    second ∈ items := by
  obtain ⟨leading, between, trailing, shape⟩ := before
  rw [shape]
  simp

private theorem before_map
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items)
    (project : β → γ) :
    HerlihyWing.Before
      (project first) (project second)
      (items.map project) := by
  obtain ⟨leading, between, trailing, shape⟩ := before
  refine ⟨leading.map project, between.map project,
    trailing.map project, ?_⟩
  simp [shape]

private theorem before_of_key_order
    {operations : List (HerlihyWing.IdentifiedCompleted α)}
    {first second : HerlihyWing.IdentifiedCompleted α}
    (firstMember : first ∈ operations)
    (secondMember : second ∈ operations)
    (keyInjective :
      ∀ {left right},
        left ∈ operations →
        right ∈ operations →
        completedKey left = completedKey right →
        left = right)
    (ordered :
      HerlihyWing.Before
        (completedKey first) (completedKey second)
        (operations.map completedKey)) :
    HerlihyWing.Before first second operations := by
  let asFilter :
      HerlihyWing.IdentifiedCompleted α →
        Option ClientOperation :=
    fun entry => some (completedKey entry)
  have filterShape :
      operations.filterMap asFilter =
        operations.map completedKey := by
    simp [asFilter]
  have filteredOrder :
      HerlihyWing.Before
        (completedKey first) (completedKey second)
        (operations.filterMap asFilter) := by
    simpa [filterShape] using ordered
  obtain ⟨sourceFirst, sourceSecond,
      firstProjects, secondProjects, sourceOrder⟩ :=
    exists_preimages_of_before_filterMap filteredOrder
  have sourceFirstMember :=
    mem_of_occursBefore_left sourceOrder
  have sourceSecondMember :=
    mem_of_occursBefore_right sourceOrder
  have firstKey :
      completedKey sourceFirst = completedKey first := by
    simpa [asFilter] using Option.some.inj firstProjects
  have secondKey :
      completedKey sourceSecond = completedKey second := by
    simpa [asFilter] using Option.some.inj secondProjects
  have sourceFirstShape :
      sourceFirst = first :=
    keyInjective sourceFirstMember firstMember firstKey
  have sourceSecondShape :
      sourceSecond = second :=
    keyInjective sourceSecondMember secondMember secondKey
  subst sourceFirst
  subst sourceSecond
  exact sourceOrder

/--
The independent client-compatible order discharges the target's exact
cross-thread real-time obligation once history and scheduled-operation
projections are identified.
-/
theorem crossThreadRealTimeCompatible_of_projection
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    (order : ClientCompatibleOrder candidate)
    {initial : TreiberRA.State α}
    (execution :
      TreiberRC11.SourceAtomicExecution initial)
    (targetSchedule : List (TreiberRC11.Event α))
    (historyProjection :
      TreiberRC11.sourceHistory
          execution.source.skeleton =
        clientHistory candidate)
    (operationsProjection :
      (TreiberRC11.scheduledOperations
          execution targetSchedule).map completedKey =
        committedOperations order.schedule)
    (keyInjective :
      ∀ {left right},
        left ∈
            TreiberRC11.scheduledOperations
              execution targetSchedule →
        right ∈
            TreiberRC11.scheduledOperations
              execution targetSchedule →
        completedKey left = completedKey right →
        left = right) :
    TreiberRC11.CrossThreadRealTimeCompatible
      execution targetSchedule := by
  intro first second firstMember secondMember
      differentThread targetRealTime
  let targetOperations :=
    TreiberRC11.scheduledOperations execution targetSchedule
  have firstKeyMember :
      completedKey first ∈ committedOperations order.schedule := by
    rw [← operationsProjection]
    exact List.mem_map.mpr ⟨first, firstMember, rfl⟩
  have secondKeyMember :
      completedKey second ∈ committedOperations order.schedule := by
    rw [← operationsProjection]
    exact List.mem_map.mpr ⟨second, secondMember, rfl⟩
  have independentRealTime :
      RealTimeEdge candidate.trace
        (completedKey first) (completedKey second) := by
    apply realTimeEdge_of_clientHistory differentThread
    rw [← historyProjection]
    exact targetRealTime
  have independentOrder :=
    order.realTime firstKeyMember secondKeyMember
      independentRealTime
  have targetKeyOrder :
      HerlihyWing.Before
        (completedKey first) (completedKey second)
        (targetOperations.map completedKey) := by
    rw [operationsProjection]
    exact independentOrder
  exact before_of_key_order
    firstMember secondMember keyInjective targetKeyOrder

end WeakMemory.TreiberC11V1.ClientFrontend
