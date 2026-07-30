import WeakMemory.TreiberC11V1Execution
import WeakMemory.TreiberInterleavingCheck
import WeakMemory.TreiberModelInitial

namespace WeakMemory.TreiberC11V1

/-!
# Source-control refinement into the checked Treiber model

This module translates only the independent source trace.  It does not inspect
RF/MO data, relation schedules, generated-event certificates, or validator
acceptance while defining the projection.

The local refinement uses `RC11.TracePayloadConsistent` only where the target
control-flow state records an abstract payload that the source state represents
by a returned node pointer.
-/

namespace Ptr

/-- Translate the independent pointer representation to the target node ID. -/
def toTarget : Ptr → Option TreiberRA.NodeId
  | Ptr.null =>
      none
  | Ptr.node nodeId =>
      some nodeId

@[simp] theorem toTarget_null :
    Ptr.null.toTarget = none :=
  rfl

@[simp] theorem toTarget_node
    (node : NodeId) :
    (Ptr.node node).toTarget = some node :=
  rfl

end Ptr

namespace AtomicAction

/-- Translate one independent source atomic into the target Treiber action. -/
def toTarget : AtomicAction α → TreiberRA.Action α
  | .pushLoad thread _ observed =>
      .pushLoad thread observed.toTarget
  | .pushCas thread _ node value expected _observed true =>
      .pushSuccess thread node value expected.toTarget
  | .pushCas thread _ node value expected observed false =>
      .pushFailure thread node value expected.toTarget observed.toTarget
  | .popLoad thread _ observed =>
      .popLoad thread observed.toTarget
  | .popCas thread _ expected value next _observed true =>
      .popSuccess thread expected value next.toTarget
  | .popCas thread _ expected _value _next observed false =>
      .popFailure thread (some expected) observed.toTarget
  | .isEmptyLoad thread _ observed =>
      .isEmptyLoad thread observed.toTarget

/-- Atomic translation preserves the owning thread exactly. -/
@[simp] theorem toTarget_thread
    (action : AtomicAction α) :
    TreiberRC11.ControlFlow.actionThread action.toTarget =
      action.thread := by
  cases action <;>
    first
    | rfl
    | rename_i succeeded
      cases succeeded <;> rfl

/--
The value observed by a successful compare-exchange is the value that its
successful target action records as read.

Failed compare-exchanges already retain their actual observed value in the
target action, so they impose no side condition here.
-/
def SuccessfulReadConsistent : AtomicAction α → Prop
  | .pushCas _ _ _ _ expected observed true =>
      observed = expected
  | .popCas _ _ expected _ _ observed true =>
      observed = .node expected
  | _ =>
      True

end AtomicAction

namespace RC11.Atom

/--
Translate one independent atom to its target graph event.

The independent identifier is retained.  A later carrier theorem derives that
these identifiers are exactly the fresh target numbering.
-/
def toTarget : RC11.Atom α → TreiberRC11.Event α
  | @RC11.Atom.initial _ =>
      TreiberRC11.EventGraph.Skeleton.initialEvent
  | @RC11.Atom.occurrence _ sourceOccurrence =>
      TreiberRC11.Event.mk sourceOccurrence.id
        (.algorithm
          (AtomicAction.toTarget sourceOccurrence.action))

/-- Successful-CAS read consistency lifted from actions to atoms. -/
def SuccessfulReadConsistent : RC11.Atom α → Prop
  | .initial =>
      True
  | .occurrence sourceOccurrence =>
      sourceOccurrence.action.SuccessfulReadConsistent

@[simp] theorem toTarget_initial :
    (RC11.Atom.initial : RC11.Atom α).toTarget =
      TreiberRC11.EventGraph.Skeleton.initialEvent :=
  rfl

@[simp] theorem toTarget_occurrence
    (occurrence : AtomicOccurrence α) :
    (RC11.Atom.occurrence occurrence).toTarget =
      TreiberRC11.Event.mk occurrence.id
        (.algorithm occurrence.action.toTarget) :=
  rfl

/-- Atom translation preserves identifiers unconditionally. -/
@[simp] theorem toTarget_id
    (atom : RC11.Atom α) :
    atom.toTarget.id = atom.id := by
  cases atom <;> rfl

/-- Atom translation preserves the optional owning thread. -/
@[simp] theorem toTarget_thread?
    (atom : RC11.Atom α) :
    atom.toTarget.thread? = atom.thread? := by
  cases atom with
  | initial =>
      rfl
  | occurrence occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        first
        | rfl
        | rename_i succeeded
          cases succeeded <;> rfl

/-- Atom translation preserves the source memory order. -/
@[simp] theorem toTarget_order
    (atom : RC11.Atom α) :
    atom.toTarget.order = atom.order := by
  cases atom with
  | initial =>
      rfl
  | occurrence occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        first
        | rfl
        | rename_i succeeded
          cases succeeded <;> rfl

/-- Atom translation preserves every written head value. -/
@[simp] theorem toTarget_writtenValue
    (atom : RC11.Atom α) :
    atom.toTarget.writtenValue =
      atom.writtenValue.map Ptr.toTarget := by
  cases atom with
  | initial =>
      rfl
  | occurrence occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        first
        | rfl
        | rename_i succeeded
          cases succeeded <;> rfl

/--
Atom translation preserves the read head value once successful-CAS source
consistency is known.
-/
theorem toTarget_readValue
    (atom : RC11.Atom α)
    (consistent : atom.SuccessfulReadConsistent) :
    atom.toTarget.readValue =
      atom.readValue.map Ptr.toTarget := by
  cases atom with
  | initial =>
      rfl
  | occurrence occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        first
        | rfl
        | rename_i succeeded
          cases succeeded <;>
            simp_all [RC11.Atom.SuccessfulReadConsistent,
              AtomicAction.SuccessfulReadConsistent,
              AtomicAction.toTarget, RC11.Atom.readValue,
              AtomicAction.readValue,
              Ptr.toTarget, TreiberRC11.Event.readValue]

/-- Atom translation preserves successful-RMW classification. -/
@[simp] theorem toTarget_isRMW :
    ∀ (atom : RC11.Atom α),
      atom.toTarget.IsRMW ↔ atom.IsRMW
  | .initial =>
      by
        simp [RC11.Atom.toTarget,
          TreiberRC11.EventGraph.Skeleton.initialEvent,
          TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
          RC11.Atom.isRMW]
  | .occurrence ⟨id, action⟩ => by
      cases action with
      | pushLoad =>
          simp [RC11.Atom.toTarget, AtomicAction.toTarget,
            TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
            RC11.Atom.isRMW, AtomicAction.isRMW]
      | pushCas thread operation node value expected observed
          succeeded =>
          cases succeeded <;>
            simp [RC11.Atom.toTarget, AtomicAction.toTarget,
              TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
              RC11.Atom.isRMW, AtomicAction.isRMW]
      | popLoad =>
          simp [RC11.Atom.toTarget, AtomicAction.toTarget,
            TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
            RC11.Atom.isRMW, AtomicAction.isRMW]
      | popCas thread operation expected value next observed
          succeeded =>
          cases succeeded <;>
            simp [RC11.Atom.toTarget, AtomicAction.toTarget,
              TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
              RC11.Atom.isRMW, AtomicAction.isRMW]
      | isEmptyLoad =>
          simp [RC11.Atom.toTarget, AtomicAction.toTarget,
            TreiberRC11.Event.IsRMW, RC11.Atom.IsRMW,
            RC11.Atom.isRMW, AtomicAction.isRMW]

/-- Atom translation preserves initializer classification. -/
@[simp] theorem toTarget_isInitial
    (atom : RC11.Atom α) :
    atom.toTarget.IsInitial ↔ atom.IsInitial := by
  cases atom <;> rfl

/--
The commit key exposed by a translated action is exactly the independent
atom's commit classification.

This is the source-side pointwise fact needed by the later canonical metadata
lookup proof; the abstract commit payload itself is deliberately discarded.
-/
theorem projectedCommitKey?_eq_commitOperation?
    (atom : RC11.Atom α) :
    (match atom with
      | .initial =>
          none
      | .occurrence sourceOccurrence =>
          sourceOccurrence.action.toTarget.commit?.map
            (fun _ =>
              (sourceOccurrence.action.thread,
                sourceOccurrence.action.operation))) =
      atom.commitOperation? := by
  cases atom with
  | initial =>
      rfl
  | occurrence sourceOccurrence =>
      rcases sourceOccurrence with ⟨id, action⟩
      cases action with
      | pushLoad thread operation observed =>
          cases observed <;> rfl
      | pushCas thread operation node value expected observed
          succeeded =>
          cases succeeded <;> rfl
      | popLoad thread operation observed =>
          cases observed <;> rfl
      | popCas thread operation expected value next observed
          succeeded =>
          cases succeeded <;>
            cases observed <;> rfl
      | isEmptyLoad thread operation observed =>
          cases observed <;> rfl

end RC11.Atom

/-- Abstract commit represented by a returned source pointer. -/
def popCommit
    (payload : NodeId → α) :
    Ptr → Treiber.Commit α
  | .null =>
      .popEmpty
  | .node node =>
      .popValue (payload node)

/-- Client-visible response represented by a returned source pointer. -/
def popResponse
    (payload : NodeId → α) :
    Ptr → StackSpec.Response α
  | .null =>
      .popped none
  | .node node =>
      .popped (some (payload node))

namespace LocalState

/--
Translate an independent local source state.

The payload table is needed only for a completed pop, whose source state keeps
the returned node pointer while the target state keeps its abstract commit.
-/
def toTarget
    (payload : NodeId → α) :
    LocalState α → TreiberRC11.ControlFlow.LocalState α
  | .idle =>
      .idle
  | .pushLoading operation node value =>
      .pushLoading operation node value
  | .pushWriting operation node value expected =>
      .pushWriting operation node value expected.toTarget
  | .pushing operation node value expected =>
      .pushing operation node value expected.toTarget
  | .popLoading operation =>
      .popLoading operation
  | .popReading operation observed =>
      .popReading operation observed
  | .popping operation expected _ next =>
      .popping operation expected next.toTarget
  | .checkingEmpty operation =>
      .checkingEmpty operation
  | .returningPush operation value =>
      .returning operation (.push value)
  | .returningPop operation result =>
      .returning operation (popCommit payload result)
  | .returningIsEmpty operation result =>
      .returning operation (.isEmpty result)

end LocalState

namespace TraceEvent

/-- Translate one independent trace event to its target source label. -/
def toTargetLabel
    (payload : NodeId → α) :
    TraceEvent α → TreiberRC11.ControlFlow.Label α
  | .invokePush _ operation node value =>
      .invokePush operation node value
  | .invokePop _ operation =>
      .invokePop operation
  | .invokeIsEmpty _ operation =>
      .invokeIsEmpty operation
  | .writeNext _ operation node next =>
      .writeNext operation node next.toTarget
  | .readNext _ operation node next =>
      .readNext operation node next.toTarget
  | .atomic occurrence =>
      .atomic occurrence.action.operation occurrence.action.toTarget
  | .respondPush _ operation =>
      .respond operation .pushed
  | .respondPop _ operation result =>
      .respond operation (popResponse payload result)
  | .respondIsEmpty _ operation result =>
      .respond operation (.checkedEmpty result)

/-- Package the translated label with its exact certified source owner. -/
def toOwnedLabel
    (payload : NodeId → α)
    (event : TraceEvent α) :
    TreiberRC11.EventGraph.OwnedLabel α where
  thread :=
    event.thread
  label :=
    event.toTargetLabel payload
  owned := by
    cases event with
    | invokePush =>
        trivial
    | invokePop =>
        trivial
    | invokeIsEmpty =>
        trivial
    | writeNext =>
        trivial
    | readNext =>
        trivial
    | atomic occurrence =>
        exact AtomicAction.toTarget_thread occurrence.action
    | respondPush =>
        trivial
    | respondPop =>
        trivial
    | respondIsEmpty =>
        trivial

@[simp] theorem toOwnedLabel_thread
    (payload : NodeId → α)
    (event : TraceEvent α) :
    (event.toOwnedLabel payload).thread = event.thread :=
  rfl

@[simp] theorem toOwnedLabel_label
    (payload : NodeId → α)
    (event : TraceEvent α) :
    (event.toOwnedLabel payload).label =
      event.toTargetLabel payload :=
  rfl

end TraceEvent

namespace SourceFrontend

/-- Target labels in the exact global source-trace order. -/
def projectedLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    List (TreiberRC11.ControlFlow.Label α) :=
  trace.map fun event =>
    event.toTargetLabel payload

/-- Certified target labels in the exact global source-trace order. -/
def projectedOwnedLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    List (TreiberRC11.EventGraph.OwnedLabel α) :=
  trace.map fun event =>
    event.toOwnedLabel payload

/-- Raw target labels obtained by forgetting only ownership proofs. -/
def projectedRawLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    List (TreiberRC11.InterleavingCheck.RawOwnedLabel α) :=
  (projectedOwnedLabels payload trace).map
    TreiberRC11.InterleavingCheck.RawOwnedLabel.ofOwned

/-- The projected owned-label list preserves every owner exactly. -/
@[simp] theorem projectedOwnedLabels_threads
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    (projectedOwnedLabels payload trace).map
        TreiberRC11.EventGraph.OwnedLabel.thread =
      trace.map TraceEvent.thread := by
  simp [projectedOwnedLabels]

/-- The projected owned-label list preserves every translated label exactly. -/
@[simp] theorem projectedOwnedLabels_labels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    (projectedOwnedLabels payload trace).map
        TreiberRC11.EventGraph.OwnedLabel.label =
      projectedLabels payload trace := by
  simp [projectedOwnedLabels, projectedLabels]

/--
Fresh target numbering agrees with independent occurrence identifiers whenever
the independent non-initial identifier list is the corresponding finite range.
-/
private theorem nonInitialAtoms_toTarget_eq_atomicEventsFrom
    (payload : NodeId → α)
    (trace : List (TraceEvent α))
    (next : EventId)
    (canonical :
      (trace.filterMap RC11.atomOfTraceEvent?).map
          RC11.Atom.id =
        List.range' next
          (trace.filterMap RC11.atomOfTraceEvent?).length) :
    (trace.filterMap RC11.atomOfTraceEvent?).map
        RC11.Atom.toTarget =
      TreiberRC11.EventGraph.atomicEventsFrom next
        (projectedOwnedLabels payload trace) := by
  induction trace generalizing next with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases event with
      | invokePush =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | invokePop =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | invokeIsEmpty =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | writeNext =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | readNext =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | atomic sourceOccurrence =>
          rcases sourceOccurrence with ⟨id, action⟩
          have shape :
              id = next ∧
                (rest.filterMap RC11.atomOfTraceEvent?).map
                    RC11.Atom.id =
                  List.range' (next + 1)
                    (rest.filterMap
                      RC11.atomOfTraceEvent?).length := by
            simpa [RC11.atomOfTraceEvent?,
              RC11.Atom.id,
              List.range'_succ] using canonical
          rcases shape with ⟨idShape, restCanonical⟩
          subst id
          simp [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel, RC11.Atom.toTarget,
            TreiberRC11.EventGraph.atomicEventsFrom,
            inductionHypothesis (next + 1) restCanonical]
      | respondPush =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | respondPop =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical
      | respondIsEmpty =>
          simpa [RC11.atomOfTraceEvent?,
            projectedOwnedLabels, TraceEvent.toOwnedLabel,
            TraceEvent.toTargetLabel,
            TreiberRC11.EventGraph.atomicEventsFrom] using
              inductionHypothesis next canonical

end SourceFrontend

open SourceFrontend

/--
Canonical independent atom identifiers are exactly the fresh identifiers of
the graph carrier generated from the projected source trace.
-/
theorem RC11.Candidate.atoms_toTarget_eq_projectedEvents
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate) :
    candidate.atoms.map RC11.Atom.toTarget =
      ({ labels :=
          projectedOwnedLabels candidate.payload candidate.trace } :
        TreiberRC11.EventGraph.Skeleton α).events := by
  have canonicalShape :
      0 ::
          candidate.nonInitialAtoms.map RC11.Atom.id =
        0 ::
          (List.range candidate.nonInitialAtoms.length).map
            Nat.succ := by
    simpa [RC11.Candidate.atomIds, RC11.Candidate.atoms,
      RC11.Atom.id, List.range_succ_eq_map] using
        valid.atomIdsCanonical
  have tailIds :
      candidate.nonInitialAtoms.map RC11.Atom.id =
        (List.range candidate.nonInitialAtoms.length).map
          Nat.succ :=
    (List.cons.inj canonicalShape).2
  have tailCanonical :
      candidate.nonInitialAtoms.map RC11.Atom.id =
        List.range' 1 candidate.nonInitialAtoms.length := by
    rw [List.range'_eq_map_range]
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using tailIds
  simp only [RC11.Candidate.atoms, List.map_cons,
    RC11.Atom.toTarget_initial,
    TreiberRC11.EventGraph.Skeleton.events,
    List.cons.injEq, true_and]
  exact
    SourceFrontend.nonInitialAtoms_toTarget_eq_atomicEventsFrom
      candidate.payload candidate.trace 1
      (by
        simpa [RC11.Candidate.nonInitialAtoms] using
          tailCanonical)

/-- Membership of a non-initial atom reflects exact source-trace membership. -/
theorem RC11.Candidate.atomic_mem_trace_of_mem_atoms
    {candidate : RC11.Candidate α}
    {sourceOccurrence : AtomicOccurrence α}
    (member :
      RC11.Atom.occurrence sourceOccurrence ∈
        candidate.atoms) :
    TraceEvent.atomic sourceOccurrence ∈ candidate.trace := by
  simp only [RC11.Candidate.atoms, List.mem_cons] at member
  rcases member with impossible | nonInitial
  · contradiction
  · rw [RC11.Candidate.nonInitialAtoms,
      List.mem_filterMap] at nonInitial
    obtain ⟨event, eventMember, projects⟩ := nonInitial
    cases event <;>
      simp [RC11.atomOfTraceEvent?] at projects
    rename_i projectedOccurrence
    cases projects
    exact eventMember

/-- A value below the range bound occurs at its own range index. -/
private theorem idxOf_range_of_lt
    {value bound : Nat}
    (less : value < bound) :
    (List.range bound).idxOf value = value := by
  induction bound with
  | zero =>
      omega
  | succ previous inductionHypothesis =>
      rw [List.range_succ, List.idxOf_append]
      by_cases earlier : value < previous
      · simp [List.mem_range.mpr earlier,
          inductionHypothesis earlier]
      · have same : value = previous := by
          omega
        subst value
        simp

/-- A duplicate-free projection is injective on its source list. -/
private theorem eq_of_nodup_map
    {items : List β}
    {project : β → γ}
    {left right : β}
    (nodup : (items.map project).Nodup)
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameProjection : project left = project right) :
    left = right := by
  induction items with
  | nil =>
      simp at leftMember
  | cons first rest inductionHypothesis =>
      have shape :=
        List.nodup_cons.mp nodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftHead | leftTail
      · subst left
        rcases rightMember with rightHead | rightTail
        · exact rightHead.symm
        · exfalso
          exact shape.1
            (List.mem_map.mpr
              ⟨right, rightTail, sameProjection.symm⟩)
      · rcases rightMember with rightHead | rightTail
        · subst right
          exfalso
          exact shape.1
            (List.mem_map.mpr
              ⟨left, leftTail, sameProjection⟩)
        · exact inductionHypothesis shape.2
            leftTail rightTail

/--
On the canonical independent carrier, strict list-position order is exactly
strict numerical identifier order.
-/
theorem RC11.Valid.idBefore_atomIds_iff_lt
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    RC11.IdBefore source.id target.id candidate.atomIds ↔
      source.id < target.id := by
  have sourceIdMember :
      source.id ∈ candidate.atomIds :=
    List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  have targetIdMember :
      target.id ∈ candidate.atomIds :=
    List.mem_map.mpr ⟨target, targetMember, rfl⟩
  have sourceBound :
      source.id < candidate.atoms.length := by
    rw [valid.atomIdsCanonical] at sourceIdMember
    simpa using sourceIdMember
  have targetBound :
      target.id < candidate.atoms.length := by
    rw [valid.atomIdsCanonical] at targetIdMember
    simpa using targetIdMember
  rw [RC11.IdBefore, valid.atomIdsCanonical]
  simp [sourceBound, targetBound,
    idxOf_range_of_lt sourceBound,
    idxOf_range_of_lt targetBound]

/--
Every independent local step is one target control-flow step.

Payload consistency is used by successful pop: the independent atomic carries
the payload while its return state carries the returned node pointer.
-/
theorem LocalStep.refines
    (payload : NodeId → α)
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (consistent :
      RC11.TracePayloadConsistent payload event) :
    TreiberRC11.ControlFlow.LocalStep thread
      (before.toTarget payload)
      (event.toTargetLabel payload)
      (after.toTarget payload) := by
  cases step with
  | beginPush operation node value =>
      exact .beginPush operation node value
  | pushLoad id operation node value observed =>
      exact .pushLoad operation node value observed.toTarget
  | writeNext operation node value expected =>
      exact .writeNext operation node value expected.toTarget
  | pushSuccess id operation node value expected =>
      exact .pushSuccess operation node value expected.toTarget
  | pushFailure id operation node value expected actual =>
      exact .pushFailure operation node value
        expected.toTarget actual.toTarget
  | finishPush operation value =>
      exact .respond operation (.push value)
  | beginPop operation =>
      exact .beginPop operation
  | popLoadEmpty id operation =>
      exact .popLoadEmpty operation
  | popLoadNode id operation observed =>
      exact .popLoadNonempty operation observed
  | readNext operation observed value next =>
      exact .readNext operation observed next.toTarget
  | popSuccess id operation expected value next =>
      have payloadShape :
          value = payload expected := by
        simpa [RC11.TracePayloadConsistent,
          RC11.AtomicPayloadConsistent] using consistent
      subst value
      exact .popSuccess operation expected
        (payload expected) next.toTarget
  | popFailureRetry id operation expected actual value next =>
      exact .popFailureRetry operation expected actual next.toTarget
  | popFailureEmpty id operation expected value next =>
      exact .popFailureEmpty operation expected next.toTarget
  | finishPop operation result =>
      cases result with
      | null =>
          exact .respond operation .popEmpty
      | node node =>
          exact .respond operation (.popValue (payload node))
  | beginIsEmpty operation =>
      exact .beginIsEmpty operation
  | isEmptyLoadNull id operation =>
      exact .isEmptyLoad operation none
  | isEmptyLoadNode id operation observed =>
      exact .isEmptyLoad operation (some observed)
  | finishIsEmpty operation result =>
      exact .respond operation (.isEmpty result)

/--
A successful compare-exchange emitted by one local source step observed its
expected head value.
-/
theorem LocalStep.successfulReadConsistent
    {thread : ThreadId}
    {before after : LocalState α}
    {occurrence : AtomicOccurrence α}
    (step :
      LocalStep thread before
        (.atomic occurrence) after) :
    occurrence.action.SuccessfulReadConsistent := by
  cases step <;>
    simp [AtomicAction.SuccessfulReadConsistent]

/-- Lift an independent local finite prefix to the target local execution. -/
theorem Run.refines
    (payload : NodeId → α)
    {thread : ThreadId}
    {initial final : LocalState α}
    {events : List (TraceEvent α)}
    (run : Run thread initial events final)
    (consistent :
      ∀ event,
        event ∈ events →
          RC11.TracePayloadConsistent payload event) :
    TreiberRC11.ControlFlow.Execution thread
      (initial.toTarget payload)
      (projectedLabels payload events)
      (final.toTarget payload) := by
  induction run with
  | nil state =>
      exact .nil _
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      apply TreiberRC11.ControlFlow.Execution.cons
      · exact first.refines payload
          (consistent event (by simp))
      · exact inductionHypothesis
          (fun laterEvent member =>
            consistent laterEvent (by simp [member]))

/--
Every atomic occurrence contained in a local run satisfies the source
successful-CAS observation equation.
-/
theorem Run.successfulReadConsistent
    {thread : ThreadId}
    {initial final : LocalState α}
    {events : List (TraceEvent α)}
    {occurrence : AtomicOccurrence α}
    (run : Run thread initial events final)
    (member :
      TraceEvent.atomic occurrence ∈ events) :
    occurrence.action.SuccessfulReadConsistent := by
  induction run with
  | nil state =>
      simp at member
  | cons event rest first later inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | inRest
      · subst event
        exact first.successfulReadConsistent
      · exact inductionHypothesis inRest

/-- Thread projection never introduces an event absent from the global trace. -/
theorem mem_eventsForThread
    {thread : ThreadId}
    {trace : List (TraceEvent α)}
    {event : TraceEvent α}
    (member : event ∈ eventsForThread thread trace) :
    event ∈ trace := by
  induction trace with
  | nil =>
      simp [eventsForThread] at member
  | cons first rest inductionHypothesis =>
      by_cases owned : first.thread = thread
      · simp only [eventsForThread, owned, if_true,
          List.mem_cons] at member
        exact member.elim (fun same => by simp [same])
          (fun inRest => by
            simp [inductionHypothesis inRest])
      · simp only [eventsForThread, owned, if_false] at member
        exact by simp [inductionHypothesis member]

/-- An event owned by a selected thread occurs in that thread projection. -/
theorem mem_eventsForThread_of_mem
    {thread : ThreadId}
    {trace : List (TraceEvent α)}
    {event : TraceEvent α}
    (member : event ∈ trace)
    (owned : event.thread = thread) :
    event ∈ eventsForThread thread trace := by
  induction trace with
  | nil =>
      simp at member
  | cons first rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | inRest
      · subst first
        simp [eventsForThread, owned]
      · by_cases firstOwned : first.thread = thread
        · simp only [eventsForThread, firstOwned, if_true,
            List.mem_cons]
          exact Or.inr (inductionHypothesis inRest)
        · simp only [eventsForThread, firstOwned, if_false]
          exact inductionHypothesis inRest

/--
Every successful compare-exchange in a globally generated trace observed its
expected head value.
-/
theorem GlobalRun.successfulReadConsistent
    {trace : List (TraceEvent α)}
    {occurrence : AtomicOccurrence α}
    (run : GlobalRun trace)
    (member :
      TraceEvent.atomic occurrence ∈ trace) :
    occurrence.action.SuccessfulReadConsistent := by
  obtain ⟨final, localRun⟩ :=
    run occurrence.action.thread
  apply localRun.successfulReadConsistent
  exact mem_eventsForThread_of_mem member rfl

/-- Projecting by source owner commutes with translating target labels. -/
theorem labelsForThread_projectedOwnedLabels
    (payload : NodeId → α)
    (thread : ThreadId)
    (trace : List (TraceEvent α)) :
    TreiberRC11.Interleaving.labelsForThread thread
        (projectedOwnedLabels payload trace) =
      projectedLabels payload
        (eventsForThread thread trace) := by
  induction trace with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      by_cases owned : event.thread = thread
      · simp only [projectedOwnedLabels, List.map_cons,
          TreiberRC11.Interleaving.labelsForThread,
          TraceEvent.toOwnedLabel_thread,
          TraceEvent.toOwnedLabel_label,
          eventsForThread]
        simp only [owned, if_true]
        change
          event.toTargetLabel payload ::
              TreiberRC11.Interleaving.labelsForThread thread
                (projectedOwnedLabels payload rest) =
            event.toTargetLabel payload ::
              projectedLabels payload
                (eventsForThread thread rest)
        exact congrArg
          (List.cons (event.toTargetLabel payload))
          inductionHypothesis
      · simp only [projectedOwnedLabels, List.map_cons,
          TreiberRC11.Interleaving.labelsForThread,
          TraceEvent.toOwnedLabel_thread,
          TraceEvent.toOwnedLabel_label,
          eventsForThread]
        simp only [owned, if_false]
        change
          TreiberRC11.Interleaving.labelsForThread thread
              (projectedOwnedLabels payload rest) =
            projectedLabels payload
              (eventsForThread thread rest)
        exact inductionHypothesis

/-- Lift every independent thread projection to target local validity. -/
theorem GlobalRun.refines
    (payload : NodeId → α)
    {trace : List (TraceEvent α)}
    (run : GlobalRun trace)
    (consistent :
      ∀ event,
        event ∈ trace →
          RC11.TracePayloadConsistent payload event) :
    TreiberRC11.Interleaving.LocallyValid
      ({ labels := projectedOwnedLabels payload trace } :
        TreiberRC11.EventGraph.Skeleton α) := by
  refine {
    execution := ?_
  }
  intro thread
  obtain ⟨final, threadRun⟩ :=
    run thread
  refine ⟨final.toTarget payload, ?_⟩
  rw [labelsForThread_projectedOwnedLabels]
  exact threadRun.refines payload
    (fun event member =>
      consistent event (mem_eventsForThread member))

/-- Invocation projection commutes with one source-event translation. -/
@[simp] theorem invocationOperation?_toOwnedLabel
    (payload : NodeId → α)
    (event : TraceEvent α) :
    TreiberRC11.Interleaving.invocationOperation?
        (event.toOwnedLabel payload) =
      invocationId? event := by
  cases event <;> rfl

/-- Invocation identifiers are preserved exactly and in trace order. -/
theorem invocationOperations_projectedOwnedLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    TreiberRC11.Interleaving.invocationOperations
        (projectedOwnedLabels payload trace) =
      invocationIds trace := by
  simp [projectedOwnedLabels,
    TreiberRC11.Interleaving.invocationOperations,
    invocationIds, Function.comp_def]

/-- Push-reservation projection commutes with one source-event translation. -/
@[simp] theorem pushReservation?_toOwnedLabel
    (payload : NodeId → α)
    (event : TraceEvent α) :
    TreiberRC11.Interleaving.pushReservation?
        (event.toOwnedLabel payload) =
      pushNode? event := by
  cases event <;> rfl

/-- Push reservations are preserved exactly and in trace order. -/
theorem pushReservations_projectedOwnedLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    TreiberRC11.Interleaving.pushReservations
        (projectedOwnedLabels payload trace) =
      pushNodes trace := by
  simp [projectedOwnedLabels,
    TreiberRC11.Interleaving.pushReservations,
    pushNodes, Function.comp_def]

namespace SupportedExecution

/--
Construct the exact target controlled source from an independent supported
execution.  No graph relation or downstream validator result is assumed.
-/
def toControlledSource
    (execution : SupportedExecution α) :
    TreiberRC11.ControlledSource
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α) where
  skeleton := {
    labels :=
      projectedOwnedLabels
        execution.candidate.payload
        execution.candidate.trace
  }
  valid := {
    toLocallyValid :=
      execution.client.globalRun.refines
        execution.candidate.payload
        execution.rc11.payloadConsistent
    operationIdsNodup := by
      rw [invocationOperations_projectedOwnedLabels]
      exact execution.client.invocationIdsNodup
    reservationsNodup := by
      rw [pushReservations_projectedOwnedLabels]
      exact execution.client.pushNodesNodup
    reservationsFresh := by
      intro reserved member
      exact TreiberRC11.ModelInitial.initialized_heap reserved
  }

/-- The constructed controlled source has exactly the projected label list. -/
@[simp] theorem toControlledSource_labels
    (execution : SupportedExecution α) :
    execution.toControlledSource.skeleton.labels =
      projectedOwnedLabels
        execution.candidate.payload
        execution.candidate.trace :=
  rfl

/-- Independent atoms map to exactly the controlled source's graph carrier. -/
theorem atoms_toTarget_eq_events
    (execution : SupportedExecution α) :
    execution.candidate.atoms.map RC11.Atom.toTarget =
      execution.toControlledSource.skeleton.events := by
  simpa [toControlledSource] using
    execution.candidate.atoms_toTarget_eq_projectedEvents
      execution.rc11

/-- Every independent carrier atom maps to a controlled-source event. -/
theorem atom_toTarget_mem
    (execution : SupportedExecution α)
    {atom : RC11.Atom α}
    (member : atom ∈ execution.candidate.atoms) :
    atom.toTarget ∈
      execution.toControlledSource.skeleton.events := by
  rw [← execution.atoms_toTarget_eq_events]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

/--
The global source run supplies the successful-CAS observation equation for
every independent carrier atom.
-/
theorem atom_successfulReadConsistent
    (execution : SupportedExecution α)
    (atom : RC11.Atom α)
    (member : atom ∈ execution.candidate.atoms) :
    atom.SuccessfulReadConsistent := by
  cases atom with
  | initial =>
      trivial
  | occurrence sourceOccurrence =>
      exact
        execution.client.globalRun.successfulReadConsistent
          (execution.candidate.atomic_mem_trace_of_mem_atoms
            member)

/-- Target and independent read values agree on every supported atom. -/
theorem atom_toTarget_readValue
    (execution : SupportedExecution α)
    (atom : RC11.Atom α)
    (member : atom ∈ execution.candidate.atoms) :
    atom.toTarget.readValue =
      atom.readValue.map Ptr.toTarget :=
  atom.toTarget_readValue
    (execution.atom_successfulReadConsistent atom member)

/-- The concrete atom projection is injective on the supported carrier. -/
theorem atom_toTarget_injectiveOn
    (execution : SupportedExecution α)
    {left right : RC11.Atom α}
    (leftMember : left ∈ execution.candidate.atoms)
    (rightMember : right ∈ execution.candidate.atoms)
    (sameEvent : left.toTarget = right.toTarget) :
    left = right := by
  have sameId : left.id = right.id := by
    simpa using congrArg TreiberRC11.Event.id sameEvent
  apply eq_of_nodup_map
      (project := RC11.Atom.id)
      (items := execution.candidate.atoms)
      (left := left) (right := right)
  · simpa [RC11.Candidate.atomIds] using
      execution.rc11.atomIdsNodup
  · exact leftMember
  · exact rightMember
  · exact sameId

/--
Target program order is exactly independent program order on projected carrier
atoms.
-/
theorem programOrder_toTarget_iff
    (execution : SupportedExecution α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ execution.candidate.atoms)
    (targetMember :
      target ∈ execution.candidate.atoms) :
    execution.toControlledSource.skeleton.programOrder
        source.toTarget target.toTarget ↔
      RC11.PO execution.candidate source target := by
  constructor
  · rintro ⟨_, _, thread, sourceThread, targetThread,
        identifierOrder⟩
    refine
      ⟨sourceMember, targetMember, thread, ?_, ?_, ?_⟩
    · simpa using sourceThread
    · simpa using targetThread
    · apply
        (execution.rc11.idBefore_atomIds_iff_lt
          sourceMember targetMember).mpr
      simpa using identifierOrder
  · rintro ⟨_, _, thread, sourceThread, targetThread,
        identifierOrder⟩
    refine
      ⟨execution.atom_toTarget_mem sourceMember,
        execution.atom_toTarget_mem targetMember,
        thread, ?_, ?_, ?_⟩
    · simpa using sourceThread
    · simpa using targetThread
    · have less :=
        (execution.rc11.idBefore_atomIds_iff_lt
          sourceMember targetMember).mp identifierOrder
      simpa using less

/-- Erasing ownership from the controlled source returns the exact raw trace. -/
@[simp] theorem rawLabels_toControlledSource
    (execution : SupportedExecution α) :
    TreiberRC11.InterleavingCheck.rawLabels
        execution.toControlledSource =
      projectedRawLabels
        execution.candidate.payload
        execution.candidate.trace :=
  rfl

/--
The existing source validator accepts the exact independent trace projection
and reconstructs the same controlled source.
-/
theorem validateRaw?_projectedRawLabels
    [DecidableEq α]
    (execution : SupportedExecution α) :
    TreiberRC11.InterleavingCheck.validateRaw?
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        (projectedRawLabels
          execution.candidate.payload
          execution.candidate.trace) =
      some execution.toControlledSource := by
  rw [← rawLabels_toControlledSource]
  exact
    TreiberRC11.InterleavingCheck.validateRaw?_complete
      execution.toControlledSource

end SupportedExecution

end WeakMemory.TreiberC11V1
