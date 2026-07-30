import WeakMemory.TreiberC11V1RC11

namespace WeakMemory.TreiberC11V1

/-!
# Independent execution interface

This module joins the source-only trace semantics to the independent finite
RC11 core.  It still does not import the Treiber validator, Herlihy--Wing
history layer, or any supported-model result type. Executions are finite
prefixes and may therefore end with a pending or committed-but-unreturned
operation.
-/

/-! ## Finite client metadata -/

/-- Invocation identifier carried by a trace event, if it is an invocation. -/
def invocationId? : TraceEvent α → Option OperationId
  | .invokePush _ operation _ _ => some operation
  | .invokePop _ operation => some operation
  | .invokeIsEmpty _ operation => some operation
  | _ => none

/-- Invocation identifiers in source-trace order. -/
def invocationIds (trace : List (TraceEvent α)) : List OperationId :=
  trace.filterMap invocationId?

/-- Node reserved by a push invocation, if any. -/
def pushNode? : TraceEvent α → Option NodeId
  | .invokePush _ _ node _ => some node
  | _ => none

/-- Push-reserved nodes in source-trace order. -/
def pushNodes (trace : List (TraceEvent α)) : List NodeId :=
  trace.filterMap pushNode?

/-- Payload annotations agree with the candidate's immutable node payload. -/
def PayloadAgrees
    (payload : NodeId → α) :
    TraceEvent α → Prop
  | .invokePush _ _ node value =>
      payload node = value
  | .atomic ⟨_, .pushCas _ _ node value _ _ _⟩ =>
      payload node = value
  | .atomic ⟨_, .popCas _ _ expected value _ _ _⟩ =>
      payload expected = value
  | _ =>
      True

/-- Strict occurrence order in a finite list. -/
def OccursBefore
    (first second : β)
    (items : List β) : Prop :=
  ∃ leading between trailing,
    items =
      leading ++ first :: between ++ second :: trailing

/--
Source and client obligations that are independent of RF/MO validation.

The final field is occurrence-sensitive: every selected `readNext` obtains
the immutable link installed by a successful push appearing in its prefix.
-/
structure ClientContract
    (candidate : RC11.Candidate α) : Prop where
  globalRun :
    GlobalRun candidate.trace
  invocationIdsNodup :
    (invocationIds candidate.trace).Nodup
  pushNodesNodup :
    (pushNodes candidate.trace).Nodup
  payloadAgreement :
    ∀ event,
      event ∈ candidate.trace →
        PayloadAgrees candidate.payload event
  immutableNextReads :
    ∀ (leading trailing : List (TraceEvent α))
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (next : Ptr),
      candidate.trace =
          leading ++
            .readNext thread operation node next :: trailing →
        ∃ id publisherThread publisherOperation,
          TraceEvent.atomic
              ⟨id,
                .pushCas
                  publisherThread publisherOperation
                  node (candidate.payload node)
                  next next true⟩ ∈
            leading

/-! ## Commits and client real time -/

/-- Client identity of one method call. -/
abbrev ClientOperation := ThreadId × OperationId

namespace RC11.Atom

/-- Classify exactly the atomic actions that commit a source operation. -/
def commitOperation? : RC11.Atom α → Option ClientOperation
  | .initial =>
      none
  | .occurrence ⟨_, .pushCas thread operation _ _ _ _ true⟩ =>
      some (thread, operation)
  | .occurrence ⟨_, .popLoad thread operation .null⟩ =>
      some (thread, operation)
  | .occurrence ⟨_, .popCas thread operation _ _ _ _ true⟩ =>
      some (thread, operation)
  | .occurrence
      ⟨_, .popCas thread operation _ _ _ .null false⟩ =>
      some (thread, operation)
  | .occurrence ⟨_, .isEmptyLoad thread operation _⟩ =>
      some (thread, operation)
  | _ =>
      none

end RC11.Atom

/-- Committed client operations in a proposed atom schedule. -/
def committedOperations
    (schedule : List (RC11.Atom α)) :
    List ClientOperation :=
  schedule.filterMap RC11.Atom.commitOperation?

/-- Invocation identity exposed by a trace event. -/
def invocationOperation? :
    TraceEvent α → Option ClientOperation
  | .invokePush thread operation _ _ =>
      some (thread, operation)
  | .invokePop thread operation =>
      some (thread, operation)
  | .invokeIsEmpty thread operation =>
      some (thread, operation)
  | _ =>
      none

/-- Response identity exposed by a trace event. -/
def responseOperation? :
    TraceEvent α → Option ClientOperation
  | .respondPush thread operation =>
      some (thread, operation)
  | .respondPop thread operation _ =>
      some (thread, operation)
  | .respondIsEmpty thread operation _ =>
      some (thread, operation)
  | _ =>
      none

/--
Cross-thread response-before-invocation order, read directly from the source
trace rather than inferred from RC11.
-/
def RealTimeEdge
    (trace : List (TraceEvent α))
    (first second : ClientOperation) : Prop :=
  first.1 ≠ second.1 ∧
    ∃ response invocation,
      responseOperation? response = some first ∧
        invocationOperation? invocation = some second ∧
        OccursBefore response invocation trace

/-! ## A client-compatible RC11 order -/

/--
A finite atom order covering the candidate exactly once and preserving every
implementation, memory-model, and applicable client-real-time edge.
-/
structure ClientCompatibleOrder
    (candidate : RC11.Candidate α) where
  schedule :
    List (RC11.Atom α)
  exactAtoms :
    schedule.Perm candidate.atoms
  programOrder :
    ∀ {source target},
      RC11.PO candidate source target →
        RC11.IdBefore source.id target.id
          (schedule.map RC11.Atom.id)
  extendedCoherence :
    ∀ {source target},
      RC11.ECO candidate source target →
        RC11.IdBefore source.id target.id
          (schedule.map RC11.Atom.id)
  realTime :
    ∀ {first second : ClientOperation},
      first ∈ committedOperations schedule →
        second ∈ committedOperations schedule →
        RealTimeEdge candidate.trace first second →
        OccursBefore first second
          (committedOperations schedule)

namespace ClientCompatibleOrder

/-- Exact atom coverage implies exact identifier coverage. -/
theorem exactAtomIds
    (order : ClientCompatibleOrder candidate) :
    (order.schedule.map RC11.Atom.id).Perm candidate.atomIds := by
  simpa [RC11.Candidate.atomIds] using
    order.exactAtoms.map RC11.Atom.id

end ClientCompatibleOrder

/--
The independent supported-execution interface.

Support is defined by source generation, declarative RC11 validity, and an
explicit compatible order.  It is not defined by downstream validator
acceptance.
-/
structure SupportedExecution (α : Type) where
  candidate :
    RC11.Candidate α
  rc11 :
    RC11.Valid candidate
  client :
    ClientContract candidate
  order :
    ClientCompatibleOrder candidate

/-! ## Empty initialized execution -/

private theorem empty_po_false
    (payload : NodeId → α)
    {source target : RC11.Atom α} :
    ¬ RC11.PO (RC11.Candidate.empty payload) source target := by
  rintro ⟨sourceMember, _, thread, sourceThread, _⟩
  have sourceIsInitial :
      source = (.initial : RC11.Atom α) := by
    simpa [RC11.Candidate.empty, RC11.Candidate.atoms,
      RC11.Candidate.nonInitialAtoms] using sourceMember
  subst source
  simp [RC11.Atom.thread?] at sourceThread

private theorem empty_rf_false
    (payload : NodeId → α)
    {source target : RC11.Atom α} :
    ¬ RC11.RF (RC11.Candidate.empty payload) source target := by
  rintro ⟨_, _, chosen⟩
  simp [RC11.Candidate.empty, RC11.Candidate.sourceId,
    RC11.sourceFor] at chosen

private theorem empty_mo_false
    (payload : NodeId → α)
    {source target : RC11.Atom α} :
    ¬ RC11.MO (RC11.Candidate.empty payload) source target := by
  rintro ⟨sourceMember, targetMember, ordered⟩
  have sourceIsInitial :
      source = (.initial : RC11.Atom α) := by
    simpa [RC11.Candidate.empty, RC11.Candidate.atoms,
      RC11.Candidate.nonInitialAtoms] using sourceMember
  have targetIsInitial :
      target = (.initial : RC11.Atom α) := by
    simpa [RC11.Candidate.empty, RC11.Candidate.atoms,
      RC11.Candidate.nonInitialAtoms] using targetMember
  subst source
  subst target
  simp [RC11.IdBefore, RC11.Candidate.writeOrder,
    RC11.Candidate.empty, RC11.Atom.id] at ordered

private theorem empty_eco_false
    (payload : NodeId → α)
    {source target : RC11.Atom α} :
    ¬ RC11.ECO (RC11.Candidate.empty payload) source target := by
  intro path
  induction path with
  | readsFrom readsFrom =>
      exact empty_rf_false payload readsFrom
  | modificationOrder modificationOrder =>
      exact empty_mo_false payload modificationOrder
  | readsBefore readsBefore =>
      obtain ⟨_, readsFrom, _, _⟩ := readsBefore
      exact empty_rf_false payload readsFrom
  | transitive _ _ firstImpossible _ =>
      exact firstImpossible

/-- The empty initialized execution inhabits the independent interface. -/
def SupportedExecution.empty
    (payload : NodeId → α) :
    SupportedExecution α where
  candidate :=
    RC11.Candidate.empty payload
  rc11 :=
    RC11.Candidate.empty_valid payload
  client := {
    globalRun :=
      emptyGlobalRun
    invocationIdsNodup := by
      simp [invocationIds, RC11.Candidate.empty]
    pushNodesNodup := by
      simp [pushNodes, RC11.Candidate.empty]
    payloadAgreement := by
      intro event member
      simp [RC11.Candidate.empty] at member
    immutableNextReads := by
      intro leading trailing thread operation node next shape
      simp [RC11.Candidate.empty] at shape
  }
  order := {
    schedule :=
      [.initial]
    exactAtoms := by
      simp [RC11.Candidate.empty, RC11.Candidate.atoms,
        RC11.Candidate.nonInitialAtoms]
    programOrder := by
      intro source target edge
      exact (empty_po_false payload edge).elim
    extendedCoherence := by
      intro source target edge
      exact (empty_eco_false payload edge).elim
    realTime := by
      intro first second firstMember
      simp [committedOperations,
        RC11.Atom.commitOperation?] at firstMember
  }

end WeakMemory.TreiberC11V1
