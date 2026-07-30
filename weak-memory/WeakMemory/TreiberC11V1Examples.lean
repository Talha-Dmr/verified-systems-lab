import WeakMemory.TreiberC11V1Frontend

namespace WeakMemory.TreiberC11V1

/-!
# Concrete executions of the independent C11 semantics

This file supplies small, nonempty witnesses for the declarative semantics.
The examples are built directly from source traces and independent RC11 data;
they do not rely on a downstream validator.
-/

namespace RC11.Candidate

/--
The complete one-thread execution in which node `1` is pushed onto an empty
stack.  Both atomic reads observe the initializer, and the successful CAS is
the sole non-initial modification.
-/
def singlePush (value : α) : RC11.Candidate α where
  trace := singlePushTrace value
  payload := fun _ => value
  readSources := [(1, 0), (2, 0)]
  modificationOrder := [2]

@[simp] theorem singlePush_trace (value : α) :
    (singlePush value).trace = singlePushTrace value :=
  rfl

@[simp] theorem singlePush_atoms (value : α) :
    (singlePush value).atoms = [
      .initial,
      .occurrence ⟨1, .pushLoad 0 1 .null⟩,
      .occurrence
        ⟨2, .pushCas 0 1 1 value .null .null true⟩
    ] := by
  rfl

@[simp] theorem singlePush_atomIds (value : α) :
    (singlePush value).atomIds = [0, 1, 2] := by
  rfl

@[simp] theorem singlePush_writeOrder (value : α) :
    (singlePush value).writeOrder = [0, 2] := by
  rfl

@[simp] theorem singlePush_sourceId
    (value : α)
    (target : EventId) :
    (singlePush value).sourceId target =
      if target = 1 ∨ target = 2 then some 0 else none := by
  by_cases first : target = 1
  · simp [singlePush, Candidate.sourceId, sourceFor, first]
  · by_cases second : target = 2
    · simp [singlePush, Candidate.sourceId, sourceFor, second]
    · simp [singlePush, Candidate.sourceId, sourceFor,
        first, second, Ne.symm first, Ne.symm second]

end RC11.Candidate

namespace SinglePush

private theorem po_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.PO (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  rcases edge with
    ⟨sourceMember, targetMember, thread,
      sourceThread, targetThread, ordered⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [RC11.Atom.thread?, RC11.Atom.id,
      RC11.IdBefore, RC11.Candidate.singlePush_atomIds,
      List.idxOf_cons]
      at sourceThread targetThread ordered ⊢

private theorem rf_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.RF (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  rcases edge with
    ⟨sourceMember, targetMember, chosen⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [RC11.Candidate.singlePush,
      RC11.Candidate.sourceId, RC11.sourceFor,
      RC11.Atom.id] at chosen ⊢

private theorem rf_source_eq_initial
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.RF (RC11.Candidate.singlePush value) source target) :
    source = .initial := by
  rcases edge with
    ⟨sourceMember, targetMember, chosen⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [RC11.Candidate.singlePush,
      RC11.Candidate.sourceId, RC11.sourceFor,
      RC11.Atom.id] at chosen ⊢

private theorem mo_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.MO (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  rcases edge with
    ⟨sourceMember, targetMember, ordered⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [RC11.IdBefore,
      RC11.Candidate.singlePush_writeOrder,
      RC11.Atom.id, List.idxOf_cons] at ordered ⊢

private theorem mo_target_eq_commit
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.MO (RC11.Candidate.singlePush value) source target) :
    target =
      .occurrence
        ⟨2, .pushCas 0 1 1 value .null .null true⟩ := by
  rcases edge with
    ⟨sourceMember, targetMember, ordered⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [RC11.IdBefore,
      RC11.Candidate.singlePush_writeOrder,
      RC11.Atom.id, List.idxOf_cons] at ordered ⊢

private theorem rb_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.RB (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  obtain ⟨origin, readsFrom, modificationOrder, different⟩ := edge
  have originBeforeSource := rf_id_lt value readsFrom
  have originIsInitial :=
    rf_source_eq_initial value readsFrom
  have targetIsCommit :=
    mo_target_eq_commit value modificationOrder
  subst origin
  subst target
  rcases readsFrom with ⟨_, sourceMember, _⟩
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember
  rcases sourceMember with rfl | rfl | rfl <;>
    simp [RC11.Atom.id]
      at originBeforeSource different ⊢

private theorem eco_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.ECO (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  induction edge with
  | readsFrom readsFrom =>
      exact rf_id_lt value readsFrom
  | modificationOrder modificationOrder =>
      exact mo_id_lt value modificationOrder
  | readsBefore readsBefore =>
      exact rb_id_lt value readsBefore
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

private theorem sw_false
    (value : α)
    {source target : RC11.Atom α} :
    ¬ RC11.SW (RC11.Candidate.singlePush value) source target := by
  rintro ⟨rfSource, releaseSequence, readsFrom,
    releaseOrder, acquireOrder⟩
  have rfSourceIsInitial :=
    rf_source_eq_initial value readsFrom
  subst rfSource
  cases releaseSequence with
  | head headMember =>
      simp [RC11.Atom.order] at releaseOrder
  | rmw previousSequence adjacent isRMW =>
      simp [RC11.Atom.IsRMW,
        RC11.Atom.isRMW] at isRMW

private theorem hb_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge : RC11.HB (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  induction edge with
  | programOrder programOrder =>
      exact po_id_lt value programOrder
  | synchronizesWith synchronizesWith =>
      exact (sw_false value synchronizesWith).elim
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

private theorem causal_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge :
      RC11.CausalOrder
        (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  induction edge with
  | programOrder programOrder =>
      exact po_id_lt value programOrder
  | readsFrom readsFrom =>
      exact rf_id_lt value readsFrom
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

end SinglePush

namespace RC11.Candidate

/-- The concrete single-push candidate satisfies the independent RC11 core. -/
theorem singlePush_valid
    (value : α) :
    RC11.Valid (singlePush value) := by
  refine {
    atomIdsCanonical := ?_
    atomIdsNodup := ?_
    payloadConsistent := ?_
    writeTailNodup := ?_
    writeTailExact := ?_
    sourceSpec := ?_
    readSourcesCanonical := ?_
    rmwAdjacent := ?_
    noThinAir := ?_
    coherence := ?_
  }
  · rfl
  · simp
  · intro event member
    simp only [singlePush_trace] at member
    simp [singlePushTrace] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [singlePush, RC11.TracePayloadConsistent,
        RC11.AtomicPayloadConsistent]
  · simp [singlePush]
  · intro eventId
    constructor
    · intro member
      have eventIsCommit : eventId = 2 := by
        simpa [singlePush] using member
      subst eventId
      refine
        ⟨.occurrence
            ⟨2, .pushCas 0 1 1 value .null .null true⟩,
          by simp, rfl, ?_, ?_⟩
      · exact ⟨.node 1, rfl⟩
      · simp [RC11.Atom.IsInitial]
    · rintro ⟨atom, atomMember, atomId,
        isWrite, notInitial⟩
      simp only [singlePush_atoms, List.mem_cons,
        List.not_mem_nil, or_false] at atomMember
      rcases atomMember with rfl | rfl | rfl
      · simp [RC11.Atom.IsInitial] at notInitial
      · simp [RC11.Atom.IsWrite,
          RC11.Atom.writtenValue,
          AtomicAction.writtenValue] at isWrite
      · change eventId ∈ [2]
        simpa [RC11.Atom.id] using atomId.symm
  · intro target targetMember
    simp only [singlePush_atoms, List.mem_cons,
      List.not_mem_nil, or_false] at targetMember
    rcases targetMember with rfl | rfl | rfl
    · rfl
    · exact
        ⟨.initial, by simp, rfl, rfl⟩
    · exact
        ⟨.initial, by simp, rfl, rfl⟩
  · rfl
  · intro source rmw sourceMember rmwMember
      chosen rmwShape
    simp only [singlePush_atoms, List.mem_cons,
      List.not_mem_nil, or_false]
      at sourceMember rmwMember
    rcases rmwMember with rfl | rfl | rfl
    · simp [RC11.Atom.IsRMW,
        RC11.Atom.isRMW] at rmwShape
    · simp [RC11.Atom.IsRMW, RC11.Atom.isRMW,
        AtomicAction.isRMW] at rmwShape
    · rcases sourceMember with rfl | rfl | rfl
      · change RC11.IdAdjacent 0 2 [0, 2]
        constructor
        · refine ⟨by simp, by simp, ?_⟩
          simp [List.idxOf_cons]
        · intro middle
          rintro ⟨firstMiddle, middleLast⟩
          have middleMember := firstMiddle.2.1
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at middleMember
          rcases middleMember with rfl | rfl
          · exact Nat.lt_irrefl _ firstMiddle.2.2
          · exact Nat.lt_irrefl _ middleLast.2.2
      · simp [singlePush, RC11.Candidate.sourceId,
          RC11.sourceFor, RC11.Atom.id] at chosen
      · simp [singlePush, RC11.Candidate.sourceId,
          RC11.sourceFor, RC11.Atom.id] at chosen
  · intro atom cycle
    exact Nat.lt_irrefl atom.id
      (SinglePush.causal_id_lt value cycle)
  · intro source middle happensBefore
    have before :=
      SinglePush.hb_id_lt value happensBefore
    constructor
    · intro same
      subst middle
      exact Nat.lt_irrefl source.id before
    · intro reverse
      exact Nat.lt_asymm before
        (SinglePush.eco_id_lt value reverse)

end RC11.Candidate

namespace SinglePush

private theorem commitRealTime_false
    (value : α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ (RC11.Candidate.singlePush value).atoms)
    (targetMember :
      target ∈ (RC11.Candidate.singlePush value).atoms) :
    ¬ CommitRealTimeEdge
        (RC11.Candidate.singlePush value) source target := by
  intro edge
  simp only [RC11.Candidate.singlePush_atoms,
    List.mem_cons, List.not_mem_nil, or_false]
    at sourceMember targetMember
  rcases sourceMember with rfl | rfl | rfl <;>
    rcases targetMember with rfl | rfl | rfl <;>
    simp [CommitRealTimeEdge,
      RC11.Atom.commitOperation?, RealTimeEdge] at edge

private theorem clientOrderEdge_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (edge :
      ClientOrderEdge
        (RC11.Candidate.singlePush value) source target) :
    source.id < target.id := by
  rcases edge with
    ⟨sourceMember, targetMember,
      programOrder | extendedCoherence | realTime⟩
  · exact po_id_lt value programOrder
  · exact eco_id_lt value extendedCoherence
  · exact
      (commitRealTime_false value
        sourceMember targetMember realTime).elim

private theorem clientOrderPath_id_lt
    (value : α)
    {source target : RC11.Atom α}
    (path :
      Relation.TransGen
        (ClientOrderEdge
          (RC11.Candidate.singlePush value))
        source target) :
    source.id < target.id := by
  induction path with
  | single edge =>
      exact clientOrderEdge_id_lt value edge
  | tail _ edge prefixBefore =>
      exact Nat.lt_trans prefixBefore
        (clientOrderEdge_id_lt value edge)

end SinglePush

/-- The one-push source trace satisfies the independent client contract. -/
theorem singlePushClientContract
    (value : α) :
    ClientContract (RC11.Candidate.singlePush value) := by
  refine {
    globalRun := singlePushGlobalRun value
    invocationIdsNodup := ?_
    pushNodesNodup := ?_
    payloadAgreement := ?_
    immutableNextReads := ?_
  }
  · simp [invocationIds, RC11.Candidate.singlePush,
      singlePushTrace, invocationId?]
  · simp [pushNodes, RC11.Candidate.singlePush,
      singlePushTrace, pushNode?]
  · intro event member
    simp only [RC11.Candidate.singlePush_trace] at member
    simp [singlePushTrace] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [PayloadAgrees, RC11.Candidate.singlePush]
  · intro leading trailing thread operation node next shape
    have selected :
        TraceEvent.readNext thread operation node next ∈
          (RC11.Candidate.singlePush value).trace := by
      rw [shape]
      simp
    simp [RC11.Candidate.singlePush,
      singlePushTrace] at selected

/-- Adding committed client real time preserves acyclicity for one push. -/
theorem singlePushClientOrderAcyclic
    (value : α) :
    ClientOrderAcyclic (RC11.Candidate.singlePush value) := by
  intro atom cycle
  exact Nat.lt_irrefl atom.id
    (SinglePush.clientOrderPath_id_lt value cycle)

namespace DeclarativeExecution

/--
A complete successful push admitted by the public, schedule-free semantics.
-/
def singlePush
    (value : α) :
    DeclarativeExecution α where
  candidate :=
    RC11.Candidate.singlePush value
  rc11 :=
    RC11.Candidate.singlePush_valid value
  client :=
    singlePushClientContract value
  clientOrderAcyclic :=
    singlePushClientOrderAcyclic value

@[simp] theorem singlePush_candidate
    (value : α) :
    (singlePush value).candidate =
      RC11.Candidate.singlePush value :=
  rfl

/-- The witness has a nonempty source trace. -/
theorem singlePush_trace_ne_nil
    (value : α) :
    (singlePush value).candidate.trace ≠ [] := by
  simp [singlePush, RC11.Candidate.singlePush,
    singlePushTrace]

/-- The witness contains the successful release CAS that commits the push. -/
theorem singlePush_successfulCommit_mem
    (value : α) :
    TraceEvent.atomic
        ⟨2, .pushCas 0 1 1 value .null .null true⟩ ∈
      (singlePush value).candidate.trace := by
  simp [singlePush, RC11.Candidate.singlePush,
    singlePushTrace]

end DeclarativeExecution

namespace SupportedExecution

/--
The same successful push with its compatible schedule derived
topologically from declarative acyclicity.
-/
noncomputable def singlePush
    (value : α) :
    SupportedExecution α :=
  (DeclarativeExecution.singlePush value).toSupportedExecution

end SupportedExecution

namespace ExecutionFrontend

/--
The concrete nonempty successful-push history is Herlihy--Wing linearizable.
-/
theorem singlePush_linearizable
    [DecidableEq α]
    (value : α) :
    HerlihyWing.Linearizable []
      (declarativeObservedHistory
        (DeclarativeExecution.singlePush value)) :=
  everyDeclarativeExecution_linearizable
    (DeclarativeExecution.singlePush value)

end ExecutionFrontend

end WeakMemory.TreiberC11V1
