import WeakMemory.MultiLocationRC11

namespace WeakMemory.MultiLocationRC11.ScheduleCounterexample

/-!
# Valid RC11 executions need not admit a global `PO ∪ ECO` schedule

This finite candidate contains two threads that write two locations in
opposite modification-order directions.  It satisfies the current
`MultiLocationRC11.Valid` definition, but `PO ∪ ECO` contains a cycle.
Consequently, validity alone cannot produce a list that respects every
program-order and extended-coherence edge.
-/

inductive Location where
  | x
  | y
  deriving Repr, DecidableEq

def xInitial : Atom Location Nat :=
  ⟨0, none, .x, .initial 0, .relaxed⟩

def yInitial : Atom Location Nat :=
  ⟨1, none, .y, .initial 0, .relaxed⟩

/-- Thread zero writes `x` and then `y`. -/
def xThreadZero : Atom Location Nat :=
  ⟨2, some 0, .x, .store 1, .relaxed⟩

def yThreadZero : Atom Location Nat :=
  ⟨3, some 0, .y, .store 1, .relaxed⟩

/-- Thread one writes `y` and then `x`. -/
def yThreadOne : Atom Location Nat :=
  ⟨4, some 1, .y, .store 2, .relaxed⟩

def xThreadOne : Atom Location Nat :=
  ⟨5, some 1, .x, .store 2, .relaxed⟩

def candidate : Candidate Location Nat where
  atoms :=
    [xInitial, yInitial, xThreadZero, yThreadZero,
      yThreadOne, xThreadOne]
  readSources := []
  modificationOrder
    | .x => [xInitial.id, xThreadOne.id, xThreadZero.id]
    | .y => [yInitial.id, yThreadZero.id, yThreadOne.id]

private theorem atom_cases
    {atom : Atom Location Nat}
    (member : atom ∈ candidate.atoms) :
    atom = xInitial ∨ atom = yInitial ∨
      atom = xThreadZero ∨ atom = yThreadZero ∨
      atom = yThreadOne ∨ atom = xThreadOne := by
  simpa [candidate] using member

theorem candidate_wellFormed : WellFormed candidate := by
  refine {
    atomIdsNodup := by native_decide
    orderSupported := ?_
    threadlessIsInitial := ?_
    initializerExistsUnique := ?_
    modificationOrderNodup := ?_
    modificationOrderExact := ?_
    initializerFirst := ?_
    sourceSpec := ?_
    readSourcesCanonical := ?_
    rmwReadsImmediatePredecessor := ?_
  }
  · intro atom member
    rcases atom_cases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Access.Allows]
  · intro atom member threadless
    rcases atom_cases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Atom.IsInitial, Access.IsInitial] at threadless ⊢
  · intro location represented
    cases location with
    | x =>
        refine ⟨xInitial, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, xInitial,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with ⟨member, sameLocation, isInitial⟩
          rcases atom_cases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [xInitial, yInitial, xThreadZero, yThreadZero,
              yThreadOne, xThreadOne, Atom.IsInitial,
              Access.IsInitial] at sameLocation isInitial ⊢
    | y =>
        refine ⟨yInitial, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, yInitial,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with ⟨member, sameLocation, isInitial⟩
          rcases atom_cases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [xInitial, yInitial, xThreadZero, yThreadZero,
              yThreadOne, xThreadOne, Atom.IsInitial,
              Access.IsInitial] at sameLocation isInitial ⊢
  · intro location
    cases location <;> native_decide
  · intro location eventId
    cases location with
    | x =>
        simp [candidate, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsWrite, Access.IsWrite]
        constructor
        · rintro (rfl | rfl | rfl) <;> simp
        · rintro (rfl | rfl | rfl) <;> simp
    | y =>
        simp [candidate, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsWrite, Access.IsWrite]
        constructor
        · rintro (rfl | rfl | rfl) <;> simp
        · rintro (rfl | rfl | rfl) <;> simp
  · intro initializer later initializerAt laterMember sameLocation
      laterWrite different
    rcases initializerAt with ⟨initializerMember, initializerLocation,
      initializerIsInitial⟩
    rcases atom_cases initializerMember with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases atom_cases laterMember with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [candidate, xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Atom.IsInitial, Access.IsInitial,
        Atom.IsWrite, Access.IsWrite, IdBefore, List.idxOf_cons]
  · intro target targetMember
    rcases atom_cases targetMember with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [candidate, Candidate.sourceId, sourceFor,
        xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Atom.readValue, Access.readValue]
  · simp [candidate, Candidate.canonicalReadSources,
      Candidate.sourceId, sourceFor]
  · intro source rmw readsFrom isRMW
    rcases atom_cases readsFrom.2.1 with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Atom.IsRMW, Access.IsRMW] at isRMW

private def poRank : Atom Location Nat → Nat
  | atom =>
      if atom = xInitial ∨ atom = yInitial then 0
      else if atom = xThreadZero ∨ atom = yThreadOne then 1
      else 2

private theorem po_increases
    {source target : Atom Location Nat}
    (edge : PO candidate source target) :
    poRank source < poRank target := by
  rcases edge with ⟨sourceMember, targetMember, global | sameThread⟩
  · rcases atom_cases sourceMember with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases atom_cases targetMember with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [poRank, xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne, Atom.IsGlobalInitial,
        Atom.IsInitial, Access.IsInitial] at global ⊢
  · obtain ⟨thread, sourceThread, targetThread, before⟩ := sameThread
    rcases atom_cases sourceMember with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases atom_cases targetMember with
        rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [xInitial, yInitial, xThreadZero, yThreadZero,
        yThreadOne, xThreadOne] at sourceThread targetThread
    all_goals subst thread
    all_goals simp at targetThread
    all_goals
      simp [candidate, Candidate.atomIds, poRank, xInitial, yInitial,
        xThreadZero, yThreadZero, yThreadOne, xThreadOne,
        IdBefore, List.idxOf_cons] at before ⊢

private theorem causalOrder_increases
    {source target : Atom Location Nat}
    (path : CausalOrder candidate source target) :
    poRank source < poRank target := by
  induction path with
  | programOrder edge => exact po_increases edge
  | readsFrom edge =>
      rcases atom_cases edge.2.1 with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [RF, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsRead, Access.IsRead] at edge
  | transitive _ _ firstIncreases secondIncreases =>
      exact Nat.lt_trans firstIncreases secondIncreases

private theorem causalOrder_preserves_thread
    {source target : Atom Location Nat}
    {thread : ThreadId}
    (path : CausalOrder candidate source target)
    (sourceThread : source.thread? = some thread) :
    target.thread? = some thread := by
  induction path generalizing thread with
  | programOrder edge =>
      rcases edge with ⟨_, _, global | sameThread⟩
      · have impossible : False := by
          simpa [Atom.IsGlobalInitial, sourceThread] using global.1
        exact impossible.elim
      · obtain ⟨edgeThread, sourceIsEdgeThread,
          targetIsEdgeThread, _⟩ := sameThread
        rw [sourceThread] at sourceIsEdgeThread
        have same : thread = edgeThread :=
          Option.some.inj sourceIsEdgeThread
        simpa [same] using targetIsEdgeThread
  | readsFrom edge =>
      rcases atom_cases edge.2.1 with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [RF, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsRead, Access.IsRead] at edge
  | transitive _ _ firstPreserves secondPreserves =>
      exact secondPreserves (firstPreserves sourceThread)

private def moRank : Atom Location Nat → Nat
  | atom =>
      if atom = xInitial ∨ atom = yInitial then 0
      else if atom = xThreadOne ∨ atom = yThreadZero then 1
      else 2

private theorem mo_increases
    {source target : Atom Location Nat}
    (edge : MO candidate source target) :
    moRank source < moRank target := by
  rcases edge with ⟨sourceMember, targetMember, sourceWrite,
    targetWrite, sameLocation, before⟩
  rcases atom_cases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases atom_cases targetMember with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [candidate, moRank, xInitial, yInitial, xThreadZero,
      yThreadZero, yThreadOne, xThreadOne, IdBefore, List.idxOf_cons]

private theorem eco_increases
    {source target : Atom Location Nat}
    (path : ECO candidate source target) :
    moRank source < moRank target := by
  induction path with
  | readsFrom edge =>
      rcases atom_cases edge.2.1 with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [RF, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsRead, Access.IsRead] at edge
  | modificationOrder edge => exact mo_increases edge
  | readsBefore edge =>
      obtain ⟨origin, readsFrom, _, _⟩ := edge
      rcases atom_cases readsFrom.2.1 with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [RF, xInitial, yInitial, xThreadZero, yThreadZero,
          yThreadOne, xThreadOne, Atom.IsRead, Access.IsRead] at readsFrom
  | transitive _ _ firstIncreases secondIncreases =>
      exact Nat.lt_trans firstIncreases secondIncreases

private theorem eco_closed
    {source target : Atom Location Nat}
    (path : ECO candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms := by
  induction path with
  | readsFrom edge => exact edge.closed
  | modificationOrder edge => exact edge.closed
  | readsBefore edge =>
      obtain ⟨origin, readsFrom, modificationOrder, _⟩ := edge
      exact ⟨readsFrom.closed.2, modificationOrder.closed.2⟩
  | transitive _ _ firstClosed secondClosed =>
      exact ⟨firstClosed.1, secondClosed.2⟩

private theorem synchronizesWith_false
    {source target : Atom Location Nat} :
    ¬ SW candidate source target := by
  rintro ⟨releaseSource, releaseSequence, readsFrom, _, _⟩
  rcases atom_cases readsFrom.2.1 with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RF, xInitial, yInitial, xThreadZero, yThreadZero,
      yThreadOne, xThreadOne, Atom.IsRead, Access.IsRead] at readsFrom

private theorem hb_is_causalOrder
    {source target : Atom Location Nat}
    (path : HB candidate source target) :
    CausalOrder candidate source target := by
  induction path with
  | programOrder edge => exact .programOrder edge
  | synchronizesWith edge => exact (synchronizesWith_false edge).elim
  | transitive _ _ firstPath secondPath =>
      exact .transitive firstPath secondPath

theorem candidate_valid : Valid candidate := by
  refine {
    candidate_wellFormed with
    noThinAir := ?_
    coherence := ?_
  }
  · intro atom cycle
    exact Nat.lt_irrefl _ (causalOrder_increases cycle)
  · intro source target happensBefore
    have forward : poRank source < poRank target :=
      causalOrder_increases (hb_is_causalOrder happensBefore)
    constructor
    · intro same
      subst target
      exact Nat.lt_irrefl _ forward
    · intro reverse
      have sameLocation := reverse.sameLocation
      have backwards : moRank target < moRank source :=
        eco_increases reverse
      rcases eco_closed reverse with
        ⟨targetMember, sourceMember⟩
      rcases atom_cases sourceMember with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases atom_cases targetMember with
          rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [poRank, moRank, xInitial, yInitial, xThreadZero,
          yThreadZero, yThreadOne, xThreadOne] at forward sameLocation backwards
      all_goals
        have impossibleThread :=
          causalOrder_preserves_thread
            (hb_is_causalOrder happensBefore) (by rfl)
        simp [yThreadZero, xThreadOne] at impossibleThread

def ScheduleEdge : Rel (Atom Location Nat) :=
  fun source target =>
    PO candidate source target ∨ ECO candidate source target

theorem po_xThreadZero_yThreadZero :
    PO candidate xThreadZero yThreadZero := by
  refine ⟨by simp [candidate], by simp [candidate], Or.inr ?_⟩
  exact ⟨0, rfl, rfl, by
    simp [candidate, Candidate.atomIds, IdBefore, xInitial, yInitial,
      xThreadZero, yThreadZero, yThreadOne, xThreadOne,
      List.idxOf_cons]⟩

theorem eco_yThreadZero_yThreadOne :
    ECO candidate yThreadZero yThreadOne := by
  exact .modificationOrder ⟨by simp [candidate], by simp [candidate],
    by simp [yThreadZero, Atom.IsWrite, Access.IsWrite],
    by simp [yThreadOne, Atom.IsWrite, Access.IsWrite], rfl,
    by simp [candidate, IdBefore, yThreadZero, yThreadOne, yInitial,
      List.idxOf_cons]⟩

theorem po_yThreadOne_xThreadOne :
    PO candidate yThreadOne xThreadOne := by
  refine ⟨by simp [candidate], by simp [candidate], Or.inr ?_⟩
  exact ⟨1, rfl, rfl, by
    simp [candidate, Candidate.atomIds, IdBefore, xInitial, yInitial,
      xThreadZero, yThreadZero, yThreadOne, xThreadOne,
      List.idxOf_cons]⟩

theorem eco_xThreadOne_xThreadZero :
    ECO candidate xThreadOne xThreadZero := by
  exact .modificationOrder ⟨by simp [candidate], by simp [candidate],
    by simp [xThreadOne, Atom.IsWrite, Access.IsWrite],
    by simp [xThreadZero, Atom.IsWrite, Access.IsWrite], rfl,
    by simp [candidate, IdBefore, xThreadOne, xThreadZero, xInitial,
      List.idxOf_cons]⟩

/-- `PO ∪ ECO` has a nonempty cycle despite `candidate_valid`. -/
theorem scheduleEdge_cycle :
    Relation.TransGen ScheduleEdge xThreadZero xThreadZero := by
  exact Relation.TransGen.trans
    (Relation.TransGen.single (Or.inl po_xThreadZero_yThreadZero))
    (Relation.TransGen.trans
      (Relation.TransGen.single (Or.inr eco_yThreadZero_yThreadOne))
      (Relation.TransGen.trans
        (Relation.TransGen.single (Or.inl po_yThreadOne_xThreadOne))
        (Relation.TransGen.single (Or.inr eco_xThreadOne_xThreadZero))))

def Respects
    (schedule : List (Atom Location Nat)) : Prop :=
  ∀ {source target},
    ScheduleEdge source target →
      IdBefore source.id target.id (schedule.map Atom.id)

/-- No identifier schedule can respect every `PO` and `ECO` edge. -/
theorem no_respecting_schedule :
    ¬ ∃ schedule : List (Atom Location Nat), Respects schedule := by
  rintro ⟨schedule, respects⟩
  have first := respects (Or.inl po_xThreadZero_yThreadZero)
  have second := respects (Or.inr eco_yThreadZero_yThreadOne)
  have third := respects (Or.inl po_yThreadOne_xThreadOne)
  have fourth := respects (Or.inr eco_xThreadOne_xThreadZero)
  have cycle :
      IdBefore xThreadZero.id xThreadZero.id
        (schedule.map Atom.id) :=
    IdBefore.transitive first
      (IdBefore.transitive second
        (IdBefore.transitive third fourth))
  exact IdBefore.irreflexive cycle

/-- Compact separation: generic RC11 validity does not supply this schedule. -/
theorem valid_but_no_respecting_schedule :
    Valid candidate ∧
      ¬ ∃ schedule : List (Atom Location Nat), Respects schedule :=
  ⟨candidate_valid, no_respecting_schedule⟩

end WeakMemory.MultiLocationRC11.ScheduleCounterexample
