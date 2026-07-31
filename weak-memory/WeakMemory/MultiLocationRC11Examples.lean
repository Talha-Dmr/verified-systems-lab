import WeakMemory.MultiLocationRC11

namespace WeakMemory.MultiLocationRC11.TwoLocationExample

/-!
# A nontrivial two-location validation

The candidate exercises both locations, release/acquire reads-from, and RMW
atomicity.  It also proves that per-location modification order does not
invent an order between unrelated writes.
-/

inductive Location where
  | left
  | right
  deriving Repr, DecidableEq

def initLeft : Atom Location Nat where
  id := 0
  thread? := none
  location := .left
  access := .initial 0
  order := .relaxed

def initRight : Atom Location Nat where
  id := 1
  thread? := none
  location := .right
  access := .initial 0
  order := .relaxed

def writeLeft : Atom Location Nat where
  id := 2
  thread? := some 0
  location := .left
  access := .store 1
  order := .release

def readLeft : Atom Location Nat where
  id := 3
  thread? := some 1
  location := .left
  access := .load 1
  order := .acquire

def rmwRight : Atom Location Nat where
  id := 4
  thread? := some 2
  location := .right
  access := .rmw 0 1
  order := .acqRel

def candidate : Candidate Location Nat where
  atoms := [initLeft, initRight, writeLeft, readLeft, rmwRight]
  readSources := [(readLeft.id, writeLeft.id),
    (rmwRight.id, initRight.id)]
  modificationOrder
    | .left => [initLeft.id, writeLeft.id]
    | .right => [initRight.id, rmwRight.id]

theorem modificationOrder_left :
    MO candidate initLeft writeLeft := by
  simp [MO, candidate, initLeft, initRight, writeLeft,
    readLeft, rmwRight, IdBefore, List.idxOf_cons,
    Atom.IsWrite, Access.IsWrite]

theorem modificationOrder_right :
    MO candidate initRight rmwRight := by
  simp [MO, candidate, initLeft, initRight, writeLeft,
    readLeft, rmwRight, IdBefore, List.idxOf_cons,
    Atom.IsWrite, Access.IsWrite]

theorem unrelatedWrites_notModificationOrdered :
    ¬ MO candidate writeLeft rmwRight ∧
      ¬ MO candidate rmwRight writeLeft := by
  constructor <;>
    simp [MO, candidate, initLeft, initRight, writeLeft,
      readLeft, rmwRight]

theorem readsFrom_left :
    RF candidate writeLeft readLeft := by
  simp [RF, candidate, initLeft, initRight, writeLeft,
    readLeft, rmwRight, Candidate.sourceId, sourceFor,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue,
    Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

theorem readsFrom_right :
    RF candidate initRight rmwRight := by
  simp [RF, candidate, initLeft, initRight, writeLeft,
    readLeft, rmwRight, Candidate.sourceId, sourceFor,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue,
    Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

theorem immediateModificationOrder_right :
    ImmediateMO candidate initRight rmwRight := by
  simp [ImmediateMO, candidate, initLeft, initRight, writeLeft,
    readLeft, rmwRight, IdAdjacent, IdBefore, List.idxOf_cons,
    Atom.IsWrite, Access.IsWrite]

theorem synchronizesWith_left :
    SW candidate writeLeft readLeft := by
  refine ⟨writeLeft, ?_, readsFrom_left, rfl, rfl⟩
  exact ReleaseSequence.head (by simp [candidate])
    (by simp [writeLeft, Atom.IsNoninitialWrite, Atom.IsWrite,
      Atom.IsInitial, Access.IsWrite, Access.IsInitial])

theorem happensBefore_left :
    HB candidate writeLeft readLeft :=
  HB.synchronizesWith synchronizesWith_left

theorem candidate_wellFormed : WellFormed candidate := by
  refine {
    atomIdsNodup := ?_
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
  · simp [Candidate.atomIds, candidate, initLeft, initRight,
      writeLeft, readLeft, rmwRight]
  · intro atom member
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals simp [initLeft, initRight, writeLeft, readLeft,
      rmwRight, Access.Allows]
  · intro atom member threadless
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [initLeft, initRight, writeLeft, readLeft,
      rmwRight, Atom.IsInitial, Access.IsInitial]
  · intro location _
    cases location with
    | left =>
        refine ⟨initLeft, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, initLeft,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with
            ⟨otherMember, sameLocation, otherInitial⟩
          simp [candidate] at otherMember
          rcases otherMember with rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [initLeft, initRight, writeLeft,
            readLeft, rmwRight, Atom.IsInitial, Access.IsInitial]
    | right =>
        refine ⟨initRight, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, initRight,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with
            ⟨otherMember, sameLocation, otherInitial⟩
          simp [candidate] at otherMember
          rcases otherMember with rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [initLeft, initRight, writeLeft,
            readLeft, rmwRight, Atom.IsInitial, Access.IsInitial]
  · intro location
    cases location <;>
      simp [candidate, initLeft, initRight, writeLeft,
        readLeft, rmwRight]
  · intro location eventId
    cases location <;>
      simp [candidate, initLeft, initRight, writeLeft,
        readLeft, rmwRight, Atom.IsWrite, Access.IsWrite, eq_comm]
  · intro initializer later initializerAt laterMember
      sameLocation laterWrite different
    rcases initializerAt with
      ⟨initializerMember, initializerLocation, initializerShape⟩
    simp [candidate] at initializerMember laterMember
    rcases initializerMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases laterMember with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [initLeft, initRight, writeLeft, readLeft,
      rmwRight, Atom.IsInitial, Access.IsInitial,
      Atom.IsWrite, Access.IsWrite, IdBefore, List.idxOf_cons,
      candidate]
  · intro target member
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals simp [candidate, initLeft, initRight, writeLeft,
      readLeft, rmwRight, Atom.readValue, Atom.writtenValue,
      Access.readValue, Access.writtenValue,
      Candidate.sourceId, sourceFor]
  · rfl
  · intro source rmw readsFrom isRMW
    have rmwIsRight : rmw = rmwRight := by
      have rmwMember := readsFrom.2.1
      simp [candidate] at rmwMember
      rcases rmwMember with rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [initLeft, initRight, writeLeft,
        readLeft, rmwRight, Atom.IsRMW, Access.IsRMW]
    subst rmw
    have sourceIsRight : source = initRight := by
      have sourceMember := readsFrom.1
      simp [candidate] at sourceMember
      rcases sourceMember with rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [RF, candidate, initLeft, initRight,
        writeLeft, readLeft, rmwRight, Candidate.sourceId,
        sourceFor, Atom.IsWrite, Atom.IsRead, Atom.writtenValue,
        Atom.readValue, Access.IsWrite, Access.IsRead,
        Access.writtenValue, Access.readValue]
    subst source
    exact immediateModificationOrder_right

/-- One common chronological rank certifies both consistency conditions. -/
def orderWitness : OrderWitness candidate where
  rank := Atom.id
  programOrderIncreases := by
    intro source target edge
    obtain ⟨sourceMember, targetMember, order⟩ := edge
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [initLeft, initRight, writeLeft, readLeft,
      rmwRight, Atom.IsGlobalInitial, Atom.IsInitial,
      Access.IsInitial, Candidate.atomIds, IdBefore]
  readsFromIncreases := by
    intro source target edge
    have sourceMember := edge.1
    have targetMember := edge.2.1
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [RF, candidate, initLeft, initRight,
      writeLeft, readLeft, rmwRight, Candidate.sourceId,
      sourceFor, Atom.IsWrite, Atom.IsRead, Atom.writtenValue,
      Atom.readValue, Access.IsWrite, Access.IsRead,
      Access.writtenValue, Access.readValue]
  modificationOrderIncreases := by
    intro source target edge
    have sourceMember := edge.1
    have targetMember := edge.2.1
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [MO, candidate, initLeft, initRight,
      writeLeft, readLeft, rmwRight, Atom.IsWrite,
      Access.IsWrite, IdBefore, List.idxOf_cons]
  readsBeforeIncreases := by
    intro read laterWrite edge
    obtain ⟨source, readsFrom, modificationOrder, different⟩ := edge
    have sourceMember := readsFrom.1
    have readMember := readsFrom.2.1
    have laterMember := modificationOrder.2.1
    simp [candidate] at sourceMember readMember laterMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases readMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases laterMember with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [RF, MO, candidate, initLeft, initRight,
      writeLeft, readLeft, rmwRight, Candidate.sourceId,
      sourceFor, Atom.IsWrite, Atom.IsRead, Atom.writtenValue,
      Atom.readValue, Access.IsWrite, Access.IsRead,
      Access.writtenValue, Access.readValue, IdBefore,
      List.idxOf_cons]

/-- The full non-SC multi-location candidate is valid. -/
theorem candidate_valid : Valid candidate where
  toWellFormed := candidate_wellFormed
  noThinAir := orderWitness.noThinAir
  coherence := orderWitness.coherent

/-- Cross-location reads-from is impossible by construction. -/
theorem noCrossLocationReadsFrom
    {source target : Atom Location Nat}
    (different : source.location ≠ target.location) :
    ¬ RF candidate source target := by
  intro readsFrom
  exact different readsFrom.sameLocation

namespace InvalidRMW

def interposedRight : Atom Location Nat where
  id := 4
  thread? := some 3
  location := .right
  access := .store 7
  order := .relaxed

def lateRmwRight : Atom Location Nat where
  id := 5
  thread? := some 2
  location := .right
  access := .rmw 0 1
  order := .acqRel

/-!
This candidate asks the late RMW to read from `initRight` even though another
right-location write intervenes in modification order.
-/
def candidate : Candidate Location Nat where
  atoms := [initLeft, initRight, writeLeft, readLeft,
    interposedRight, lateRmwRight]
  readSources := [(readLeft.id, writeLeft.id),
    (lateRmwRight.id, initRight.id)]
  modificationOrder
    | .left => [initLeft.id, writeLeft.id]
    | .right => [initRight.id, interposedRight.id, lateRmwRight.id]

theorem readsFrom_staleInitializer :
    RF candidate initRight lateRmwRight := by
  simp [RF, candidate, initLeft, initRight, writeLeft, readLeft,
    interposedRight, lateRmwRight, Candidate.sourceId, sourceFor,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue, Atom.readValue,
    Access.IsWrite, Access.IsRead, Access.writtenValue,
    Access.readValue]

theorem initializer_notImmediate :
    ¬ ImmediateMO candidate initRight lateRmwRight := by
  intro immediate
  have noMiddle := immediate.2.2.2.2.2.2
  exact noMiddle interposedRight.id
    ⟨by
      simp [IdBefore, candidate, initRight, interposedRight,
        lateRmwRight, List.idxOf_cons],
     by
      simp [IdBefore, candidate, initRight, interposedRight,
        lateRmwRight, List.idxOf_cons]⟩

/-- Same-location RMW atomicity rejects the deliberately stale RF source. -/
theorem notWellFormed : ¬ WellFormed candidate := by
  intro wellFormed
  exact initializer_notImmediate
    (wellFormed.rmwReadsImmediatePredecessor
      readsFrom_staleInitializer
      (by simp [lateRmwRight, Atom.IsRMW, Access.IsRMW]))

end InvalidRMW

end WeakMemory.MultiLocationRC11.TwoLocationExample
