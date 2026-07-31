import WeakMemory.MultiLocationRC11

namespace WeakMemory.MultiLocationRC11.ReleaseSequenceExample

/-!
# Release-sequence publication across two locations

This finite candidate combines the RC11 features needed by a queue-shaped
publication argument.  A thread-owned initializer at `payload` is ordered
before a release publication at `publication`.  The release sequence then
passes through a later same-thread plain store and an RMW in another thread;
an acquire reads from that RMW.  A still-later write also makes from-read
nonempty, so the consistency certificate exercises every relation used by
`OrderWitness`.
-/

inductive Location where
  | payload
  | publication
  deriving Repr, DecidableEq

def publicationInit : Atom Location Nat where
  id := 0
  thread? := none
  location := .publication
  access := .initial 0
  order := .relaxed

/-- A freshly allocated object's thread-owned initializer. -/
def dynamicInit : Atom Location Nat where
  id := 1
  thread? := some 0
  location := .payload
  access := .initial 42
  order := .relaxed

/-- The publication whose release semantics heads the release sequence. -/
def releaseHead : Atom Location Nat where
  id := 2
  thread? := some 0
  location := .publication
  access := .store 1
  order := .release

/-- A later same-thread, same-location plain store. -/
def plainStore : Atom Location Nat where
  id := 3
  thread? := some 0
  location := .publication
  access := .store 2
  order := .relaxed

/-- An RMW in another thread that reads from `plainStore`. -/
def sequenceRmw : Atom Location Nat where
  id := 4
  thread? := some 1
  location := .publication
  access := .rmw 2 3
  order := .acqRel

/-- An acquire that reads the RMW's written value. -/
def acquireRead : Atom Location Nat where
  id := 5
  thread? := some 2
  location := .publication
  access := .load 3
  order := .acquire

/-- A later write witnessing a nonempty from-read edge. -/
def laterWrite : Atom Location Nat where
  id := 6
  thread? := some 3
  location := .publication
  access := .store 4
  order := .relaxed

def candidate : Candidate Location Nat where
  atoms := [publicationInit, dynamicInit, releaseHead, plainStore,
    sequenceRmw, acquireRead, laterWrite]
  readSources := [(sequenceRmw.id, plainStore.id),
    (acquireRead.id, sequenceRmw.id)]
  modificationOrder
    | .payload => [dynamicInit.id]
    | .publication => [publicationInit.id, releaseHead.id,
        plainStore.id, sequenceRmw.id, laterWrite.id]

theorem dynamicInit_programOrder_releaseHead :
    PO candidate dynamicInit releaseHead := by
  simp [PO, candidate, publicationInit, dynamicInit, releaseHead,
    plainStore, sequenceRmw, acquireRead, laterWrite,
    Candidate.atomIds, IdBefore, List.idxOf_cons, Atom.IsGlobalInitial,
    Atom.IsInitial, Access.IsInitial]

theorem releaseHead_programOrder_plainStore :
    PO candidate releaseHead plainStore := by
  simp [PO, candidate, publicationInit, dynamicInit, releaseHead,
    plainStore, sequenceRmw, acquireRead, laterWrite,
    Candidate.atomIds, IdBefore, List.idxOf_cons, Atom.IsGlobalInitial,
    Atom.IsInitial, Access.IsInitial]

theorem readsFrom_plainStore_sequenceRmw :
    RF candidate plainStore sequenceRmw := by
  simp [RF, candidate, publicationInit, dynamicInit, releaseHead,
    plainStore, sequenceRmw, acquireRead, laterWrite,
    Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
    Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

theorem readsFrom_sequenceRmw_acquireRead :
    RF candidate sequenceRmw acquireRead := by
  simp [RF, candidate, publicationInit, dynamicInit, releaseHead,
    plainStore, sequenceRmw, acquireRead, laterWrite,
    Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
    Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

theorem immediateModificationOrder_plainStore_sequenceRmw :
    ImmediateMO candidate plainStore sequenceRmw := by
  simp [ImmediateMO, candidate, publicationInit, dynamicInit,
    releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite,
    IdAdjacent, IdBefore, List.idxOf_cons, Atom.IsWrite,
    Access.IsWrite]

theorem releaseSequence_plainStore :
    ReleaseSequence candidate releaseHead plainStore := by
  exact ReleaseSequence.sameThreadWrite
    (by simp [releaseHead, Atom.IsNoninitialWrite, Atom.IsWrite,
      Atom.IsInitial, Access.IsWrite, Access.IsInitial])
    releaseHead_programOrder_plainStore rfl
    (by simp [plainStore, Atom.IsNoninitialWrite, Atom.IsWrite,
      Atom.IsInitial, Access.IsWrite, Access.IsInitial])

theorem releaseSequence_sequenceRmw :
    ReleaseSequence candidate releaseHead sequenceRmw := by
  exact ReleaseSequence.rmw releaseSequence_plainStore
    readsFrom_plainStore_sequenceRmw
    (by simp [sequenceRmw, Atom.IsRMW, Access.IsRMW])

theorem synchronizesWith_acquireRead :
    SW candidate releaseHead acquireRead := by
  exact ⟨sequenceRmw, releaseSequence_sequenceRmw,
    readsFrom_sequenceRmw_acquireRead, rfl, rfl⟩

/-- Publication carries the dynamic initializer to the acquiring thread. -/
theorem dynamicInit_happensBefore_acquireRead :
    HB candidate dynamicInit acquireRead :=
  HB.transitive
    (HB.programOrder dynamicInit_programOrder_releaseHead)
    (HB.synchronizesWith synchronizesWith_acquireRead)

theorem modificationOrder_sequenceRmw_laterWrite :
    MO candidate sequenceRmw laterWrite := by
  simp [MO, candidate, publicationInit, dynamicInit, releaseHead,
    plainStore, sequenceRmw, acquireRead, laterWrite,
    IdBefore, List.idxOf_cons, Atom.IsWrite, Access.IsWrite]

/-- A genuine from-read edge: the acquire precedes a later write in MO. -/
theorem readsBefore_acquireRead_laterWrite :
    RB candidate acquireRead laterWrite :=
  ⟨sequenceRmw, readsFrom_sequenceRmw_acquireRead,
    modificationOrder_sequenceRmw_laterWrite, by decide⟩

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
  · simp [Candidate.atomIds, candidate, publicationInit, dynamicInit,
      releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite]
  · intro atom member
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [publicationInit, dynamicInit, releaseHead,
      plainStore, sequenceRmw, acquireRead, laterWrite, Access.Allows]
  · intro atom member threadless
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [publicationInit, dynamicInit, releaseHead,
      plainStore, sequenceRmw, acquireRead, laterWrite,
      Atom.IsInitial, Access.IsInitial]
  · intro location _
    cases location with
    | payload =>
        refine ⟨dynamicInit, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, dynamicInit,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with
            ⟨otherMember, sameLocation, otherInitial⟩
          simp [candidate] at otherMember
          rcases otherMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [publicationInit, dynamicInit, releaseHead,
            plainStore, sequenceRmw, acquireRead, laterWrite,
            Atom.IsInitial, Access.IsInitial]
    | publication =>
        refine ⟨publicationInit, ?_, ?_⟩
        · simp [Candidate.InitializerAt, candidate, publicationInit,
            Atom.IsInitial, Access.IsInitial]
        · intro other otherInitializer
          rcases otherInitializer with
            ⟨otherMember, sameLocation, otherInitial⟩
          simp [candidate] at otherMember
          rcases otherMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [publicationInit, dynamicInit, releaseHead,
            plainStore, sequenceRmw, acquireRead, laterWrite,
            Atom.IsInitial, Access.IsInitial]
  · intro location
    cases location <;>
      simp [candidate, publicationInit, dynamicInit, releaseHead,
        plainStore, sequenceRmw, acquireRead, laterWrite]
  · intro location eventId
    cases location <;>
      simp [candidate, publicationInit, dynamicInit, releaseHead,
        plainStore, sequenceRmw, acquireRead, laterWrite,
        Atom.IsWrite, Access.IsWrite, eq_comm]
  · intro initializer later initializerAt laterMember sameLocation
      laterWriteShape different
    rcases initializerAt with
      ⟨initializerMember, initializerLocation, initializerShape⟩
    simp [candidate] at initializerMember laterMember
    rcases initializerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases laterMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [publicationInit, dynamicInit, releaseHead,
      plainStore, sequenceRmw, acquireRead, laterWrite,
      Atom.IsInitial, Access.IsInitial, Atom.IsWrite, Access.IsWrite,
      IdBefore, List.idxOf_cons, candidate]
  · intro target member
    simp [candidate] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [candidate, publicationInit, dynamicInit, releaseHead,
      plainStore, sequenceRmw, acquireRead, laterWrite,
      Atom.readValue, Atom.writtenValue, Access.readValue,
      Access.writtenValue, Candidate.sourceId, sourceFor]
  · rfl
  · intro source rmw readsFrom isRMW
    have rmwIsSequenceRmw : rmw = sequenceRmw := by
      have rmwMember := readsFrom.2.1
      simp [candidate] at rmwMember
      rcases rmwMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [publicationInit, dynamicInit, releaseHead,
        plainStore, sequenceRmw, acquireRead, laterWrite,
        Atom.IsRMW, Access.IsRMW]
    subst rmw
    have sourceIsPlainStore : source = plainStore := by
      have sourceMember := readsFrom.1
      simp [candidate] at sourceMember
      rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [RF, candidate, publicationInit, dynamicInit,
        releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite,
        Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
        Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
        Access.writtenValue, Access.readValue]
    subst source
    exact immediateModificationOrder_plainStore_sequenceRmw

def orderWitness : OrderWitness candidate where
  rank := Atom.id
  programOrderIncreases := by
    intro source target edge
    obtain ⟨sourceMember, targetMember, order⟩ := edge
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [candidate, publicationInit, dynamicInit, releaseHead,
      plainStore, sequenceRmw, acquireRead, laterWrite,
      Atom.IsGlobalInitial, Atom.IsInitial, Access.IsInitial,
      Candidate.atomIds, IdBefore, List.idxOf_cons]
  readsFromIncreases := by
    intro source target edge
    have sourceMember := edge.1
    have targetMember := edge.2.1
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [RF, candidate, publicationInit, dynamicInit,
      releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite,
      Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
      Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
      Access.writtenValue, Access.readValue]
  modificationOrderIncreases := by
    intro source target edge
    have sourceMember := edge.1
    have targetMember := edge.2.1
    simp [candidate] at sourceMember targetMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases targetMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [MO, candidate, publicationInit, dynamicInit,
      releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite,
      Atom.IsWrite, Access.IsWrite, IdBefore, List.idxOf_cons]
  readsBeforeIncreases := by
    intro read later edge
    obtain ⟨source, readsFrom, modificationOrder, different⟩ := edge
    have sourceMember := readsFrom.1
    have readMember := readsFrom.2.1
    have laterMember := modificationOrder.2.1
    simp [candidate] at sourceMember readMember laterMember
    rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases readMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases laterMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [RF, MO, candidate, publicationInit, dynamicInit,
      releaseHead, plainStore, sequenceRmw, acquireRead, laterWrite,
      Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
      Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
      Access.writtenValue, Access.readValue, IdBefore, List.idxOf_cons]

theorem candidate_valid : Valid candidate where
  toWellFormed := candidate_wellFormed
  noThinAir := orderWitness.noThinAir
  coherence := orderWitness.coherent

end WeakMemory.MultiLocationRC11.ReleaseSequenceExample
