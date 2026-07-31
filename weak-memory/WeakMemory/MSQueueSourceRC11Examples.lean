import WeakMemory.MSQueueSourceWellFormedExamples

namespace WeakMemory.MSQueue.Source.RC11Example

open MultiLocationRC11
open Example

/-!
# RC11 projection of the checked sequential Michael--Scott source trace

The atomic carrier is generated exclusively by `projectCandidate`; the named
atoms below are projections of the corresponding source occurrences, not
independently authored RC11 atoms.
-/

def readSources : List (EventId × EventId) :=
  [(4, 1), (5, 2), (6, 1), (7, 2), (8, 1),
   (9, 0), (10, 8), (11, 7), (12, 0), (13, 0),
   (14, 13), (15, 8), (16, 3), (17, 13)]

def modificationOrder : Site → List EventId
  | .head => [0, 13]
  | .tail => [1, 8]
  | .next 0 => [2, 7]
  | .next 1 => [3]
  | .next _ => []

def candidate : Candidate Site Ptr :=
  projectCandidate 0 sequentialEvents readSources modificationOrder

def dynamicNextInitializer : Atom Site Ptr :=
  (⟨3, AtomicAction.initializeNext 0 10 1⟩ :
    AtomicOccurrence Nat).toRC11Atom

def enqueueTailRead : Atom Site Ptr :=
  (⟨4, AtomicAction.enqueueTailLoad 0 10 (.node 0)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def enqueueNextRead : Atom Site Ptr :=
  (⟨5, AtomicAction.enqueueNextLoad 0 10 0 .null⟩ :
    AtomicOccurrence Nat).toRC11Atom

def enqueueTailValidation : Atom Site Ptr :=
  (⟨6, AtomicAction.enqueueTailValidate 0 10 (.node 0)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def enqueueLink : Atom Site Ptr :=
  (⟨7, AtomicAction.enqueueLinkCAS 0 10 0 1 7 .null true⟩ :
    AtomicOccurrence Nat).toRC11Atom

def enqueueTailSwing : Atom Site Ptr :=
  (⟨8, AtomicAction.enqueueFinishTailCAS
      0 10 0 1 (.node 0) true⟩ :
    AtomicOccurrence Nat).toRC11Atom

def dequeueHeadRead : Atom Site Ptr :=
  (⟨9, AtomicAction.dequeueHeadLoad 2 30 (.node 0)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def dequeueTailRead : Atom Site Ptr :=
  (⟨10, AtomicAction.dequeueTailLoad 2 30 (.node 1)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def dequeueNextRead : Atom Site Ptr :=
  (⟨11, AtomicAction.dequeueNextLoad 2 30 0 (.node 1)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def dequeueHeadValidation : Atom Site Ptr :=
  (⟨12, AtomicAction.dequeueHeadValidate 2 30 (.node 0)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def dequeueHeadSwing : Atom Site Ptr :=
  (⟨13, AtomicAction.dequeueHeadCAS
      2 30 0 1 7 (.node 0) true⟩ :
    AtomicOccurrence Nat).toRC11Atom

def emptyHeadRead : Atom Site Ptr :=
  (⟨14, AtomicAction.dequeueHeadLoad 1 20 (.node 1)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def emptyTailRead : Atom Site Ptr :=
  (⟨15, AtomicAction.dequeueTailLoad 1 20 (.node 1)⟩ :
    AtomicOccurrence Nat).toRC11Atom

def emptyNextRead : Atom Site Ptr :=
  (⟨16, AtomicAction.dequeueNextLoad 1 20 1 .null⟩ :
    AtomicOccurrence Nat).toRC11Atom

def emptyHeadValidation : Atom Site Ptr :=
  (⟨17, AtomicAction.dequeueHeadValidateEmpty 1 20 1 16⟩ :
    AtomicOccurrence Nat).toRC11Atom

theorem candidate_atoms_exact :
    candidate.atoms = projectedAtoms 0 sequentialEvents :=
  rfl

theorem candidate_atoms_explicit :
    candidate.atoms =
      [headInitializer 0, tailInitializer 0, dummyNextInitializer 0,
       dynamicNextInitializer, enqueueTailRead, enqueueNextRead,
       enqueueTailValidation, enqueueLink, enqueueTailSwing,
       dequeueHeadRead, dequeueTailRead, dequeueNextRead,
       dequeueHeadValidation, dequeueHeadSwing, emptyHeadRead,
       emptyTailRead, emptyNextRead, emptyHeadValidation] := by
  rfl

theorem dynamicNextInitializer_mem :
    dynamicNextInitializer ∈ candidate.atoms := by
  native_decide

theorem enqueueLink_mem : enqueueLink ∈ candidate.atoms := by
  native_decide

theorem dequeueNextRead_mem : dequeueNextRead ∈ candidate.atoms := by
  native_decide

theorem initializerAt_head_iff (atom : Atom Site Ptr) :
    Candidate.InitializerAt candidate .head atom ↔
      atom = headInitializer 0 := by
  constructor
  · rintro ⟨member, sameSite, initial⟩
    simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
      atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
      enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [headInitializer, tailInitializer,
      dummyNextInitializer, AtomicOccurrence.toRC11Atom,
      AtomicAction.thread, AtomicAction.site, AtomicAction.access,
      AtomicAction.order, Atom.IsInitial, Access.IsInitial]
  · rintro rfl
    refine ⟨?_, rfl, ?_⟩
    · native_decide
    · trivial

theorem initializerAt_tail_iff (atom : Atom Site Ptr) :
    Candidate.InitializerAt candidate .tail atom ↔
      atom = tailInitializer 0 := by
  constructor
  · rintro ⟨member, sameSite, initial⟩
    simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
      atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
      enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [headInitializer, tailInitializer,
      dummyNextInitializer, AtomicOccurrence.toRC11Atom,
      AtomicAction.thread, AtomicAction.site, AtomicAction.access,
      AtomicAction.order, Atom.IsInitial, Access.IsInitial]
  · rintro rfl
    refine ⟨?_, rfl, ?_⟩
    · native_decide
    · trivial

theorem initializerAt_next_iff (node : NodeId) (atom : Atom Site Ptr) :
    Candidate.InitializerAt candidate (.next node) atom ↔
      (node = 0 ∧ atom = dummyNextInitializer 0) ∨
      (node = 1 ∧ atom = dynamicNextInitializer) := by
  constructor
  · rintro ⟨member, sameSite, initial⟩
    simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
      atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
      enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [dynamicNextInitializer, headInitializer,
      tailInitializer, dummyNextInitializer,
      AtomicOccurrence.toRC11Atom, AtomicAction.thread,
      AtomicAction.site, AtomicAction.access, AtomicAction.order,
      Atom.IsInitial, Access.IsInitial]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨?_, rfl, ?_⟩
      · native_decide
      · trivial
    · exact ⟨dynamicNextInitializer_mem, rfl, by trivial⟩

theorem represents_next_iff (node : NodeId) :
    candidate.Represents (.next node) ↔ node = 0 ∨ node = 1 := by
  constructor
  · rintro ⟨atom, member, sameSite⟩
    simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
      atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
      enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [headInitializer, tailInitializer,
      dummyNextInitializer, AtomicOccurrence.toRC11Atom,
      AtomicAction.thread, AtomicAction.site]
  · intro shape
    rcases shape with rfl | rfl
    · exact ⟨dummyNextInitializer 0, by native_decide, rfl⟩
    · exact ⟨dynamicNextInitializer,
        dynamicNextInitializer_mem, rfl⟩

theorem dynamicNextInitializer_programOrder_enqueueLink :
    PO candidate dynamicNextInitializer enqueueLink := by
  simp [PO, candidate, dynamicNextInitializer, enqueueLink,
    projectCandidate, projectedAtoms, staticAtoms, headInitializer,
    tailInitializer, dummyNextInitializer, atomicOccurrences,
    sequentialEvents, enqueueEvents, valueDequeueEvents,
    emptyDequeueEvents, TraceEvent.atomicOccurrence?,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Candidate.atomIds, IdBefore, Atom.IsGlobalInitial,
    Atom.IsInitial, Access.IsInitial, List.idxOf_cons]

theorem enqueueLink_readsFrom_dequeueNextRead :
    RF candidate enqueueLink dequeueNextRead := by
  simp [RF, candidate, enqueueLink, dequeueNextRead, readSources,
    projectCandidate, projectedAtoms, staticAtoms, atomicOccurrences,
    sequentialEvents, enqueueEvents, valueDequeueEvents,
    emptyDequeueEvents, TraceEvent.atomicOccurrence?,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
    Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

theorem enqueueLink_synchronizesWith_dequeueNextRead :
    SW candidate enqueueLink dequeueNextRead := by
  refine ⟨enqueueLink, ?_, enqueueLink_readsFrom_dequeueNextRead,
    rfl, rfl⟩
  exact ReleaseSequence.head enqueueLink_mem
    (by simp [enqueueLink, AtomicOccurrence.toRC11Atom,
      AtomicAction.access, Atom.IsNoninitialWrite, Atom.IsWrite,
      Atom.IsInitial, Access.IsWrite, Access.IsInitial])

theorem dynamicNextInitializer_happensBefore_dequeueNextRead :
    HB candidate dynamicNextInitializer dequeueNextRead :=
  HB.transitive
    (HB.programOrder dynamicNextInitializer_programOrder_enqueueLink)
    (HB.synchronizesWith enqueueLink_synchronizesWith_dequeueNextRead)

theorem immediate_next0_initializer_link :
    ImmediateMO candidate (dummyNextInitializer 0) enqueueLink := by
  simp [ImmediateMO, candidate, enqueueLink, modificationOrder,
    projectCandidate, projectedAtoms, staticAtoms, atomicOccurrences,
    sequentialEvents, enqueueEvents, valueDequeueEvents,
    emptyDequeueEvents, TraceEvent.atomicOccurrence?,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    headInitializer, tailInitializer, dummyNextInitializer,
    Atom.IsWrite, Access.IsWrite, IdAdjacent, IdBefore,
    List.idxOf_cons]

theorem immediate_tail_initializer_finish :
    ImmediateMO candidate (tailInitializer 0)
      ((⟨8, AtomicAction.enqueueFinishTailCAS
          0 10 0 1 (.node 0) true⟩ : AtomicOccurrence Nat).toRC11Atom) := by
  simp [ImmediateMO, candidate, modificationOrder, projectCandidate,
    projectedAtoms, staticAtoms, atomicOccurrences, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents,
    TraceEvent.atomicOccurrence?, AtomicOccurrence.toRC11Atom,
    AtomicAction.thread, AtomicAction.site, AtomicAction.access,
    AtomicAction.order, headInitializer, tailInitializer,
    dummyNextInitializer, Atom.IsWrite, Access.IsWrite,
    IdAdjacent, IdBefore, List.idxOf_cons]

theorem immediate_head_initializer_swing :
    ImmediateMO candidate (headInitializer 0)
      ((⟨13, AtomicAction.dequeueHeadCAS
          2 30 0 1 7 (.node 0) true⟩ : AtomicOccurrence Nat).toRC11Atom) := by
  simp [ImmediateMO, candidate, modificationOrder, projectCandidate,
    projectedAtoms, staticAtoms, atomicOccurrences, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents,
    TraceEvent.atomicOccurrence?, AtomicOccurrence.toRC11Atom,
    AtomicAction.thread, AtomicAction.site, AtomicAction.access,
    AtomicAction.order, headInitializer, tailInitializer,
    dummyNextInitializer, Atom.IsWrite, Access.IsWrite,
    IdAdjacent, IdBefore, List.idxOf_cons]

theorem candidate_atomIds_nodup : candidate.atomIds.Nodup := by
  native_decide

theorem candidate_order_supported :
    ∀ atom, atom ∈ candidate.atoms →
      atom.access.Allows atom.order := by
  intro atom member
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [headInitializer, tailInitializer,
    dummyNextInitializer, dynamicNextInitializer, enqueueTailRead,
    enqueueNextRead, enqueueTailValidation, enqueueLink,
    enqueueTailSwing, dequeueHeadRead, dequeueTailRead,
    dequeueNextRead, dequeueHeadValidation, dequeueHeadSwing,
    emptyHeadRead, emptyTailRead, emptyNextRead,
    emptyHeadValidation, AtomicOccurrence.toRC11Atom,
    AtomicAction.access, AtomicAction.order, Access.Allows]

theorem candidate_threadless_is_initial :
    ∀ atom, atom ∈ candidate.atoms →
      atom.thread? = none → atom.IsInitial := by
  intro atom member threadless
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [headInitializer, tailInitializer,
    dummyNextInitializer, dynamicNextInitializer, enqueueTailRead,
    enqueueNextRead, enqueueTailValidation, enqueueLink,
    enqueueTailSwing, dequeueHeadRead, dequeueTailRead,
    dequeueNextRead, dequeueHeadValidation, dequeueHeadSwing,
    emptyHeadRead, emptyTailRead, emptyNextRead,
    emptyHeadValidation, AtomicOccurrence.toRC11Atom,
    AtomicAction.thread, AtomicAction.access, Atom.IsInitial,
    Access.IsInitial]

theorem candidate_initializer_exists_unique :
    ∀ location, candidate.Represents location →
      ∃ initializer,
        Candidate.InitializerAt candidate location initializer ∧
          ∀ other,
            Candidate.InitializerAt candidate location other →
            other = initializer := by
  intro location represented
  cases location with
  | head =>
      refine ⟨headInitializer 0,
        (initializerAt_head_iff (headInitializer 0)).2 rfl, ?_⟩
      intro other otherInitializer
      exact (initializerAt_head_iff other).1 otherInitializer
  | tail =>
      refine ⟨tailInitializer 0,
        (initializerAt_tail_iff (tailInitializer 0)).2 rfl, ?_⟩
      intro other otherInitializer
      exact (initializerAt_tail_iff other).1 otherInitializer
  | next node =>
      rcases (represents_next_iff node).1 represented with rfl | rfl
      · refine ⟨dummyNextInitializer 0,
          (initializerAt_next_iff 0 (dummyNextInitializer 0)).2
            (Or.inl ⟨rfl, rfl⟩), ?_⟩
        intro other otherInitializer
        rcases (initializerAt_next_iff 0 other).1 otherInitializer with
          ⟨_, rfl⟩ | ⟨impossible, _⟩
        · rfl
        · exact (Nat.zero_ne_one impossible).elim
      · refine ⟨dynamicNextInitializer,
          (initializerAt_next_iff 1 dynamicNextInitializer).2
            (Or.inr ⟨rfl, rfl⟩), ?_⟩
        intro other otherInitializer
        rcases (initializerAt_next_iff 1 other).1 otherInitializer with
          ⟨impossible, _⟩ | ⟨_, rfl⟩
        · exact (Nat.one_ne_zero impossible).elim
        · rfl

theorem candidate_modificationOrder_nodup :
    ∀ location, (candidate.modificationOrder location).Nodup := by
  intro location
  cases location with
  | head => native_decide
  | tail => native_decide
  | next node =>
      cases node with
      | zero => native_decide
      | succ node =>
          cases node with
          | zero => native_decide
          | succ node =>
              simp [candidate, projectCandidate, modificationOrder]

theorem candidate_modificationOrder_exact :
    ∀ location eventId,
      eventId ∈ candidate.modificationOrder location ↔
        ∃ atom,
          atom ∈ candidate.atoms ∧
            atom.location = location ∧
            atom.id = eventId ∧ atom.IsWrite := by
  intro location eventId
  rw [candidate_atoms_explicit]
  cases location with
  | head =>
      simp [candidate, projectCandidate, modificationOrder,
        headInitializer, tailInitializer, dummyNextInitializer,
        dynamicNextInitializer, enqueueTailRead, enqueueNextRead,
        enqueueTailValidation, enqueueLink, enqueueTailSwing,
        dequeueHeadRead, dequeueTailRead, dequeueNextRead,
        dequeueHeadValidation, dequeueHeadSwing, emptyHeadRead,
        emptyTailRead, emptyNextRead, emptyHeadValidation,
        AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access, Atom.IsWrite, Access.IsWrite, eq_comm]
  | tail =>
      simp [candidate, projectCandidate, modificationOrder,
        headInitializer, tailInitializer, dummyNextInitializer,
        dynamicNextInitializer, enqueueTailRead, enqueueNextRead,
        enqueueTailValidation, enqueueLink, enqueueTailSwing,
        dequeueHeadRead, dequeueTailRead, dequeueNextRead,
        dequeueHeadValidation, dequeueHeadSwing, emptyHeadRead,
        emptyTailRead, emptyNextRead, emptyHeadValidation,
        AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access, Atom.IsWrite, Access.IsWrite, eq_comm]
  | next node =>
      cases node with
      | zero =>
          simp [candidate, projectCandidate, modificationOrder,
            headInitializer, tailInitializer, dummyNextInitializer,
            dynamicNextInitializer, enqueueTailRead, enqueueNextRead,
            enqueueTailValidation, enqueueLink, enqueueTailSwing,
            dequeueHeadRead, dequeueTailRead, dequeueNextRead,
            dequeueHeadValidation, dequeueHeadSwing, emptyHeadRead,
            emptyTailRead, emptyNextRead, emptyHeadValidation,
            AtomicOccurrence.toRC11Atom, AtomicAction.site,
            AtomicAction.access, Atom.IsWrite, Access.IsWrite, eq_comm]
      | succ node =>
          cases node with
          | zero =>
              simp [candidate, projectCandidate, modificationOrder,
                headInitializer, tailInitializer,
                dummyNextInitializer, dynamicNextInitializer,
                enqueueTailRead, enqueueNextRead,
                enqueueTailValidation, enqueueLink, enqueueTailSwing,
                dequeueHeadRead, dequeueTailRead, dequeueNextRead,
                dequeueHeadValidation, dequeueHeadSwing,
                emptyHeadRead, emptyTailRead, emptyNextRead,
                emptyHeadValidation, AtomicOccurrence.toRC11Atom,
                AtomicAction.site, AtomicAction.access,
                Atom.IsWrite, Access.IsWrite, eq_comm]
          | succ node =>
              simp [candidate, projectCandidate, modificationOrder,
                headInitializer, tailInitializer,
                dummyNextInitializer, dynamicNextInitializer,
                enqueueTailRead, enqueueNextRead,
                enqueueTailValidation, enqueueLink, enqueueTailSwing,
                dequeueHeadRead, dequeueTailRead, dequeueNextRead,
                dequeueHeadValidation, dequeueHeadSwing,
                emptyHeadRead, emptyTailRead, emptyNextRead,
                emptyHeadValidation, AtomicOccurrence.toRC11Atom,
                AtomicAction.site, AtomicAction.access,
                Atom.IsWrite, Access.IsWrite, eq_comm]

theorem candidate_initializer_first :
    ∀ {initializer later : Atom Site Ptr},
      Candidate.InitializerAt candidate initializer.location initializer →
      later ∈ candidate.atoms →
      later.location = initializer.location →
      later.IsWrite →
      later ≠ initializer →
      IdBefore initializer.id later.id
        (candidate.modificationOrder initializer.location) := by
  intro initializer later initializerAt laterMember sameLocation
    laterWrite different
  rcases initializerAt with
    ⟨initializerMember, initializerLocation, initializerShape⟩
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at initializerMember
  rcases initializerMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [headInitializer, tailInitializer,
    dummyNextInitializer, dynamicNextInitializer, enqueueTailRead,
    enqueueNextRead, enqueueTailValidation, enqueueLink,
    enqueueTailSwing, dequeueHeadRead, dequeueTailRead,
    dequeueNextRead, dequeueHeadValidation, dequeueHeadSwing,
    emptyHeadRead, emptyTailRead, emptyNextRead,
    emptyHeadValidation, AtomicOccurrence.toRC11Atom,
    AtomicAction.access, Atom.IsInitial, Access.IsInitial]
      at initializerShape
  all_goals
    simp only [candidate_atoms_explicit, List.mem_cons,
      List.not_mem_nil, or_false] at laterMember
    rcases laterMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [candidate, projectCandidate, modificationOrder,
      headInitializer, tailInitializer, dummyNextInitializer,
      dynamicNextInitializer, enqueueTailRead, enqueueNextRead,
      enqueueTailValidation, enqueueLink, enqueueTailSwing,
      dequeueHeadRead, dequeueTailRead, dequeueNextRead,
      dequeueHeadValidation, dequeueHeadSwing, emptyHeadRead,
      emptyTailRead, emptyNextRead, emptyHeadValidation,
      AtomicOccurrence.toRC11Atom, AtomicAction.thread,
      AtomicAction.site, AtomicAction.access, AtomicAction.order,
      Atom.IsWrite, Access.IsWrite, IdBefore, List.idxOf_cons]

theorem candidate_source_spec :
    ∀ target, target ∈ candidate.atoms →
      match target.readValue with
      | none => candidate.sourceId target.id = none
      | some value =>
          ∃ source,
            source ∈ candidate.atoms ∧
              source.location = target.location ∧
              source.writtenValue = some value ∧
              candidate.sourceId target.id = some source.id := by
  intro target targetMember
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at targetMember
  rcases targetMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨tailInitializer 0, by native_decide⟩
  · exact ⟨dummyNextInitializer 0, by native_decide⟩
  · exact ⟨tailInitializer 0, by native_decide⟩
  · exact ⟨dummyNextInitializer 0, by native_decide⟩
  · exact ⟨tailInitializer 0, by native_decide⟩
  · exact ⟨headInitializer 0, by native_decide⟩
  · exact ⟨enqueueTailSwing, by native_decide⟩
  · exact ⟨enqueueLink, by native_decide⟩
  · exact ⟨headInitializer 0, by native_decide⟩
  · exact ⟨headInitializer 0, by native_decide⟩
  · exact ⟨dequeueHeadSwing, by native_decide⟩
  · exact ⟨enqueueTailSwing, by native_decide⟩
  · exact ⟨dynamicNextInitializer, by native_decide⟩
  · exact ⟨dequeueHeadSwing, by native_decide⟩

theorem candidate_readSources_canonical :
    candidate.readSources = candidate.canonicalReadSources := by
  native_decide

theorem enqueueLink_rf_source
    {source : Atom Site Ptr}
    (readsFrom : RF candidate source enqueueLink) :
    source = dummyNextInitializer 0 := by
  have sourceMember := readsFrom.1
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at sourceMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [RF, candidate, projectCandidate, readSources,
    Candidate.sourceId, sourceFor, headInitializer,
    tailInitializer, dummyNextInitializer, dynamicNextInitializer,
    enqueueTailRead, enqueueNextRead, enqueueTailValidation,
    enqueueLink, enqueueTailSwing, dequeueHeadRead,
    dequeueTailRead, dequeueNextRead, dequeueHeadValidation,
    dequeueHeadSwing, emptyHeadRead, emptyTailRead,
    emptyNextRead, emptyHeadValidation,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue, Atom.readValue,
    Access.IsWrite, Access.IsRead, Access.writtenValue,
    Access.readValue]

theorem enqueueTailSwing_rf_source
    {source : Atom Site Ptr}
    (readsFrom : RF candidate source enqueueTailSwing) :
    source = tailInitializer 0 := by
  have sourceMember := readsFrom.1
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at sourceMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [RF, candidate, projectCandidate, readSources,
    Candidate.sourceId, sourceFor, headInitializer,
    tailInitializer, dummyNextInitializer, dynamicNextInitializer,
    enqueueTailRead, enqueueNextRead, enqueueTailValidation,
    enqueueLink, enqueueTailSwing, dequeueHeadRead,
    dequeueTailRead, dequeueNextRead, dequeueHeadValidation,
    dequeueHeadSwing, emptyHeadRead, emptyTailRead,
    emptyNextRead, emptyHeadValidation,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue, Atom.readValue,
    Access.IsWrite, Access.IsRead, Access.writtenValue,
    Access.readValue]

theorem dequeueHeadSwing_rf_source
    {source : Atom Site Ptr}
    (readsFrom : RF candidate source dequeueHeadSwing) :
    source = headInitializer 0 := by
  have sourceMember := readsFrom.1
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at sourceMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [RF, candidate, projectCandidate, readSources,
    Candidate.sourceId, sourceFor, headInitializer,
    tailInitializer, dummyNextInitializer, dynamicNextInitializer,
    enqueueTailRead, enqueueNextRead, enqueueTailValidation,
    enqueueLink, enqueueTailSwing, dequeueHeadRead,
    dequeueTailRead, dequeueNextRead, dequeueHeadValidation,
    dequeueHeadSwing, emptyHeadRead, emptyTailRead,
    emptyNextRead, emptyHeadValidation,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Atom.IsWrite, Atom.IsRead, Atom.writtenValue, Atom.readValue,
    Access.IsWrite, Access.IsRead, Access.writtenValue,
    Access.readValue]

theorem candidate_rmw_reads_immediate_predecessor :
    ∀ {source rmw : Atom Site Ptr},
      RF candidate source rmw → rmw.IsRMW →
        ImmediateMO candidate source rmw := by
  intro source rmw readsFrom isRMW
  have rmwMember := readsFrom.2.1
  have rmwShape :
      rmw = enqueueLink ∨ rmw = enqueueTailSwing ∨
        rmw = dequeueHeadSwing := by
    simp only [candidate_atoms_explicit, List.mem_cons,
      List.not_mem_nil, or_false] at rmwMember
    rcases rmwMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [headInitializer, tailInitializer,
      dummyNextInitializer, dynamicNextInitializer, enqueueTailRead,
      enqueueNextRead, enqueueTailValidation, enqueueLink,
      enqueueTailSwing, dequeueHeadRead, dequeueTailRead,
      dequeueNextRead, dequeueHeadValidation, dequeueHeadSwing,
      emptyHeadRead, emptyTailRead, emptyNextRead,
      emptyHeadValidation, AtomicOccurrence.toRC11Atom,
      AtomicAction.access, Atom.IsRMW, Access.IsRMW]
  rcases rmwShape with rfl | rfl | rfl
  · rw [enqueueLink_rf_source readsFrom]
    exact immediate_next0_initializer_link
  · rw [enqueueTailSwing_rf_source readsFrom]
    exact immediate_tail_initializer_finish
  · rw [dequeueHeadSwing_rf_source readsFrom]
    exact immediate_head_initializer_swing

theorem candidate_wellFormed : WellFormed candidate where
  atomIdsNodup := candidate_atomIds_nodup
  orderSupported := candidate_order_supported
  threadlessIsInitial := candidate_threadless_is_initial
  initializerExistsUnique := candidate_initializer_exists_unique
  modificationOrderNodup := candidate_modificationOrder_nodup
  modificationOrderExact := candidate_modificationOrder_exact
  initializerFirst := candidate_initializer_first
  sourceSpec := by
    intro target member
    cases selected : target.readValue with
    | none =>
        simpa [selected] using candidate_source_spec target member
    | some value =>
        simpa [selected] using candidate_source_spec target member
  readSourcesCanonical := candidate_readSources_canonical
  rmwReadsImmediatePredecessor :=
    candidate_rmw_reads_immediate_predecessor

set_option maxHeartbeats 1000000 in
theorem po_id_lt
    {source target : Atom Site Ptr}
    (edge : PO candidate source target) :
    source.id < target.id := by
  obtain ⟨sourceMember, targetMember, order⟩ := edge
  simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at sourceMember targetMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases targetMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [candidate, projectCandidate, projectedAtoms,
    staticAtoms, atomicOccurrences, TraceEvent.atomicOccurrence?,
    sequentialEvents, enqueueEvents, valueDequeueEvents,
    emptyDequeueEvents, headInitializer, tailInitializer,
    dummyNextInitializer, AtomicOccurrence.toRC11Atom,
    AtomicAction.thread, AtomicAction.site, AtomicAction.access,
    AtomicAction.order, Atom.IsGlobalInitial, Atom.IsInitial,
    Access.IsInitial, Candidate.atomIds, IdBefore,
    List.idxOf_cons]

set_option maxHeartbeats 1000000 in
theorem rf_id_lt
    {source target : Atom Site Ptr}
    (edge : RF candidate source target) :
    source.id < target.id := by
  have sourceMember := edge.1
  have targetMember := edge.2.1
  simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at sourceMember targetMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases targetMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [RF, candidate, readSources, projectCandidate,
    projectedAtoms, staticAtoms, atomicOccurrences,
    TraceEvent.atomicOccurrence?, sequentialEvents, enqueueEvents,
    valueDequeueEvents, emptyDequeueEvents, headInitializer,
    tailInitializer, dummyNextInitializer,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
    Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue]

set_option maxHeartbeats 1000000 in
theorem mo_id_lt
    {source target : Atom Site Ptr}
    (edge : MO candidate source target) :
    source.id < target.id := by
  have sourceMember := edge.1
  have targetMember := edge.2.1
  simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at sourceMember targetMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases targetMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [MO, candidate, modificationOrder,
    projectCandidate, projectedAtoms, staticAtoms, atomicOccurrences,
    TraceEvent.atomicOccurrence?, sequentialEvents, enqueueEvents,
    valueDequeueEvents, emptyDequeueEvents, headInitializer,
    tailInitializer, dummyNextInitializer,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Atom.IsWrite, Access.IsWrite, IdBefore, List.idxOf_cons]

set_option maxHeartbeats 1000000 in
theorem rb_id_lt
    {read later : Atom Site Ptr}
    (edge : RB candidate read later) :
    read.id < later.id := by
  obtain ⟨source, readsFrom, modificationOrdered, different⟩ := edge
  have readMember := readsFrom.2.1
  have laterMember := modificationOrdered.2.1
  simp [candidate, projectCandidate, projectedAtoms, staticAtoms,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents] at readMember laterMember
  rcases readMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases laterMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [RF, MO, candidate, readSources,
    modificationOrder, projectCandidate, projectedAtoms, staticAtoms,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents,
    headInitializer, tailInitializer, dummyNextInitializer,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    Candidate.sourceId, sourceFor, Atom.IsWrite, Atom.IsRead,
    Atom.writtenValue, Atom.readValue, Access.IsWrite, Access.IsRead,
    Access.writtenValue, Access.readValue, IdBefore,
    List.idxOf_cons]

def orderWitness : OrderWitness candidate where
  rank := Atom.id
  programOrderIncreases := po_id_lt
  readsFromIncreases := rf_id_lt
  modificationOrderIncreases := mo_id_lt
  readsBeforeIncreases := rb_id_lt

theorem candidate_valid : Valid candidate where
  toWellFormed := candidate_wellFormed
  noThinAir := orderWitness.noThinAir
  coherence := orderWitness.coherent

def supportedExecution : SupportedExecution 0 sequentialEvents where
  sourceWellFormed := sequentialSourceWellFormed
  readSources := readSources
  modificationOrder := modificationOrder
  valid := candidate_valid

theorem supportedExecution_candidate :
    supportedExecution.candidate = candidate := rfl

theorem supportedExecution_atoms_exact :
    supportedExecution.candidate.atoms =
      projectedAtoms 0 sequentialEvents :=
  supportedExecution.atoms_exact

end WeakMemory.MSQueue.Source.RC11Example
