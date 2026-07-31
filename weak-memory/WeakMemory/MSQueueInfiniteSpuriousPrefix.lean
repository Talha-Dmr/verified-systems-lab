import WeakMemory.MSQueueInfiniteSpurious

namespace WeakMemory.MSQueue.Source

/-!
# Coherent finite RC11 prefixes of the all-spurious queue execution

The three global initializers have identifiers zero through two.  Every source
event from time two onward is atomic, so the dynamic carrier is the dense
identifier interval beginning at three.  All reads observe either the Tail
initializer or the dummy node's `next` initializer.  There are no successful
RMWs and every represented site has exactly one write.
-/

namespace InfiniteSpurious

open MultiLocationRC11

/-- Dense dynamic atomic stream underlying all finite prefixes. -/
def occurrence : Nat → AtomicOccurrence Unit
  | 0 => ⟨3, .initializeNext 0 1 1⟩
  | 1 => ⟨4, .enqueueTailLoad 0 1 (.node 0)⟩
  | 2 => ⟨5, .enqueueNextLoad 0 1 0 .null⟩
  | 3 => ⟨6, .enqueueTailValidate 0 1 (.node 0)⟩
  | retry + 4 =>
      match retryPhase retry with
      | .link =>
          ⟨retry + 7,
            .enqueueLinkCAS 0 1 0 1 () .null false⟩
      | .tail =>
          ⟨retry + 7, .enqueueTailLoad 0 1 (.node 0)⟩
      | .next =>
          ⟨retry + 7, .enqueueNextLoad 0 1 0 .null⟩
      | .validate =>
          ⟨retry + 7, .enqueueTailValidate 0 1 (.node 0)⟩

@[simp] theorem occurrence_id (index : Nat) :
    (occurrence index).id = index + 3 := by
  cases index with
  | zero => rfl
  | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
          cases index with
          | zero => rfl
          | succ index =>
              cases index with
              | zero => rfl
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase] <;> omega

@[simp] theorem occurrence_thread (index : Nat) :
    (occurrence index).action.thread = 0 := by
  cases index with
  | zero => rfl
  | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
          cases index with
          | zero => rfl
          | succ index =>
              cases index with
              | zero => rfl
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase, AtomicAction.thread]

@[simp] theorem event_two_add (index : Nat) :
    event (index + 2) = .atomic (occurrence index) := by
  cases index with
  | zero => rfl
  | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
          cases index with
          | zero => rfl
          | succ index =>
              cases index with
              | zero => rfl
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [event, occurrence, phase]

/-- Exact source trace after the two non-atomic enqueue prefix events. -/
theorem tracePrefix_two_add (count : Nat) :
    source.tracePrefix (count + 2) =
      [.invokeEnqueue 0 1 1 (), .initializePayload 0 1 1 ()] ++
        (List.range count).map fun index =>
          TraceEvent.atomic (occurrence index) := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      calc
        source.tracePrefix (count.succ + 2) =
            source.tracePrefix (count + 2 + 1) := by
              rfl
        _ = source.tracePrefix (count + 2) ++
              [source.event (count + 2)] :=
            source.tracePrefix_succ (count + 2)
        _ = [.invokeEnqueue 0 1 1 (),
              .initializePayload 0 1 1 ()] ++
              (List.range count.succ).map fun index =>
                TraceEvent.atomic (occurrence index) := by
            rw [inductionHypothesis]
            simp [source, event_two_add, List.range_succ]

/-- Number of dynamic atoms in the first `length` source events. -/
def atomCount (length : Nat) : Nat := length - 2

/-- Every finite source prefix has the expected dense atomic projection. -/
theorem atomicOccurrences_tracePrefix (length : Nat) :
    atomicOccurrences (source.tracePrefix length) =
      (List.range (atomCount length)).map occurrence := by
  cases length with
  | zero =>
      rfl
  | succ length =>
      cases length with
      | zero =>
          rfl
      | succ count =>
          rw [tracePrefix_two_add count]
          simp [atomicOccurrences, atomCount,
            TraceEvent.atomicOccurrence?, List.filterMap_map,
            Function.comp_def]

/-- RF source selected by a dense dynamic occurrence. -/
def occurrenceReadSource : Nat → Option EventId
  | 0 => none
  | 1 => some 1
  | 2 => some 2
  | 3 => some 1
  | retry + 4 =>
      match retryPhase retry with
      | .link => some 2
      | .tail => some 1
      | .next => some 2
      | .validate => some 1

/-- One global RF function shared by all finite restrictions. -/
def readSource : EventId → Option EventId
  | 0 | 1 | 2 => none
  | index + 3 => occurrenceReadSource index

/-- Canonical finite RF serialization for the first `count` occurrences. -/
def prefixReadSources (count : Nat) : List (EventId × EventId) :=
  (List.range count).filterMap fun index =>
    (occurrenceReadSource index).map fun sourceId =>
      (index + 3, sourceId)

/-- Explicit dense carrier shared by the count-indexed candidates. -/
def denseAtoms (count : Nat) : List (Atom Site Ptr) :=
  staticAtoms 0 ++
    (List.range count).map fun index =>
      (occurrence index).toRC11Atom

def isWriteBool (atom : Atom Site Ptr) : Bool :=
  match atom.access with
  | .initial _ | .store _ | .rmw _ _ => true
  | .load _ => false

@[simp] theorem isWriteBool_eq_true_iff (atom : Atom Site Ptr) :
    isWriteBool atom = true ↔ atom.IsWrite := by
  cases atom with
  | mk id thread location access order =>
    cases access <;>
    simp [isWriteBool, Atom.IsWrite, Access.IsWrite]

/-- Per-site write orders, obtained by restricting the carrier to its writes. -/
def prefixModificationOrder
    (count : Nat) (site : Site) : List EventId :=
  ((denseAtoms count).filter fun atom =>
      atom.location == site && isWriteBool atom).map Atom.id

/-- Prefix candidate stated directly over the source projection. -/
def prefixCandidate (length : Nat) : Candidate Site Ptr :=
  projectCandidate 0 (source.tracePrefix length)
    (prefixReadSources (atomCount length))
    (prefixModificationOrder (atomCount length))

/-- A count-indexed candidate with an explicit dense carrier. -/
def denseCandidate (count : Nat) : Candidate Site Ptr where
  atoms := denseAtoms count
  readSources := prefixReadSources count
  modificationOrder := prefixModificationOrder count

theorem prefixCandidate_eq_denseCandidate (length : Nat) :
    prefixCandidate length = denseCandidate (atomCount length) := by
  simp [prefixCandidate, denseCandidate, projectCandidate,
    projectedAtoms, denseAtoms, atomicOccurrences_tracePrefix]

@[simp] theorem denseCandidate_atomIds (count : Nat) :
    (denseCandidate count).atomIds = List.range (count + 3) := by
  simp [denseCandidate, denseAtoms, Candidate.atomIds, staticAtoms,
    headInitializer, tailInitializer, dummyNextInitializer,
    AtomicOccurrence.toRC11Atom, List.range_succ_eq_map,
    List.map_map, Function.comp_def]

@[simp] theorem occurrence_isWrite_iff (index : Nat) :
    (occurrence index).toRC11Atom.IsWrite ↔ index = 0 := by
  cases index with
  | zero =>
      simp [occurrence, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.IsWrite, Access.IsWrite]
  | succ index =>
      cases index with
      | zero =>
          simp [occurrence, AtomicOccurrence.toRC11Atom,
            AtomicAction.access, Atom.IsWrite, Access.IsWrite]
      | succ index =>
          cases index with
          | zero =>
              simp [occurrence, AtomicOccurrence.toRC11Atom,
                AtomicAction.access, Atom.IsWrite, Access.IsWrite]
          | succ index =>
              cases index with
              | zero =>
                  simp [occurrence, AtomicOccurrence.toRC11Atom,
                    AtomicAction.access, Atom.IsWrite, Access.IsWrite]
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase,
                      AtomicOccurrence.toRC11Atom,
                      AtomicAction.access, Atom.IsWrite,
                      Access.IsWrite]

@[simp] theorem occurrence_isInitial_iff (index : Nat) :
    (occurrence index).toRC11Atom.IsInitial ↔ index = 0 := by
  cases index with
  | zero =>
      simp [occurrence, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.IsInitial, Access.IsInitial]
  | succ index =>
      cases index with
      | zero =>
          simp [occurrence, AtomicOccurrence.toRC11Atom,
            AtomicAction.access, Atom.IsInitial, Access.IsInitial]
      | succ index =>
          cases index with
          | zero =>
              simp [occurrence, AtomicOccurrence.toRC11Atom,
                AtomicAction.access, Atom.IsInitial, Access.IsInitial]
          | succ index =>
              cases index with
              | zero =>
                  simp [occurrence, AtomicOccurrence.toRC11Atom,
                    AtomicAction.access, Atom.IsInitial,
                    Access.IsInitial]
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase,
                      AtomicOccurrence.toRC11Atom,
                      AtomicAction.access, Atom.IsInitial,
                      Access.IsInitial]

@[simp] theorem occurrence_not_isRMW (index : Nat) :
    ¬ (occurrence index).toRC11Atom.IsRMW := by
  cases index with
  | zero =>
      simp [occurrence, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.IsRMW, Access.IsRMW]
  | succ index =>
      cases index with
      | zero =>
          simp [occurrence, AtomicOccurrence.toRC11Atom,
            AtomicAction.access, Atom.IsRMW, Access.IsRMW]
      | succ index =>
          cases index with
          | zero =>
              simp [occurrence, AtomicOccurrence.toRC11Atom,
                AtomicAction.access, Atom.IsRMW, Access.IsRMW]
          | succ index =>
              cases index with
              | zero =>
                  simp [occurrence, AtomicOccurrence.toRC11Atom,
                    AtomicAction.access, Atom.IsRMW, Access.IsRMW]
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase,
                      AtomicOccurrence.toRC11Atom,
                      AtomicAction.access, Atom.IsRMW,
                      Access.IsRMW]

/-- Exactly the four initializers are writes in a finite dense carrier. -/
theorem denseAtoms_write_iff
    (count : Nat) (atom : Atom Site Ptr) :
    atom ∈ denseAtoms count ∧ atom.IsWrite ↔
      atom = headInitializer 0 ∨
      atom = tailInitializer 0 ∨
      atom = dummyNextInitializer 0 ∨
      (0 < count ∧ atom = (occurrence 0).toRC11Atom) := by
  constructor
  · rintro ⟨member, write⟩
    simp only [denseAtoms, List.mem_append, List.mem_map] at member
    rcases member with static | dynamic
    · simp [staticAtoms] at static
      rcases static with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · obtain ⟨index, indexMember, rfl⟩ := dynamic
      have indexZero : index = 0 :=
        (occurrence_isWrite_iff index).1 write
      subst index
      exact Or.inr (Or.inr (Or.inr ⟨by simpa using indexMember, rfl⟩))
  · intro shape
    rcases shape with rfl | rfl | rfl | ⟨positive, rfl⟩
    · simp [denseAtoms, staticAtoms, headInitializer,
        Atom.IsWrite, Access.IsWrite]
    · simp [denseAtoms, staticAtoms, tailInitializer,
        Atom.IsWrite, Access.IsWrite]
    · simp [denseAtoms, staticAtoms, dummyNextInitializer,
        Atom.IsWrite, Access.IsWrite]
    · constructor
      · simp only [denseAtoms, List.mem_append]
        exact Or.inr
          (List.mem_map.mpr
            ⟨0, by simpa using positive, rfl⟩)
      · exact (occurrence_isWrite_iff 0).2 rfl

/-- A represented site contains at most one write. -/
theorem denseAtoms_write_eq_of_same_location
    (count : Nat)
    {first second : Atom Site Ptr}
    (firstMember : first ∈ denseAtoms count)
    (secondMember : second ∈ denseAtoms count)
    (firstWrite : first.IsWrite)
    (secondWrite : second.IsWrite)
    (sameLocation : first.location = second.location) :
    first = second := by
  have firstShape :=
    (denseAtoms_write_iff count first).1 ⟨firstMember, firstWrite⟩
  have secondShape :=
    (denseAtoms_write_iff count second).1 ⟨secondMember, secondWrite⟩
  rcases firstShape with rfl | rfl | rfl | ⟨_, rfl⟩ <;>
    rcases secondShape with rfl | rfl | rfl | ⟨_, rfl⟩
  all_goals
    simp [headInitializer, tailInitializer, dummyNextInitializer,
      occurrence, AtomicOccurrence.toRC11Atom,
      AtomicAction.site] at sameLocation ⊢

private theorem isWrite_of_isInitial
    {atom : Atom Location Value}
    (initial : atom.IsInitial) :
    atom.IsWrite := by
  change atom.access.IsInitial at initial
  change atom.access.IsWrite
  generalize atom.access = access at initial ⊢
  cases access <;>
    simp_all [Access.IsInitial, Access.IsWrite]

theorem denseCandidate_atomIds_nodup (count : Nat) :
    (denseCandidate count).atomIds.Nodup := by
  rw [denseCandidate_atomIds]
  exact List.nodup_range

theorem denseCandidate_order_supported
    (count : Nat) :
    ∀ atom,
      atom ∈ (denseCandidate count).atoms →
        atom.access.Allows atom.order := by
  intro atom member
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    all_goals
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, Access.Allows]
  · obtain ⟨index, _, rfl⟩ := dynamic
    exact (occurrence index).toRC11Atom_orderSupported

theorem denseCandidate_threadless_is_initial
    (count : Nat) :
    ∀ atom,
      atom ∈ (denseCandidate count).atoms →
        atom.thread? = none →
          atom.IsInitial := by
  intro atom member threadless
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    all_goals
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, Atom.IsInitial,
        Access.IsInitial]
  · obtain ⟨index, _, rfl⟩ := dynamic
    simp [AtomicOccurrence.toRC11Atom,
      occurrence_thread] at threadless

/-- Every represented atom's site has its expected initializer. -/
theorem denseCandidate_initializer_for_atom
    (count : Nat)
    {atom : Atom Site Ptr}
    (member : atom ∈ (denseCandidate count).atoms) :
    ∃ initializer,
      (denseCandidate count).InitializerAt
        atom.location initializer := by
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    · exact ⟨headInitializer 0, by
        simp [Candidate.InitializerAt, denseCandidate,
          denseAtoms, staticAtoms, headInitializer,
          Atom.IsInitial, Access.IsInitial]⟩
    · exact ⟨tailInitializer 0, by
        simp [Candidate.InitializerAt, denseCandidate,
          denseAtoms, staticAtoms, tailInitializer,
          Atom.IsInitial, Access.IsInitial]⟩
    · exact ⟨dummyNextInitializer 0, by
        simp [Candidate.InitializerAt, denseCandidate,
          denseAtoms, staticAtoms, dummyNextInitializer,
          Atom.IsInitial, Access.IsInitial]⟩
  · obtain ⟨index, indexMember, rfl⟩ := dynamic
    cases index with
    | zero =>
        refine ⟨(occurrence 0).toRC11Atom, ?_⟩
        exact ⟨by
          simp only [denseCandidate, denseAtoms, List.mem_append]
          exact Or.inr
            (List.mem_map.mpr ⟨0, indexMember, rfl⟩),
          rfl, (occurrence_isInitial_iff 0).2 rfl⟩
    | succ index =>
        cases index with
        | zero =>
            exact ⟨tailInitializer 0, by
              simp [Candidate.InitializerAt, denseCandidate,
                denseAtoms, staticAtoms, occurrence,
                tailInitializer, AtomicOccurrence.toRC11Atom,
                AtomicAction.site, Atom.IsInitial,
                Access.IsInitial]⟩
        | succ index =>
            cases index with
            | zero =>
                exact ⟨dummyNextInitializer 0, by
                  simp [Candidate.InitializerAt, denseCandidate,
                    denseAtoms, staticAtoms, occurrence,
                    dummyNextInitializer,
                    AtomicOccurrence.toRC11Atom,
                    AtomicAction.site, Atom.IsInitial,
                    Access.IsInitial]⟩
            | succ index =>
                cases index with
                | zero =>
                    exact ⟨tailInitializer 0, by
                      simp [Candidate.InitializerAt,
                        denseCandidate, denseAtoms, staticAtoms,
                        occurrence, tailInitializer,
                        AtomicOccurrence.toRC11Atom,
                        AtomicAction.site, Atom.IsInitial,
                        Access.IsInitial]⟩
                | succ retry =>
                    cases phase : retryPhase retry with
                    | link =>
                        exact ⟨dummyNextInitializer 0, by
                          simp [Candidate.InitializerAt,
                            denseCandidate, denseAtoms, staticAtoms,
                            occurrence, phase,
                            dummyNextInitializer,
                            AtomicOccurrence.toRC11Atom,
                            AtomicAction.site, Atom.IsInitial,
                            Access.IsInitial]⟩
                    | tail =>
                        exact ⟨tailInitializer 0, by
                          simp [Candidate.InitializerAt,
                            denseCandidate, denseAtoms, staticAtoms,
                            occurrence, phase, tailInitializer,
                            AtomicOccurrence.toRC11Atom,
                            AtomicAction.site, Atom.IsInitial,
                            Access.IsInitial]⟩
                    | next =>
                        exact ⟨dummyNextInitializer 0, by
                          simp [Candidate.InitializerAt,
                            denseCandidate, denseAtoms, staticAtoms,
                            occurrence, phase,
                            dummyNextInitializer,
                            AtomicOccurrence.toRC11Atom,
                            AtomicAction.site, Atom.IsInitial,
                            Access.IsInitial]⟩
                    | validate =>
                        exact ⟨tailInitializer 0, by
                          simp [Candidate.InitializerAt,
                            denseCandidate, denseAtoms, staticAtoms,
                            occurrence, phase, tailInitializer,
                            AtomicOccurrence.toRC11Atom,
                            AtomicAction.site, Atom.IsInitial,
                            Access.IsInitial]⟩

theorem denseCandidate_initializer_exists_unique
    (count : Nat) :
    ∀ location,
      (denseCandidate count).Represents location →
        ∃ initializer,
          (denseCandidate count).InitializerAt location initializer ∧
            ∀ other,
              (denseCandidate count).InitializerAt location other →
                other = initializer := by
  intro location represented
  obtain ⟨atom, atomMember, atomLocation⟩ := represented
  obtain ⟨initializer, initializerAt⟩ :=
    denseCandidate_initializer_for_atom count atomMember
  have initializerLocation : initializer.location = location := by
    exact initializerAt.2.1.trans atomLocation
  refine ⟨initializer,
    ⟨initializerAt.1, initializerLocation, initializerAt.2.2⟩,
    ?_⟩
  intro other otherAt
  apply denseAtoms_write_eq_of_same_location count
  · simpa [denseCandidate] using otherAt.1
  · simpa [denseCandidate] using initializerAt.1
  · exact isWrite_of_isInitial otherAt.2.2
  · exact isWrite_of_isInitial initializerAt.2.2
  · exact otherAt.2.1.trans initializerLocation.symm

theorem denseCandidate_modificationOrder_nodup
    (count : Nat) :
    ∀ location,
      ((denseCandidate count).modificationOrder location).Nodup := by
  intro location
  have carrierNodup :
      ((denseAtoms count).map Atom.id).Nodup := by
    simpa [denseCandidate, Candidate.atomIds] using
      denseCandidate_atomIds_nodup count
  exact carrierNodup.sublist
    ((List.filter_sublist
      (p := fun atom : Atom Site Ptr =>
        atom.location == location && isWriteBool atom)
      (l := denseAtoms count)).map Atom.id)

theorem denseCandidate_modificationOrder_exact
    (count : Nat) :
    ∀ location eventId,
      eventId ∈ (denseCandidate count).modificationOrder location ↔
        ∃ atom,
          atom ∈ (denseCandidate count).atoms ∧
            atom.location = location ∧
            atom.id = eventId ∧
            atom.IsWrite := by
  intro location eventId
  change
    eventId ∈
        (((denseAtoms count).filter fun atom =>
          atom.location == location && isWriteBool atom).map Atom.id) ↔
      ∃ atom,
        atom ∈ denseAtoms count ∧
          atom.location = location ∧
          atom.id = eventId ∧
          atom.IsWrite
  constructor
  · intro member
    obtain ⟨atom, selected, atomId⟩ := List.mem_map.mp member
    obtain ⟨atomMember, predicate⟩ := List.mem_filter.mp selected
    have parts :
        atom.location = location ∧ isWriteBool atom = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using predicate
    exact ⟨atom, atomMember, parts.1, atomId, by
      exact (isWriteBool_eq_true_iff atom).1 parts.2⟩
  · rintro ⟨atom, atomMember, locationExact, atomId, write⟩
    apply List.mem_map.mpr
    refine ⟨atom, List.mem_filter.mpr ⟨atomMember, ?_⟩, atomId⟩
    simp [locationExact, (isWriteBool_eq_true_iff atom).2 write]

theorem denseCandidate_initializer_first
    (count : Nat) :
    ∀ {initializer later : Atom Site Ptr},
      (denseCandidate count).InitializerAt
          initializer.location initializer →
      later ∈ (denseCandidate count).atoms →
      later.location = initializer.location →
      later.IsWrite →
      later ≠ initializer →
      IdBefore initializer.id later.id
        ((denseCandidate count).modificationOrder
          initializer.location) := by
  intro initializer later initializerAt laterMember sameLocation
    laterWrite different
  have equal := denseAtoms_write_eq_of_same_location count
    initializerAt.1 laterMember
    (isWrite_of_isInitial initializerAt.2.2)
    laterWrite sameLocation.symm
  exact (different equal.symm).elim

@[simp] theorem occurrenceReadSource_eq_none_iff (index : Nat) :
    occurrenceReadSource index = none ↔ index = 0 := by
  cases index with
  | zero => simp [occurrenceReadSource]
  | succ index =>
      cases index with
      | zero => simp [occurrenceReadSource]
      | succ index =>
          cases index with
          | zero => simp [occurrenceReadSource]
          | succ index =>
              cases index with
              | zero => simp [occurrenceReadSource]
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrenceReadSource, phase]

theorem prefixReadSources_succ (count : Nat) :
    prefixReadSources (count + 1) =
      prefixReadSources count ++
        (occurrenceReadSource count).toList.map fun sourceId =>
          (count + 3, sourceId) := by
  simp [prefixReadSources, List.range_succ,
    List.filterMap_append]
  cases selected : occurrenceReadSource count <;>
    simp [selected]

/-- RF target identifiers are exactly `4, ..., count + 2`. -/
theorem prefixReadSources_targets (count : Nat) :
    (prefixReadSources count).map Prod.fst =
      List.range' 4 (count - 1) := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      rw [prefixReadSources_succ, List.map_append,
        inductionHypothesis]
      by_cases countZero : count = 0
      · subst count
        rfl
      · obtain ⟨prior, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero countZero
        cases selected : occurrenceReadSource (prior + 1) with
        | none =>
            have impossible : prior + 1 = 0 :=
              (occurrenceReadSource_eq_none_iff (prior + 1)).1 selected
            omega
        | some sourceId =>
            simpa [selected, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using
              (List.range'_1_concat
                (s := 4) (n := prior)).symm

theorem prefixReadSources_targets_nodup (count : Nat) :
    ((prefixReadSources count).map Prod.fst).Nodup := by
  rw [prefixReadSources_targets]
  exact List.nodup_range'

private theorem sourceFor_eq_of_mem
    {entries : List (EventId × EventId)}
    (targetsNodup : (entries.map Prod.fst).Nodup)
    {target sourceId : EventId}
    (member : (target, sourceId) ∈ entries) :
    MultiLocationRC11.sourceFor entries target = some sourceId := by
  induction entries with
  | nil =>
      simp at member
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headTarget, headSource⟩
      simp only [List.map_cons, List.nodup_cons] at targetsNodup
      obtain ⟨headFresh, tailNodup⟩ := targetsNodup
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · injection headExact with targetExact sourceExact
        subst target
        subst sourceId
        simp [MultiLocationRC11.sourceFor]
      · have different : headTarget ≠ target := by
          intro same
          subst headTarget
          exact headFresh
            (List.mem_map.mpr
              ⟨(target, sourceId), tailMember, rfl⟩)
        simp [MultiLocationRC11.sourceFor, different,
          inductionHypothesis tailNodup tailMember]

private theorem sourceFor_eq_none_of_not_mem
    {entries : List (EventId × EventId)}
    {target : EventId}
    (absent : target ∉ entries.map Prod.fst) :
    MultiLocationRC11.sourceFor entries target = none := by
  induction entries with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headTarget, headSource⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      obtain ⟨different, tailAbsent⟩ := absent
      have reversed : headTarget ≠ target := Ne.symm different
      simp [MultiLocationRC11.sourceFor, reversed,
        inductionHypothesis tailAbsent]

@[simp] theorem denseCandidate_sourceId_static
    (count eventId : Nat)
    (isStatic : eventId < 4) :
    (denseCandidate count).sourceId eventId = none := by
  apply sourceFor_eq_none_of_not_mem
  change eventId ∉ (prefixReadSources count).map Prod.fst
  rw [prefixReadSources_targets]
  simp only [List.mem_range']
  omega

@[simp] theorem denseCandidate_sourceId_zero (count : Nat) :
    (denseCandidate count).sourceId 0 = none :=
  denseCandidate_sourceId_static count 0 (by omega)

@[simp] theorem denseCandidate_sourceId_one (count : Nat) :
    (denseCandidate count).sourceId 1 = none :=
  denseCandidate_sourceId_static count 1 (by omega)

@[simp] theorem denseCandidate_sourceId_two (count : Nat) :
    (denseCandidate count).sourceId 2 = none :=
  denseCandidate_sourceId_static count 2 (by omega)

@[simp] theorem denseCandidate_sourceId_occurrence
    (count index : Nat)
    (inPrefix : index < count) :
    (denseCandidate count).sourceId (index + 3) =
      occurrenceReadSource index := by
  cases selected : occurrenceReadSource index with
  | none =>
      have indexZero : index = 0 :=
        (occurrenceReadSource_eq_none_iff index).1 selected
      subst index
      exact denseCandidate_sourceId_static count 3 (by omega)
  | some sourceId =>
      apply sourceFor_eq_of_mem
        (prefixReadSources_targets_nodup count)
      apply List.mem_filterMap.mpr
      refine ⟨index, by simpa using inPrefix, ?_⟩
      simp [selected]

/-- Each dynamic read agrees with the initializer named by its RF selector. -/
theorem occurrence_read_source_spec (index : Nat) :
    match occurrenceReadSource index with
    | none =>
        (occurrence index).toRC11Atom.readValue = none
    | some sourceId =>
        ∃ source : Atom Site Ptr,
          source ∈ staticAtoms 0 ∧
            source.location =
              (occurrence index).toRC11Atom.location ∧
            source.writtenValue =
              (occurrence index).toRC11Atom.readValue ∧
            source.id = sourceId := by
  cases index with
  | zero =>
      simp [occurrenceReadSource, occurrence,
        AtomicOccurrence.toRC11Atom, AtomicAction.access,
        Atom.readValue, Access.readValue]
  | succ index =>
      cases index with
      | zero =>
          exact ⟨tailInitializer 0, by
            simp [occurrence, staticAtoms,
              tailInitializer, AtomicOccurrence.toRC11Atom,
              AtomicAction.site, AtomicAction.access,
              Atom.writtenValue, Atom.readValue,
              Access.writtenValue, Access.readValue]⟩
      | succ index =>
          cases index with
          | zero =>
              exact ⟨dummyNextInitializer 0, by
                simp [occurrence, staticAtoms,
                  dummyNextInitializer,
                  AtomicOccurrence.toRC11Atom,
                  AtomicAction.site, AtomicAction.access,
                  Atom.writtenValue, Atom.readValue,
                  Access.writtenValue, Access.readValue]⟩
          | succ index =>
              cases index with
              | zero =>
                  exact ⟨tailInitializer 0, by
                    simp [occurrence, staticAtoms, tailInitializer,
                      AtomicOccurrence.toRC11Atom,
                      AtomicAction.site, AtomicAction.access,
                      Atom.writtenValue, Atom.readValue,
                      Access.writtenValue, Access.readValue]⟩
              | succ retry =>
                  cases phase : retryPhase retry with
                  | link =>
                      simp only [occurrenceReadSource, occurrence, phase]
                      exact ⟨dummyNextInitializer 0, by
                        simp [staticAtoms,
                          dummyNextInitializer,
                          AtomicOccurrence.toRC11Atom,
                          AtomicAction.site, AtomicAction.access,
                          Atom.writtenValue, Atom.readValue,
                          Access.writtenValue, Access.readValue]⟩
                  | tail =>
                      simp only [occurrenceReadSource, occurrence, phase]
                      exact ⟨tailInitializer 0, by
                        simp [staticAtoms, tailInitializer,
                          AtomicOccurrence.toRC11Atom,
                          AtomicAction.site, AtomicAction.access,
                          Atom.writtenValue, Atom.readValue,
                          Access.writtenValue, Access.readValue]⟩
                  | next =>
                      simp only [occurrenceReadSource, occurrence, phase]
                      exact ⟨dummyNextInitializer 0, by
                        simp [staticAtoms,
                          dummyNextInitializer,
                          AtomicOccurrence.toRC11Atom,
                          AtomicAction.site, AtomicAction.access,
                          Atom.writtenValue, Atom.readValue,
                          Access.writtenValue, Access.readValue]⟩
                  | validate =>
                      simp only [occurrenceReadSource, occurrence, phase]
                      exact ⟨tailInitializer 0, by
                        simp [staticAtoms, tailInitializer,
                          AtomicOccurrence.toRC11Atom,
                          AtomicAction.site, AtomicAction.access,
                          Atom.writtenValue, Atom.readValue,
                          Access.writtenValue, Access.readValue]⟩

private theorem static_written_some
    {atom : Atom Site Ptr}
    (member : atom ∈ staticAtoms 0) :
    ∃ value, atom.writtenValue = some value := by
  simp [staticAtoms] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨.node 0, by
      simp [headInitializer, Atom.writtenValue,
        Access.writtenValue]⟩
  · exact ⟨.node 0, by
      simp [tailInitializer, Atom.writtenValue,
        Access.writtenValue]⟩
  · exact ⟨.null, by
      simp [dummyNextInitializer, Atom.writtenValue,
        Access.writtenValue]⟩

theorem denseCandidate_source_spec
    (count : Nat) :
    ∀ target,
      target ∈ (denseCandidate count).atoms →
      match target.readValue with
      | none =>
          (denseCandidate count).sourceId target.id = none
      | some value =>
          ∃ source,
            source ∈ (denseCandidate count).atoms ∧
              source.location = target.location ∧
              source.writtenValue = some value ∧
              (denseCandidate count).sourceId target.id =
                some source.id := by
  intro target member
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    all_goals
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, Atom.readValue,
        Access.readValue, denseCandidate_sourceId_static]
  · obtain ⟨index, indexMember, rfl⟩ := dynamic
    have indexLt : index < count := by
      simpa using indexMember
    have lookup :=
      denseCandidate_sourceId_occurrence count index indexLt
    have sourceSpec := occurrence_read_source_spec index
    cases selected : occurrenceReadSource index with
    | none =>
        rw [selected] at sourceSpec
        rw [sourceSpec]
        simpa [selected, AtomicOccurrence.toRC11Atom,
          occurrence_id] using lookup
    | some sourceId =>
        rw [selected] at sourceSpec
        obtain ⟨source, sourceStatic, sameLocation,
          sameValue, sourceIdExact⟩ := sourceSpec
        obtain ⟨value, sourceWritten⟩ :=
          static_written_some sourceStatic
        have targetRead :
            (occurrence index).toRC11Atom.readValue = some value := by
          rw [← sameValue, sourceWritten]
        rw [targetRead]
        refine ⟨source, ?_, sameLocation, sourceWritten, ?_⟩
        · change source ∈ denseAtoms count
          simp only [denseAtoms, List.mem_append]
          exact Or.inl sourceStatic
        · simpa [selected, sourceIdExact,
            AtomicOccurrence.toRC11Atom, occurrence_id] using lookup

private theorem filterMap_eq_of_forall
    {items : List β}
    {left right : β → Option γ}
    (exact :
      ∀ item,
        item ∈ items →
          left item = right item) :
    items.filterMap left = items.filterMap right := by
  induction items with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      have headExact : left head = right head :=
        exact head (by simp)
      have tailExact :
          ∀ item,
            item ∈ tail →
              left item = right item :=
        fun item member => exact item (by simp [member])
      cases selected : right head <;>
        simp [headExact, selected,
          inductionHypothesis tailExact]

theorem denseCandidate_readSources_canonical
    (count : Nat) :
    (denseCandidate count).readSources =
      (denseCandidate count).canonicalReadSources := by
  rw [Candidate.canonicalReadSources]
  change
    prefixReadSources count =
      (denseAtoms count).filterMap fun target =>
        ((denseCandidate count).sourceId target.id).map fun sourceId =>
          (target.id, sourceId)
  rw [denseAtoms, List.filterMap_append]
  have staticEmpty :
      (staticAtoms 0).filterMap
          (fun target =>
            ((denseCandidate count).sourceId target.id).map
              fun sourceId => (target.id, sourceId)) = [] := by
    simp [staticAtoms, headInitializer, tailInitializer,
      dummyNextInitializer]
  rw [staticEmpty, List.nil_append, List.filterMap_map]
  unfold prefixReadSources
  change
    List.filterMap
        (fun index =>
          Option.map (fun sourceId => (index + 3, sourceId))
            (occurrenceReadSource index))
        (List.range count) =
      List.filterMap
        ((fun atom : Atom Site Ptr =>
          Option.map (fun sourceId => (atom.id, sourceId))
            ((denseCandidate count).sourceId atom.id)) ∘
          fun index => (occurrence index).toRC11Atom)
        (List.range count)
  apply filterMap_eq_of_forall
  intro index indexMember
  have indexLt : index < count := by
    simpa using indexMember
  simp only [Function.comp_apply,
    AtomicOccurrence.toRC11Atom]
  rw [occurrence_id,
    denseCandidate_sourceId_occurrence count index indexLt]

theorem denseCandidate_rmw_reads_immediate_predecessor
    (count : Nat) :
    ∀ {source rmw : Atom Site Ptr},
      RF (denseCandidate count) source rmw →
      rmw.IsRMW →
        ImmediateMO (denseCandidate count) source rmw := by
  intro source rmw readsFrom isRMW
  have member := readsFrom.2.1
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    all_goals
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, Atom.IsRMW,
        Access.IsRMW] at isRMW
  · obtain ⟨index, _, rfl⟩ := dynamic
    exact (occurrence_not_isRMW index isRMW).elim

theorem denseCandidate_wellFormed
    (count : Nat) :
    WellFormed (denseCandidate count) where
  atomIdsNodup := denseCandidate_atomIds_nodup count
  orderSupported := denseCandidate_order_supported count
  threadlessIsInitial :=
    denseCandidate_threadless_is_initial count
  initializerExistsUnique :=
    denseCandidate_initializer_exists_unique count
  modificationOrderNodup :=
    denseCandidate_modificationOrder_nodup count
  modificationOrderExact :=
    denseCandidate_modificationOrder_exact count
  initializerFirst := denseCandidate_initializer_first count
  sourceSpec := by
    intro target member
    cases selected : target.readValue with
    | none =>
        simpa [selected] using
          denseCandidate_source_spec count target member
    | some value =>
        simpa [selected] using
          denseCandidate_source_spec count target member
  readSourcesCanonical :=
    denseCandidate_readSources_canonical count
  rmwReadsImmediatePredecessor :=
    denseCandidate_rmw_reads_immediate_predecessor count

private theorem idxOf_range_of_lt
    {index bound : Nat}
    (inRange : index < bound) :
    (List.range bound).idxOf index = index := by
  induction bound with
  | zero =>
      omega
  | succ bound inductionHypothesis =>
      rw [List.range_succ, List.idxOf_append]
      by_cases earlier : index < bound
      · simp [List.mem_range, earlier,
          inductionHypothesis earlier]
      · have exactLast : index = bound := by
          omega
        subst index
        simp [List.mem_range]

theorem denseCandidate_po_id_lt
    (count : Nat)
    {source target : Atom Site Ptr}
    (edge : PO (denseCandidate count) source target) :
    source.id < target.id := by
  obtain ⟨sourceMember, targetMember, order⟩ := edge
  rcases order with global | sameThread
  · obtain ⟨sourceGlobal, targetNotGlobal⟩ := global
    simp only [denseCandidate, denseAtoms, List.mem_append,
      List.mem_map] at sourceMember targetMember
    rcases sourceMember with sourceStatic | sourceDynamic
    · simp [staticAtoms] at sourceStatic
      rcases sourceStatic with rfl | rfl | rfl
      all_goals
        rcases targetMember with targetStatic | targetDynamic
      all_goals
        try
          { simp [staticAtoms] at targetStatic
            rcases targetStatic with rfl | rfl | rfl
            all_goals
              simp [headInitializer, tailInitializer,
                dummyNextInitializer, Atom.IsGlobalInitial,
                Atom.IsInitial, Access.IsInitial]
                at targetNotGlobal }
      all_goals
        obtain ⟨index, _, rfl⟩ := targetDynamic
        simp [headInitializer, tailInitializer,
          dummyNextInitializer, AtomicOccurrence.toRC11Atom,
          occurrence_id]
    · obtain ⟨index, _, rfl⟩ := sourceDynamic
      have impossible := sourceGlobal.2
      simp [AtomicOccurrence.toRC11Atom,
        occurrence_thread] at impossible
  · obtain ⟨thread, _, _, before⟩ := sameThread
    rw [denseCandidate_atomIds] at before
    obtain ⟨sourceIdMember, targetIdMember, ordered⟩ := before
    have sourceLt : source.id < count + 3 := by
      simpa using sourceIdMember
    have targetLt : target.id < count + 3 := by
      simpa using targetIdMember
    rwa [idxOf_range_of_lt sourceLt,
      idxOf_range_of_lt targetLt] at ordered

theorem denseCandidate_rf_id_lt
    (count : Nat)
    {source target : Atom Site Ptr}
    (edge : RF (denseCandidate count) source target) :
    source.id < target.id := by
  have targetMember := edge.2.1
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at targetMember
  rcases targetMember with targetStatic | targetDynamic
  · simp [staticAtoms] at targetStatic
    rcases targetStatic with rfl | rfl | rfl
    all_goals
      have targetRead := edge.2.2.2.1
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, Atom.IsRead,
        Access.IsRead] at targetRead
  · obtain ⟨index, indexMember, rfl⟩ := targetDynamic
    have indexLt : index < count := by
      simpa using indexMember
    have lookup :=
      denseCandidate_sourceId_occurrence count index indexLt
    have selected :
        occurrenceReadSource index = some source.id := by
      rw [← lookup]
      simpa [AtomicOccurrence.toRC11Atom,
        occurrence_id] using edge.2.2.2.2.2.2
    change source.id < (occurrence index).id
    rw [occurrence_id]
    cases index with
    | zero =>
        simp [occurrenceReadSource] at selected
    | succ index =>
        cases index with
        | zero =>
            have sourceExact : source.id = 1 :=
              (Option.some.inj selected).symm
            rw [sourceExact]
            simp
        | succ index =>
            cases index with
            | zero =>
                have sourceExact : source.id = 2 :=
                  (Option.some.inj selected).symm
                rw [sourceExact]
                simp
            | succ index =>
                cases index with
                | zero =>
                    have sourceExact : source.id = 1 :=
                      (Option.some.inj selected).symm
                    rw [sourceExact]
                    simp
                | succ retry =>
                    cases phase : retryPhase retry with
                    | link =>
                        simp only [occurrenceReadSource, phase] at selected
                        have sourceExact : source.id = 2 :=
                          (Option.some.inj selected).symm
                        rw [sourceExact]
                        simp
                    | tail =>
                        simp only [occurrenceReadSource, phase] at selected
                        have sourceExact : source.id = 1 :=
                          (Option.some.inj selected).symm
                        rw [sourceExact]
                        simp
                    | next =>
                        simp only [occurrenceReadSource, phase] at selected
                        have sourceExact : source.id = 2 :=
                          (Option.some.inj selected).symm
                        rw [sourceExact]
                        simp
                    | validate =>
                        simp only [occurrenceReadSource, phase] at selected
                        have sourceExact : source.id = 1 :=
                          (Option.some.inj selected).symm
                        rw [sourceExact]
                        simp

theorem denseCandidate_mo_false
    (count : Nat)
    {source target : Atom Site Ptr}
    (edge : MO (denseCandidate count) source target) :
    False := by
  obtain ⟨sourceMember, targetMember, sourceWrite,
    targetWrite, sameLocation, before⟩ := edge
  have equal := denseAtoms_write_eq_of_same_location count
    (by simpa [denseCandidate] using sourceMember)
    (by simpa [denseCandidate] using targetMember)
    sourceWrite targetWrite sameLocation
  subst target
  exact IdBefore.irreflexive before

theorem denseCandidate_rb_false
    (count : Nat)
    {read later : Atom Site Ptr}
    (edge : RB (denseCandidate count) read later) :
    False := by
  obtain ⟨source, _, modificationOrdered, _⟩ := edge
  exact denseCandidate_mo_false count modificationOrdered

def denseCandidate_orderWitness
    (count : Nat) :
    OrderWitness (denseCandidate count) where
  rank := Atom.id
  programOrderIncreases := denseCandidate_po_id_lt count
  readsFromIncreases := denseCandidate_rf_id_lt count
  modificationOrderIncreases := by
    intro source target edge
    exact (denseCandidate_mo_false count edge).elim
  readsBeforeIncreases := by
    intro read later edge
    exact (denseCandidate_rb_false count edge).elim

theorem denseCandidate_valid
    (count : Nat) :
    Valid (denseCandidate count) where
  toWellFormed := denseCandidate_wellFormed count
  noThinAir := (denseCandidate_orderWitness count).noThinAir
  coherence := (denseCandidate_orderWitness count).coherent

/-!
## Source well-formedness and supported prefixes
-/

theorem sourceWellFormed (length : Nat) :
    SourceWellFormed 0 (source.tracePrefix length) := by
  cases length with
  | zero =>
      refine {
        atomicIdsCanonical := rfl
        invocationIdsNodup := by
          simp [source, InfiniteExecution.tracePrefix,
            invocationIds]
        reservedNodesNodup := by
          simp [source, InfiniteExecution.tracePrefix,
            reservedNodes]
        dummyNotReserved := by
          simp [source, InfiniteExecution.tracePrefix,
            reservedNodes]
        threadRuns := fun thread =>
          ⟨source.state 0 thread, source.prefix_run thread 0⟩
        payloadInitializationMatches := ?_
        nextInitializationMatches := ?_
        payloadReadInitialized := ?_
        emptyAnchor := ?_
      }
      all_goals simp [source, InfiniteExecution.tracePrefix]
  | succ length =>
      cases length with
      | zero =>
          refine {
            atomicIdsCanonical := rfl
            invocationIdsNodup := by
              simp [source, InfiniteExecution.tracePrefix,
                event, invocationIds, TraceEvent.invocationId?]
            reservedNodesNodup := by
              simp [source, InfiniteExecution.tracePrefix,
                event, reservedNodes, TraceEvent.reservedNode?]
            dummyNotReserved := by
              simp [source, InfiniteExecution.tracePrefix,
                event, reservedNodes, TraceEvent.reservedNode?]
            threadRuns := fun thread =>
              ⟨source.state 1 thread, source.prefix_run thread 1⟩
            payloadInitializationMatches := ?_
            nextInitializationMatches := ?_
            payloadReadInitialized := ?_
            emptyAnchor := ?_
          }
          all_goals
            simp [source, InfiniteExecution.tracePrefix,
              event]
      | succ count =>
          have traceExact := tracePrefix_two_add count
          refine {
            atomicIdsCanonical := ?_
            invocationIdsNodup := ?_
            reservedNodesNodup := ?_
            dummyNotReserved := ?_
            threadRuns := fun thread =>
              ⟨source.state (count + 2) thread,
                source.prefix_run thread (count + 2)⟩
            payloadInitializationMatches := ?_
            nextInitializationMatches := ?_
            payloadReadInitialized := ?_
            emptyAnchor := ?_
          }
          · simp [atomicIds, canonicalDynamicIds,
              atomicOccurrences_tracePrefix, List.map_map,
              occurrence_id, List.range'_eq_map_range,
              Function.comp_def, atomCount, Nat.add_comm]
          · rw [traceExact]
            simp [invocationIds, TraceEvent.invocationId?,
              List.filterMap_map, Function.comp_def]
            have empty :
                List.filterMap
                    (fun _ : Nat => (none : Option OperationId))
                    (List.range count) = [] := by
              rw [List.filterMap_eq_nil_iff]
              simp
            rw [empty]
            exact List.nodup_nil
          · rw [traceExact]
            simp [reservedNodes, TraceEvent.reservedNode?,
              List.filterMap_map, Function.comp_def]
            have empty :
                List.filterMap
                    (fun _ : Nat => (none : Option NodeId))
                    (List.range count) = [] := by
              rw [List.filterMap_eq_nil_iff]
              simp
            rw [empty]
            exact List.nodup_nil
          · rw [traceExact]
            simp [reservedNodes, TraceEvent.reservedNode?,
              List.filterMap_map, Function.comp_def]
          · intro thread operation node value member
            rw [traceExact] at member ⊢
            simp at member ⊢
            simp_all
          · intro id thread operation node member
            rw [traceExact] at member ⊢
            simp only [List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, List.mem_map] at member
            rcases member with impossible | dynamic
            · simp at impossible
            · obtain ⟨index, indexMember, exactOccurrence⟩ := dynamic
              cases index with
              | zero =>
                  simp [occurrence] at exactOccurrence
                  rcases exactOccurrence with ⟨rfl, rfl, rfl, rfl⟩
                  simp
              | succ index =>
                  cases index with
                  | zero => simp [occurrence] at exactOccurrence
                  | succ index =>
                      cases index with
                      | zero => simp [occurrence] at exactOccurrence
                      | succ index =>
                          cases index with
                          | zero => simp [occurrence] at exactOccurrence
                          | succ retry =>
                              cases phase : retryPhase retry <;>
                                simp [occurrence, phase] at exactOccurrence
          · intro index thread operation node value selected
            have eventMember :=
              List.fst_mem_of_mem_zipIdx selected
            rw [traceExact] at eventMember
            simp only [List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, List.mem_map] at eventMember
            rcases eventMember with impossible | dynamic
            · simp at impossible
            · obtain ⟨atomIndex, _, impossible⟩ := dynamic
              simp at impossible
          · intro validation thread operation head point member
            rw [traceExact] at member
            simp only [List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, List.mem_map] at member
            rcases member with impossible | dynamic
            · simp at impossible
            · obtain ⟨index, _, exactOccurrence⟩ := dynamic
              cases index with
              | zero => simp [occurrence] at exactOccurrence
              | succ index =>
                  cases index with
                  | zero => simp [occurrence] at exactOccurrence
                  | succ index =>
                      cases index with
                      | zero => simp [occurrence] at exactOccurrence
                      | succ index =>
                          cases index with
                          | zero => simp [occurrence] at exactOccurrence
                          | succ retry =>
                              cases phase : retryPhase retry <;>
                                simp [occurrence, phase] at exactOccurrence

/-- Every raw source prefix is a fully valid source-backed RC11 execution. -/
def finitePrefix (length : Nat) :
    SupportedExecution 0 (source.tracePrefix length) where
  sourceWellFormed := sourceWellFormed length
  readSources := prefixReadSources (atomCount length)
  modificationOrder := prefixModificationOrder (atomCount length)
  valid := by
    change Valid (prefixCandidate length)
    rw [prefixCandidate_eq_denseCandidate]
    exact denseCandidate_valid (atomCount length)

theorem denseCandidate_sourceId_eq_readSource
    (count : Nat)
    (atom : Atom Site Ptr)
    (member : atom ∈ (denseCandidate count).atoms) :
    (denseCandidate count).sourceId atom.id =
      readSource atom.id := by
  simp only [denseCandidate, denseAtoms, List.mem_append,
    List.mem_map] at member
  rcases member with static | dynamic
  · simp [staticAtoms] at static
    rcases static with rfl | rfl | rfl
    all_goals
      simp [headInitializer, tailInitializer,
        dummyNextInitializer, readSource]
  · obtain ⟨index, indexMember, rfl⟩ := dynamic
    have indexLt : index < count := by
      simpa using indexMember
    simpa [AtomicOccurrence.toRC11Atom, occurrence_id,
      readSource] using
      denseCandidate_sourceId_occurrence count index indexLt

theorem prefixCandidate_sourceId_eq_readSource
    (length : Nat)
    (atom : Atom Site Ptr)
    (member : atom ∈ (prefixCandidate length).atoms) :
    (prefixCandidate length).sourceId atom.id =
      readSource atom.id := by
  rw [prefixCandidate_eq_denseCandidate] at member ⊢
  exact denseCandidate_sourceId_eq_readSource
    (atomCount length) atom member

/-- A one-write site has no strict finite modification-order edge. -/
theorem denseCandidate_idBefore_modificationOrder_false
    (count : Nat)
    (site : Site)
    (firstId secondId : EventId) :
    ¬ IdBefore firstId secondId
      ((denseCandidate count).modificationOrder site) := by
  intro before
  obtain ⟨first, firstMember, firstLocation, firstIdExact,
    firstWrite⟩ :=
      (denseCandidate_modificationOrder_exact count
        site firstId).1 before.1
  obtain ⟨second, secondMember, secondLocation, secondIdExact,
    secondWrite⟩ :=
      (denseCandidate_modificationOrder_exact count
        site secondId).1 before.2.1
  have sameLocation : first.location = second.location :=
    firstLocation.trans secondLocation.symm
  have equal := denseAtoms_write_eq_of_same_location count
    (by simpa [denseCandidate] using firstMember)
    (by simpa [denseCandidate] using secondMember)
    firstWrite secondWrite sameLocation
  have sameId : firstId = secondId := by
    rw [← firstIdExact, ← secondIdExact, equal]
  exact IdBefore.irreflexive (sameId ▸ before)

theorem prefixCandidate_idBefore_modificationOrder_false
    (length : Nat)
    (site : Site)
    (firstId secondId : EventId) :
    ¬ IdBefore firstId secondId
      ((prefixCandidate length).modificationOrder site) := by
  rw [prefixCandidate_eq_denseCandidate]
  exact denseCandidate_idBefore_modificationOrder_false
    (atomCount length) site firstId secondId

/-- The coherent infinite RC11 carrier shared by every finite prefix. -/
def execution : InfiniteRC11Execution Unit 1 0 where
  source := source
  readSource := readSource
  modificationOrder := fun _ _ _ => False
  modificationOrderIrreflexive := by
    intro site event ordered
    exact ordered
  modificationOrderTransitive := by
    intro site first middle last firstMiddle middleLast
    exact firstMiddle.elim
  finitePrefix := finitePrefix
  prefixReadSource := by
    intro length atom member
    change
      (prefixCandidate length).sourceId atom.id =
        readSource atom.id
    exact prefixCandidate_sourceId_eq_readSource
      length atom member
  prefixModificationOrder := by
    intro length site first second firstMember secondMember
    change
      IdBefore first.id second.id
          ((prefixCandidate length).modificationOrder site) ↔
        False
    constructor
    · exact prefixCandidate_idBefore_modificationOrder_false
        length site first.id second.id
    · intro impossible
      exact impossible.elim

end InfiniteSpurious

end WeakMemory.MSQueue.Source
