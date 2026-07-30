import WeakMemory.TreiberC11V1InfiniteWitness

namespace WeakMemory.TreiberC11V1

/-!
# Finite declarative prefixes of the concrete infinite witness

This module equips the five-step, one-thread push execution from
`TreiberC11V1InfiniteWitness` with canonical finite RC11 candidates.  Every
finite candidate is a restriction of one global reads-from function and one
global modification order.
-/

namespace InfiniteWitness

/-- Number of atomic occurrences in the first `length` source events. -/
def atomCount (length : Nat) : Nat :=
  2 * (length / 5) +
    match length % 5 with
    | 0 | 1 => 0
    | 2 | 3 => 1
    | _ => 2

/-- The dense, zero-based stream of atomic occurrences. -/
def occurrence (index : Nat) : AtomicOccurrence Unit :=
  let operation := index / 2
  match index % 2 with
  | 0 =>
      ⟨index + 1,
        .pushLoad 0 (operation + 1)
          (priorHead operation)⟩
  | _ =>
      ⟨index + 1,
        .pushCas 0 (operation + 1) (operation + 1) ()
          (priorHead operation) (priorHead operation) true⟩

/-- The write identifier for one modification-order generation. -/
def writeId (generation : Nat) : EventId :=
  2 * generation

/-- Every non-initial atomic read observes the preceding successful push. -/
def readSource : EventId → Option EventId
  | 0 => none
  | target + 1 => some (writeId (target / 2))

/-- Strict global modification order on the initializer and successful CASes. -/
def modificationOrder
    (first second : EventId) : Prop :=
  ∃ firstGeneration secondGeneration,
    first = writeId firstGeneration ∧
      second = writeId secondGeneration ∧
      firstGeneration < secondGeneration

/-- Canonical finite RF serialization for the first `count` occurrences. -/
def prefixReadSources
    (count : Nat) : List (EventId × EventId) :=
  (List.range count).map fun index =>
    (index + 1, writeId (index / 2))

/-- Non-initial writes among the first `count` occurrences. -/
def prefixWriteTail
    (count : Nat) : List EventId :=
  (List.range (count / 2)).map fun generation =>
    writeId (generation + 1)

/-- The RC11 candidate attached to one finite source prefix. -/
def prefixCandidate
    (length : Nat) : RC11.Candidate Unit where
  trace := source.tracePrefix length
  payload := fun _ => ()
  readSources := prefixReadSources (atomCount length)
  modificationOrder := prefixWriteTail (atomCount length)

private theorem phase_cases (time : Nat) :
    time % 5 = 0 ∨
      time % 5 = 1 ∨
      time % 5 = 2 ∨
      time % 5 = 3 ∨
      time % 5 = 4 := by
  omega

/-- Atomic projection of a finite trace is the dense occurrence prefix. -/
theorem prefixCandidate_nonInitialAtoms
    (length : Nat) :
    (prefixCandidate length).nonInitialAtoms =
      (List.range (atomCount length)).map fun index =>
        .occurrence (occurrence index) := by
  induction length with
  | zero =>
      rfl
  | succ length inductionHypothesis =>
      rcases phase_cases length with
          phase | phase | phase | phase | phase
      · have nextDiv : (length + 1) / 5 = length / 5 := by
          omega
        have nextMod : (length + 1) % 5 = 1 := by
          omega
        simp only [prefixCandidate, RC11.Candidate.nonInitialAtoms]
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [List.filterMap_append]
        have densePrefix :
            List.filterMap RC11.atomOfTraceEvent?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map fun index =>
                .occurrence (occurrence index) := by
          simpa [prefixCandidate,
            RC11.Candidate.nonInitialAtoms] using inductionHypothesis
        rw [densePrefix]
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          RC11.atomOfTraceEvent?]
      · have nextDiv : (length + 1) / 5 = length / 5 := by
          omega
        have nextMod : (length + 1) % 5 = 2 := by
          omega
        simp only [prefixCandidate, RC11.Candidate.nonInitialAtoms]
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [List.filterMap_append]
        have densePrefix :
            List.filterMap RC11.atomOfTraceEvent?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map fun index =>
                .occurrence (occurrence index) := by
          simpa [prefixCandidate,
            RC11.Candidate.nonInitialAtoms] using inductionHypothesis
        rw [densePrefix]
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, RC11.atomOfTraceEvent?, List.range_succ]
      · have nextDiv : (length + 1) / 5 = length / 5 := by
          omega
        have nextMod : (length + 1) % 5 = 3 := by
          omega
        simp only [prefixCandidate, RC11.Candidate.nonInitialAtoms]
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [List.filterMap_append]
        have densePrefix :
            List.filterMap RC11.atomOfTraceEvent?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map fun index =>
                .occurrence (occurrence index) := by
          simpa [prefixCandidate,
            RC11.Candidate.nonInitialAtoms] using inductionHypothesis
        rw [densePrefix]
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          RC11.atomOfTraceEvent?, List.range_succ]
      · have nextDiv : (length + 1) / 5 = length / 5 := by
          omega
        have nextMod : (length + 1) % 5 = 4 := by
          omega
        have oddDiv :
            (2 * (length / 5) + 1) / 2 = length / 5 := by
          omega
        simp only [prefixCandidate, RC11.Candidate.nonInitialAtoms]
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [List.filterMap_append]
        have densePrefix :
            List.filterMap RC11.atomOfTraceEvent?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map fun index =>
                .occurrence (occurrence index) := by
          simpa [prefixCandidate,
            RC11.Candidate.nonInitialAtoms] using inductionHypothesis
        rw [densePrefix]
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, RC11.atomOfTraceEvent?, List.range_succ,
          oddDiv]
      · have nextDiv : (length + 1) / 5 = length / 5 + 1 := by
          omega
        have nextMod : (length + 1) % 5 = 0 := by
          omega
        simp only [prefixCandidate, RC11.Candidate.nonInitialAtoms]
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [List.filterMap_append]
        have densePrefix :
            List.filterMap RC11.atomOfTraceEvent?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map fun index =>
                .occurrence (occurrence index) := by
          simpa [prefixCandidate,
            RC11.Candidate.nonInitialAtoms] using inductionHypothesis
        rw [densePrefix]
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          RC11.atomOfTraceEvent?, List.range_succ, Nat.mul_add]

/-- Every generated occurrence carries the next canonical positive ID. -/
@[simp] theorem occurrence_id (index : Nat) :
    (occurrence index).id = index + 1 := by
  simp [occurrence]
  split <;> rfl

/-- Exact atom carrier of a finite witness prefix. -/
theorem prefixCandidate_atoms
    (length : Nat) :
    (prefixCandidate length).atoms =
      .initial ::
        ((List.range (atomCount length)).map fun index =>
          .occurrence (occurrence index)) := by
  simp [RC11.Candidate.atoms,
    prefixCandidate_nonInitialAtoms]

/-- Atom identifiers are the canonical initial segment required by `Valid`. -/
theorem prefixCandidate_atomIds
    (length : Nat) :
    (prefixCandidate length).atomIds =
      List.range (atomCount length + 1) := by
  rw [RC11.Candidate.atomIds, prefixCandidate_atoms]
  simp only [List.map_cons, RC11.Atom.id, List.map_map]
  rw [List.range_succ_eq_map]
  congr 1
  apply List.map_congr_left
  intro index _
  change (occurrence index).id = index + 1
  exact occurrence_id index

/-- The finite write order is the initial segment of even generations. -/
theorem prefixCandidate_writeOrder
    (length : Nat) :
    (prefixCandidate length).writeOrder =
      (List.range (atomCount length / 2 + 1)).map writeId := by
  rw [RC11.Candidate.writeOrder]
  simp only [prefixCandidate, prefixWriteTail]
  rw [List.range_succ_eq_map]
  simp [writeId, List.map_map, Function.comp_def,
    Nat.mul_add]

private theorem sourceFor_eq_of_mem
    {entries : List (EventId × EventId)}
    (targetsNodup : (entries.map Prod.fst).Nodup)
    {target sourceId : EventId}
    (member : (target, sourceId) ∈ entries) :
    RC11.sourceFor entries target = some sourceId := by
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
        simp [RC11.sourceFor]
      · have different : headTarget ≠ target := by
          intro same
          subst headTarget
          exact headFresh
            (List.mem_map.mpr
              ⟨(target, sourceId), tailMember, rfl⟩)
        simp [RC11.sourceFor, different,
          inductionHypothesis tailNodup tailMember]

private theorem sourceFor_eq_none_of_not_mem
    {entries : List (EventId × EventId)}
    {target : EventId}
    (absent : target ∉ entries.map Prod.fst) :
    RC11.sourceFor entries target = none := by
  induction entries with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headTarget, headSource⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      obtain ⟨different, tailAbsent⟩ := absent
      have reversed : headTarget ≠ target :=
        Ne.symm different
      simp [RC11.sourceFor, reversed,
        inductionHypothesis tailAbsent]

private theorem filterMap_eq_map_of_forall
    {items : List β}
    {select : β → Option γ}
    {project : β → γ}
    (exact :
      ∀ item,
        item ∈ items →
          select item = some (project item)) :
    items.filterMap select = items.map project := by
  induction items with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      have headExact : select head = some (project head) :=
        exact head (by simp)
      have tailExact :
          ∀ item,
            item ∈ tail →
              select item = some (project item) :=
        fun item member => exact item (by simp [member])
      simp [headExact, inductionHypothesis tailExact]

/-- RF target identifiers in a prefix are exactly `1, ..., count`. -/
theorem prefixReadSources_targets
    (count : Nat) :
    (prefixReadSources count).map Prod.fst =
      List.range' 1 count := by
  simp [prefixReadSources, List.map_map,
    List.range'_eq_map_range, Function.comp_def,
    Nat.add_comm]

/-- The canonical finite RF table has no duplicate targets. -/
theorem prefixReadSources_targets_nodup
    (count : Nat) :
    ((prefixReadSources count).map Prod.fst).Nodup := by
  rw [prefixReadSources_targets]
  exact List.nodup_range'

/-- The initializer is not a read and has no RF source. -/
@[simp] theorem prefixCandidate_sourceId_initial
    (length : Nat) :
    (prefixCandidate length).sourceId 0 = none := by
  apply sourceFor_eq_none_of_not_mem
  change
    0 ∉ (prefixReadSources (atomCount length)).map Prod.fst
  rw [prefixReadSources_targets]
  simp

/-- Every in-prefix occurrence selects its global preceding write. -/
@[simp] theorem prefixCandidate_sourceId_occurrence
    (length index : Nat)
    (inPrefix : index < atomCount length) :
    (prefixCandidate length).sourceId (index + 1) =
      some (writeId (index / 2)) := by
  apply sourceFor_eq_of_mem
    (prefixReadSources_targets_nodup (atomCount length))
  apply List.mem_map.mpr
  exact
    ⟨index, by simpa using inPrefix, rfl⟩

/-- Finite RF lookup is exactly the global lookup on every carrier atom. -/
theorem prefixCandidate_sourceId_eq_readSource
    (length : Nat)
    (atom : RC11.Atom Unit)
    (member : atom ∈ (prefixCandidate length).atoms) :
    (prefixCandidate length).sourceId atom.id =
      readSource atom.id := by
  rw [prefixCandidate_atoms] at member
  simp only [List.mem_cons] at member
  rcases member with initial | occurrenceMember
  · subst atom
    simp [RC11.Atom.id, readSource]
  · obtain ⟨index, indexMember, atomExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst atom
    have indexLt : index < atomCount length := by
      simpa using indexMember
    simpa [readSource, RC11.Atom.id] using
      prefixCandidate_sourceId_occurrence
        length index indexLt

/-- The serialized RF table is the candidate's canonical fixed point. -/
theorem prefixCandidate_readSourcesCanonical
    (length : Nat) :
    (prefixCandidate length).readSources =
      (prefixCandidate length).canonicalReadSources := by
  rw [RC11.Candidate.canonicalReadSources,
    prefixCandidate_atoms]
  simp only [List.filterMap_cons, RC11.Atom.id,
    prefixCandidate_sourceId_initial, Option.map_none,
    List.filterMap_map]
  change
    prefixReadSources (atomCount length) =
      List.filterMap
        ((fun atom : RC11.Atom Unit =>
          Option.map
            (fun sourceId => (atom.id, sourceId))
            ((prefixCandidate length).sourceId atom.id)) ∘
          fun index => RC11.Atom.occurrence (occurrence index))
        (List.range (atomCount length))
  have projected :
      ((fun atom : RC11.Atom Unit =>
          Option.map
            (fun sourceId => (atom.id, sourceId))
            ((prefixCandidate length).sourceId atom.id)) ∘
        fun index => RC11.Atom.occurrence (occurrence index)) =
        fun index =>
          Option.map
            (fun sourceId => (index + 1, sourceId))
            ((prefixCandidate length).sourceId (index + 1)) := by
    funext index
    change
      Option.map
          (fun sourceId => ((occurrence index).id, sourceId))
          ((prefixCandidate length).sourceId
            (occurrence index).id) =
        Option.map
          (fun sourceId => (index + 1, sourceId))
          ((prefixCandidate length).sourceId (index + 1))
    rw [occurrence_id]
  rw [projected]
  rw [filterMap_eq_map_of_forall
    (project := fun index =>
      (index + 1, writeId (index / 2)))]
  · rfl
  intro index indexMember
  have indexLt : index < atomCount length := by
    simpa using indexMember
  simp [prefixCandidate_sourceId_occurrence
    length index indexLt]

/-- Canonical atom representing one global write generation. -/
def writeAtom : Nat → RC11.Atom Unit
  | 0 =>
      .initial
  | generation + 1 =>
      .occurrence (occurrence (2 * generation + 1))

@[simp] theorem writeAtom_id (generation : Nat) :
    (writeAtom generation).id = writeId generation := by
  cases generation with
  | zero =>
      rfl
  | succ generation =>
      change
        (occurrence (2 * generation + 1)).id =
          writeId (generation + 1)
      rw [occurrence_id]
      simp [writeId, Nat.mul_add]

@[simp] theorem occurrence_readValue (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).readValue =
      some (priorHead (index / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · simp [occurrence, even, RC11.Atom.readValue,
      AtomicAction.readValue]
  · simp [occurrence, odd, RC11.Atom.readValue,
      AtomicAction.readValue]

theorem occurrence_isWrite_iff (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).IsWrite ↔
      index % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · simp [occurrence, even, RC11.Atom.IsWrite,
      RC11.Atom.writtenValue, AtomicAction.writtenValue]
  · simp [occurrence, odd, RC11.Atom.IsWrite,
      RC11.Atom.writtenValue, AtomicAction.writtenValue]

theorem occurrence_isRMW_iff (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).IsRMW ↔
      index % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · simp [occurrence, even, RC11.Atom.IsRMW,
      RC11.Atom.isRMW, AtomicAction.isRMW]
  · simp [occurrence, odd, RC11.Atom.IsRMW,
      RC11.Atom.isRMW, AtomicAction.isRMW]

/-- Every generated atomic action is non-acquiring. -/
@[simp] theorem occurrence_hasAcquire (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).order.hasAcquire =
      false := by
  rcases Nat.mod_two_eq_zero_or_one index with even | odd
  · simp [occurrence, even, RC11.Atom.order,
      AtomicAction.order, MemoryOrder.hasAcquire]
  · simp [occurrence, odd, RC11.Atom.order,
      AtomicAction.order, MemoryOrder.hasAcquire]

/-- A generation writes exactly the pointer read by the next push. -/
theorem writeAtom_writtenValue (generation : Nat) :
    (writeAtom generation).writtenValue =
      some (priorHead generation) := by
  cases generation with
  | zero =>
      rfl
  | succ generation =>
      have odd : (2 * generation + 1) % 2 = 1 := by
        omega
      simp [writeAtom, occurrence, odd,
        RC11.Atom.writtenValue, AtomicAction.writtenValue,
        priorHead]
      omega

/-- The RF source of every in-prefix occurrence is itself in the prefix. -/
theorem writeAtom_mem_of_occurrence_mem
    (length index : Nat)
    (inPrefix : index < atomCount length) :
    writeAtom (index / 2) ∈
      (prefixCandidate length).atoms := by
  rw [prefixCandidate_atoms]
  by_cases initial : index / 2 = 0
  · rw [initial]
    simp [writeAtom]
  · simp only [List.mem_cons]
    apply Or.inr
    apply List.mem_map.mpr
    let sourceIndex := 2 * (index / 2) - 1
    refine ⟨sourceIndex, ?_, ?_⟩
    · simp only [List.mem_range]
      dsimp [sourceIndex]
      omega
    · have generationShape :
          index / 2 = (index / 2 - 1) + 1 := by
        omega
      rw [generationShape]
      simp only [writeAtom]
      congr 2
      dsimp [sourceIndex]
      omega

/-- Numeric write generations have unique identifiers. -/
theorem writeId_injective : Function.Injective writeId := by
  intro first second same
  exact Nat.mul_left_cancel
    (n := 2) (m := first) (k := second)
    (by decide)
    (by simpa [writeId] using same)

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

private theorem writeId_mem_prefix_iff
    {eventId bound : Nat} :
    eventId ∈ (List.range bound).map writeId ↔
      ∃ generation,
        generation < bound ∧
          eventId = writeId generation := by
  constructor
  · intro member
    obtain ⟨generation, generationMember, exactId⟩ :=
      List.mem_map.mp member
    exact
      ⟨generation, by simpa using generationMember,
        exactId.symm⟩
  · rintro ⟨generation, generationLt, rfl⟩
    exact List.mem_map.mpr
      ⟨generation, by simpa using generationLt, rfl⟩

private theorem idxOf_writeId_prefix
    {generation bound : Nat}
    (inRange : generation < bound) :
    ((List.range bound).map writeId).idxOf
        (writeId generation) =
      generation := by
  induction bound with
  | zero =>
      omega
  | succ bound inductionHypothesis =>
      rw [List.range_succ, List.map_append,
        List.idxOf_append]
      by_cases earlier : generation < bound
      · have member :
          writeId generation ∈
            (List.range bound).map writeId :=
          (writeId_mem_prefix_iff).2
            ⟨generation, earlier, rfl⟩
        simp [member, inductionHypothesis earlier]
      · have exactLast : generation = bound := by
          omega
        subst generation
        have absent :
            writeId bound ∉
              (List.range bound).map writeId := by
          intro member
          obtain ⟨earlierGeneration, earlierLt,
              sameId⟩ :=
            (writeId_mem_prefix_iff).1 member
          have sameGeneration :=
            writeId_injective sameId
          omega
        simp [absent]

/-- Strict list position on write IDs is strict generation order. -/
theorem idBefore_writeIds_iff
    {first second bound : Nat} :
    RC11.IdBefore first second
        ((List.range bound).map writeId) ↔
      ∃ firstGeneration secondGeneration,
        firstGeneration < bound ∧
          secondGeneration < bound ∧
          first = writeId firstGeneration ∧
          second = writeId secondGeneration ∧
          firstGeneration < secondGeneration := by
  constructor
  · rintro ⟨firstMember, secondMember, before⟩
    obtain ⟨firstGeneration, firstLt, firstExact⟩ :=
      (writeId_mem_prefix_iff).1 firstMember
    obtain ⟨secondGeneration, secondLt, secondExact⟩ :=
      (writeId_mem_prefix_iff).1 secondMember
    refine
      ⟨firstGeneration, secondGeneration,
        firstLt, secondLt, firstExact, secondExact, ?_⟩
    rw [firstExact,
      idxOf_writeId_prefix firstLt,
      secondExact,
      idxOf_writeId_prefix secondLt] at before
    exact before
  · rintro ⟨firstGeneration, secondGeneration,
      firstLt, secondLt, rfl, rfl, before⟩
    exact
      ⟨(writeId_mem_prefix_iff).2
          ⟨firstGeneration, firstLt, rfl⟩,
        (writeId_mem_prefix_iff).2
          ⟨secondGeneration, secondLt, rfl⟩,
        by simpa [idxOf_writeId_prefix firstLt,
          idxOf_writeId_prefix secondLt]⟩

/--
If an in-prefix atom has a write-generation ID, that generation belongs to
the finite write-order prefix.
-/
theorem writeGeneration_lt_of_atom_mem
    (length : Nat)
    (atom : RC11.Atom Unit)
    (member : atom ∈ (prefixCandidate length).atoms)
    (generation : Nat)
    (sameId : atom.id = writeId generation) :
    generation < atomCount length / 2 + 1 := by
  rw [prefixCandidate_atoms] at member
  simp only [List.mem_cons] at member
  rcases member with initial | occurrenceMember
  · subst atom
    have generationZero : generation = 0 := by
      apply writeId_injective
      simpa [RC11.Atom.id, writeId] using sameId.symm
    omega
  · obtain ⟨index, indexMember, atomExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst atom
    have indexLt : index < atomCount length := by
      simpa using indexMember
    have numeric :
        index + 1 = 2 * generation := by
      simpa [RC11.Atom.id, writeId] using sameId
    omega

/-- Finite MO is exactly the restriction of the global generation order. -/
theorem prefixCandidate_mo_iff_modificationOrder
    (length : Nat)
    (first second : RC11.Atom Unit)
    (firstMember : first ∈ (prefixCandidate length).atoms)
    (secondMember : second ∈ (prefixCandidate length).atoms) :
    RC11.MO (prefixCandidate length) first second ↔
      modificationOrder first.id second.id := by
  simp only [RC11.MO, firstMember, secondMember, true_and]
  rw [prefixCandidate_writeOrder, idBefore_writeIds_iff]
  constructor
  · rintro ⟨firstGeneration, secondGeneration,
      _, _, firstExact, secondExact, before⟩
    exact
      ⟨firstGeneration, secondGeneration,
        firstExact, secondExact, before⟩
  · rintro ⟨firstGeneration, secondGeneration,
      firstExact, secondExact, before⟩
    exact
      ⟨firstGeneration, secondGeneration,
        writeGeneration_lt_of_atom_mem
          length first firstMember firstGeneration firstExact,
        writeGeneration_lt_of_atom_mem
          length second secondMember secondGeneration secondExact,
        firstExact, secondExact, before⟩

/-- Global modification order strictly increases numeric event IDs. -/
theorem modificationOrder_id_lt
    {first second : EventId}
    (ordered : modificationOrder first second) :
    first < second := by
  obtain ⟨firstGeneration, secondGeneration,
      rfl, rfl, before⟩ := ordered
  simp [writeId]
  omega

/-- In-prefix atom identifiers remain injective without assuming `Valid`. -/
theorem prefixCandidate_atom_eq_of_id_eq
    (length : Nat)
    {first second : RC11.Atom Unit}
    (firstMember : first ∈ (prefixCandidate length).atoms)
    (secondMember : second ∈ (prefixCandidate length).atoms)
    (sameId : first.id = second.id) :
    first = second := by
  rw [prefixCandidate_atoms] at firstMember secondMember
  simp only [List.mem_cons] at firstMember secondMember
  rcases firstMember with firstInitial | firstOccurrence
  · subst first
    rcases secondMember with secondInitial | secondOccurrence
    · exact secondInitial.symm
    · obtain ⟨index, _, secondExact⟩ :=
        List.mem_map.mp secondOccurrence
      subst second
      simp [RC11.Atom.id, occurrence_id] at sameId
  · obtain ⟨firstIndex, _, firstExact⟩ :=
      List.mem_map.mp firstOccurrence
    subst first
    rcases secondMember with secondInitial | secondOccurrence
    · subst second
      simp [RC11.Atom.id, occurrence_id] at sameId
    · obtain ⟨secondIndex, _, secondExact⟩ :=
        List.mem_map.mp secondOccurrence
      subst second
      have sameIndex : firstIndex = secondIndex := by
        simpa [RC11.Atom.id, occurrence_id] using sameId
      subst secondIndex
      rfl

/-- Exact shape of a finite reads-from edge. -/
theorem prefixCandidate_rf_shape
    (length : Nat)
    {sourceAtom readAtom : RC11.Atom Unit}
    (edge :
      RC11.RF (prefixCandidate length)
        sourceAtom readAtom) :
    ∃ index,
      index < atomCount length ∧
        readAtom =
          .occurrence (occurrence index) ∧
        sourceAtom.id = writeId (index / 2) := by
  obtain ⟨sourceMember, readMember, chosen⟩ := edge
  rw [prefixCandidate_atoms] at readMember
  simp only [List.mem_cons] at readMember
  rcases readMember with readInitial | readOccurrence
  · subst readAtom
    simp [RC11.Atom.id,
      prefixCandidate_sourceId_initial] at chosen
  · obtain ⟨index, indexMember, readExact⟩ :=
      List.mem_map.mp readOccurrence
    have indexLt : index < atomCount length := by
      simpa using indexMember
    subst readAtom
    have sourceExact :
        sourceAtom.id = writeId (index / 2) := by
      change
        (prefixCandidate length).sourceId
            ((occurrence index).id) =
          some sourceAtom.id at chosen
      rw [occurrence_id] at chosen
      rw [prefixCandidate_sourceId_occurrence
        length index indexLt] at chosen
      exact Option.some.inj chosen.symm
    exact ⟨index, indexLt, rfl, sourceExact⟩

/-- Reads-from always points forward in dense event-ID order. -/
theorem prefixCandidate_rf_id_lt
    (length : Nat)
    {sourceAtom readAtom : RC11.Atom Unit}
    (edge :
      RC11.RF (prefixCandidate length)
        sourceAtom readAtom) :
    sourceAtom.id < readAtom.id := by
  obtain ⟨index, _, rfl, sourceExact⟩ :=
    prefixCandidate_rf_shape length edge
  rw [sourceExact]
  have sourceAtMost :
      2 * (index / 2) ≤ index :=
    Nat.mul_div_le index 2
  simpa [writeId, RC11.Atom.id, occurrence_id] using
    Nat.lt_succ_of_le sourceAtMost

/-- Same-thread program order always points forward in dense IDs. -/
theorem prefixCandidate_po_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (edge :
      RC11.PO (prefixCandidate length)
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  obtain ⟨_, _, _, _, _, ordered⟩ := edge
  rw [prefixCandidate_atomIds] at ordered
  obtain ⟨sourceMember, targetMember, before⟩ := ordered
  have sourceLt : sourceAtom.id < atomCount length + 1 := by
    simpa using sourceMember
  have targetLt : targetAtom.id < atomCount length + 1 := by
    simpa using targetMember
  rwa [idxOf_range_of_lt sourceLt,
    idxOf_range_of_lt targetLt] at before

/-- Finite modification order always points forward in dense IDs. -/
theorem prefixCandidate_mo_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (edge :
      RC11.MO (prefixCandidate length)
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  exact modificationOrder_id_lt
    ((prefixCandidate_mo_iff_modificationOrder
      length sourceAtom targetAtom edge.1 edge.2.1).1 edge)

/-- From-read also points forward; the RMW self-case is explicitly excluded. -/
theorem prefixCandidate_rb_id_lt
    (length : Nat)
    {readAtom laterWrite : RC11.Atom Unit}
    (edge :
      RC11.RB (prefixCandidate length)
        readAtom laterWrite) :
    readAtom.id < laterWrite.id := by
  obtain ⟨sourceAtom, readsFrom, ordered, different⟩ := edge
  obtain ⟨index, _, readExact, sourceExact⟩ :=
    prefixCandidate_rf_shape length readsFrom
  obtain ⟨sourceGeneration, laterGeneration,
      sourceGenerationExact, laterExact, before⟩ :=
    (prefixCandidate_mo_iff_modificationOrder
      length sourceAtom laterWrite ordered.1 ordered.2.1).1
        ordered
  have generationExact : sourceGeneration = index / 2 := by
    apply writeId_injective
    rw [← sourceGenerationExact, sourceExact]
  subst sourceGeneration
  subst readAtom
  have indexBeforeLaterWrite :
      index < laterGeneration * 2 :=
    (Nat.div_lt_iff_lt_mul (k := 2)
      (x := index) (y := laterGeneration)
      (by decide)).1 before
  have numericAtMost :
      index + 1 ≤ 2 * laterGeneration := by
    omega
  have atMost :
      (RC11.Atom.occurrence (occurrence index)).id ≤
        laterWrite.id := by
    rw [laterExact]
    simpa [RC11.Atom.id, occurrence_id, writeId,
      Nat.mul_comm] using numericAtMost
  have idDifferent :
      (RC11.Atom.occurrence (occurrence index)).id ≠
        laterWrite.id := by
    intro sameId
    exact different
      (prefixCandidate_atom_eq_of_id_eq
        length readsFrom.2.1 ordered.2.1 sameId)
  exact Nat.lt_of_le_of_ne atMost idDifferent

/-- Every extended-coherence path points forward in dense IDs. -/
theorem prefixCandidate_eco_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (path :
      RC11.ECO (prefixCandidate length)
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  induction path with
  | readsFrom edge =>
      exact prefixCandidate_rf_id_lt length edge
  | modificationOrder edge =>
      exact prefixCandidate_mo_id_lt length edge
  | readsBefore edge =>
      exact prefixCandidate_rb_id_lt length edge
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

/-- Synchronizes-with is empty because this push-only trace has no acquire. -/
theorem prefixCandidate_sw_false
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit} :
    ¬ RC11.SW (prefixCandidate length)
        sourceAtom targetAtom := by
  rintro ⟨rfSource, _, readsFrom, _, targetAcquire⟩
  obtain ⟨index, _, targetExact, _⟩ :=
    prefixCandidate_rf_shape length readsFrom
  subst targetAtom
  simp at targetAcquire

/-- Happens-before is forward in the push-only finite witness. -/
theorem prefixCandidate_hb_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (path :
      RC11.HB (prefixCandidate length)
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  induction path with
  | programOrder edge =>
      exact prefixCandidate_po_id_lt length edge
  | synchronizesWith edge =>
      exact (prefixCandidate_sw_false length edge).elim
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

/-- Causal order is forward in the push-only finite witness. -/
theorem prefixCandidate_causal_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (path :
      RC11.CausalOrder (prefixCandidate length)
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  induction path with
  | programOrder edge =>
      exact prefixCandidate_po_id_lt length edge
  | readsFrom edge =>
      exact prefixCandidate_rf_id_lt length edge
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

private theorem nodup_map_of_injective
    {items : List β}
    {project : β → γ}
    (injective : Function.Injective project)
    (nodup : items.Nodup) :
    (items.map project).Nodup := by
  induction items with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at nodup ⊢
      obtain ⟨headFresh, tailNodup⟩ := nodup
      constructor
      · intro mappedMember
        obtain ⟨item, itemMember, same⟩ :=
          List.mem_map.mp mappedMember
        exact headFresh
          (injective same.symm ▸ itemMember)
      · exact inductionHypothesis tailNodup

/-- Consecutive generations are adjacent in every containing write prefix. -/
theorem writeId_adjacent
    (generation bound : Nat)
    (nextInRange : generation + 1 < bound) :
    RC11.IdAdjacent
      (writeId generation)
      (writeId (generation + 1))
      ((List.range bound).map writeId) := by
  constructor
  · exact (idBefore_writeIds_iff).2
      ⟨generation, generation + 1,
        Nat.lt_trans (Nat.lt_succ_self generation)
          nextInRange,
        nextInRange, rfl, rfl, Nat.lt_succ_self generation⟩
  · intro middle
    rintro ⟨firstMiddle, middleLast⟩
    obtain ⟨firstGeneration, middleGeneration,
        _, _, firstExact, middleExact, firstBefore⟩ :=
      (idBefore_writeIds_iff).1 firstMiddle
    obtain ⟨middleGeneration', lastGeneration,
        _, _, middleExact', lastExact, lastBefore⟩ :=
      (idBefore_writeIds_iff).1 middleLast
    have firstGenerationExact :
        firstGeneration = generation :=
      writeId_injective (firstExact.symm)
    have middleGenerationExact :
        middleGeneration = middleGeneration' :=
      writeId_injective (middleExact.symm.trans middleExact')
    have lastGenerationExact :
        lastGeneration = generation + 1 :=
      writeId_injective lastExact.symm
    omega

/-- The finite write-tail list contains exactly the non-initial writes. -/
theorem prefixCandidate_writeTailExact
    (length : Nat)
    (eventId : EventId) :
    eventId ∈ (prefixCandidate length).modificationOrder ↔
      ∃ atom,
        atom ∈ (prefixCandidate length).atoms ∧
          atom.id = eventId ∧
          atom.IsWrite ∧
          ¬ atom.IsInitial := by
  constructor
  · intro member
    change
      eventId ∈
        prefixWriteTail (atomCount length) at member
    obtain ⟨generation, generationMember, exactId⟩ :=
      List.mem_map.mp member
    have generationLt :
        generation < atomCount length / 2 := by
      simpa using generationMember
    let atom :=
      RC11.Atom.occurrence
        (occurrence (2 * generation + 1))
    refine ⟨atom, ?_, ?_, ?_, ?_⟩
    · rw [prefixCandidate_atoms]
      simp only [List.mem_cons]
      apply Or.inr
      apply List.mem_map.mpr
      refine
        ⟨2 * generation + 1, ?_, rfl⟩
      simp only [List.mem_range]
      have generationNextLe :
          generation + 1 ≤ atomCount length / 2 := by
        omega
      have doubledLe :
          (generation + 1) * 2 ≤ atomCount length :=
        (Nat.le_div_iff_mul_le (k := 2)
          (x := generation + 1)
          (y := atomCount length)
          (by decide)).1 generationNextLe
      omega
    · change (occurrence (2 * generation + 1)).id = eventId
      rw [occurrence_id]
      rw [← exactId]
      simp [writeId, Nat.mul_add]
    · rw [occurrence_isWrite_iff]
      omega
    · simp [atom, RC11.Atom.IsInitial]
  · rintro ⟨atom, atomMember, atomId,
      isWrite, notInitial⟩
    rw [prefixCandidate_atoms] at atomMember
    simp only [List.mem_cons] at atomMember
    rcases atomMember with initial | occurrenceMember
    · subst atom
      simp [RC11.Atom.IsInitial] at notInitial
    · obtain ⟨index, indexMember, atomExact⟩ :=
        List.mem_map.mp occurrenceMember
      subst atom
      have indexLt : index < atomCount length := by
        simpa using indexMember
      have odd : index % 2 = 1 :=
        (occurrence_isWrite_iff index).1 isWrite
      have divisionShape := Nat.mod_add_div index 2
      have idShape :
          index + 1 = writeId (index / 2 + 1) := by
        simp [writeId]
        omega
      change
        eventId ∈ prefixWriteTail (atomCount length)
      apply List.mem_map.mpr
      refine
        ⟨index / 2, ?_, ?_⟩
      · simp only [List.mem_range]
        have positiveProduct :
            (index / 2 + 1) * 2 ≤
              atomCount length := by
          simp only [Nat.add_mul]
          omega
        exact
          (Nat.le_div_iff_mul_le (k := 2)
            (x := index / 2 + 1)
            (y := atomCount length)
            (by decide)).2 positiveProduct
            |> Nat.lt_of_succ_le
      · rw [← atomId]
        simpa [RC11.Atom.id, occurrence_id] using idShape.symm

/-- The constant `Unit` payload is consistent with every source event. -/
theorem unitPayloadConsistent
    (traceEvent : TraceEvent Unit) :
    RC11.TracePayloadConsistent (fun _ => ()) traceEvent := by
  cases traceEvent with
  | invokePush thread operation node value =>
      cases value
      rfl
  | atomic atomicOccurrence =>
      rcases atomicOccurrence with ⟨id, action⟩
      cases action <;>
        simp [RC11.TracePayloadConsistent,
          RC11.AtomicPayloadConsistent]
  | _ =>
      simp [RC11.TracePayloadConsistent]

/-- Every in-prefix read has a present, value-matching RF source. -/
theorem prefixCandidate_sourceSpec
    (length : Nat)
    (target : RC11.Atom Unit)
    (member : target ∈ (prefixCandidate length).atoms) :
    match target.readValue with
    | none =>
        (prefixCandidate length).sourceId target.id = none
    | some value =>
        ∃ sourceAtom,
          sourceAtom ∈ (prefixCandidate length).atoms ∧
            sourceAtom.writtenValue = some value ∧
            (prefixCandidate length).sourceId target.id =
              some sourceAtom.id := by
  rw [prefixCandidate_atoms] at member
  simp only [List.mem_cons] at member
  rcases member with initial | occurrenceMember
  · subst target
    simp [RC11.Atom.readValue, RC11.Atom.id,
      prefixCandidate_sourceId_initial]
  · obtain ⟨index, indexMember, targetExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst target
    have indexLt : index < atomCount length := by
      simpa using indexMember
    simp only [occurrence_readValue]
    refine
      ⟨writeAtom (index / 2),
        writeAtom_mem_of_occurrence_mem
          length index indexLt,
        writeAtom_writtenValue (index / 2),
        ?_⟩
    change
      (prefixCandidate length).sourceId
          ((occurrence index).id) =
        some (writeAtom (index / 2)).id
    rw [occurrence_id,
      prefixCandidate_sourceId_occurrence
        length index indexLt,
      writeAtom_id]

/-- Successful finite RMWs read from the immediately preceding write. -/
theorem prefixCandidate_rmwAdjacent
    (length : Nat)
    {sourceAtom rmw : RC11.Atom Unit}
    (_sourceMember :
      sourceAtom ∈ (prefixCandidate length).atoms)
    (rmwMember :
      rmw ∈ (prefixCandidate length).atoms)
    (chosen :
      (prefixCandidate length).sourceId rmw.id =
        some sourceAtom.id)
    (rmwShape : rmw.IsRMW) :
    RC11.IdAdjacent sourceAtom.id rmw.id
      (prefixCandidate length).writeOrder := by
  rw [prefixCandidate_atoms] at rmwMember
  simp only [List.mem_cons] at rmwMember
  rcases rmwMember with initial | occurrenceMember
  · subst rmw
    simp [RC11.Atom.IsRMW,
      RC11.Atom.isRMW] at rmwShape
  · obtain ⟨index, indexMember, rmwExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst rmw
    have indexLt : index < atomCount length := by
      simpa using indexMember
    have odd : index % 2 = 1 :=
      (occurrence_isRMW_iff index).1 rmwShape
    change
      (prefixCandidate length).sourceId
          ((occurrence index).id) =
        some sourceAtom.id at chosen
    rw [occurrence_id,
      prefixCandidate_sourceId_occurrence
        length index indexLt] at chosen
    have sourceExact :
        sourceAtom.id = writeId (index / 2) :=
      Option.some.inj chosen.symm
    have divisionShape := Nat.mod_add_div index 2
    have numericId :
        index + 1 = 2 * (index / 2 + 1) := by
      omega
    have rmwExactId :
        (RC11.Atom.occurrence (occurrence index)).id =
          writeId (index / 2 + 1) := by
      simpa [RC11.Atom.id, occurrence_id,
        writeId] using numericId
    have productLe :
        (index / 2 + 1) * 2 ≤
          atomCount length := by
      rw [Nat.mul_comm]
      omega
    have generationInRange :
        index / 2 + 1 <
          atomCount length / 2 + 1 := by
      apply Nat.lt_succ_of_le
      exact
        (Nat.le_div_iff_mul_le (k := 2)
          (x := index / 2 + 1)
          (y := atomCount length)
          (by decide)).2 productLe
    rw [sourceExact, rmwExactId,
      prefixCandidate_writeOrder]
    exact writeId_adjacent
      (index / 2)
      (atomCount length / 2 + 1)
      generationInRange

/-- Every finite prefix candidate satisfies the independent RC11 core. -/
theorem prefixCandidate_valid
    (length : Nat) :
    RC11.Valid (prefixCandidate length) := by
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
  · rw [prefixCandidate_atomIds,
      prefixCandidate_atoms]
    simp
  · rw [prefixCandidate_atomIds]
    exact List.nodup_range
  · intro traceEvent _
    exact unitPayloadConsistent traceEvent
  · exact nodup_map_of_injective
      (fun first second same => by
        have shifted :=
          writeId_injective same
        omega)
      List.nodup_range
  · exact prefixCandidate_writeTailExact length
  · exact prefixCandidate_sourceSpec length
  · exact prefixCandidate_readSourcesCanonical length
  · exact prefixCandidate_rmwAdjacent length
  · intro atom cycle
    exact Nat.lt_irrefl atom.id
      (prefixCandidate_causal_id_lt length cycle)
  · intro sourceAtom middle happensBefore
    have before :=
      prefixCandidate_hb_id_lt length happensBefore
    constructor
    · intro same
      subst middle
      exact Nat.lt_irrefl sourceAtom.id before
    · intro reverse
      exact Nat.lt_asymm before
        (prefixCandidate_eco_id_lt length reverse)

/-- A functional projection with no selected collisions preserves `Nodup`. -/
private theorem filterMap_nodup_of_no_collision
    {items : List β}
    {select : β → Option γ}
    (itemsNodup : items.Nodup)
    (noCollision :
      ∀ {first second output},
        first ∈ items →
        second ∈ items →
        select first = some output →
        select second = some output →
        first = second) :
    (items.filterMap select).Nodup := by
  induction items with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      simp only [List.nodup_cons] at itemsNodup
      obtain ⟨headFresh, tailNodup⟩ := itemsNodup
      cases selected : select head with
      | none =>
          simp [selected]
          exact inductionHypothesis tailNodup
            (fun {first second output}
                firstMember secondMember
                firstSelected secondSelected =>
              noCollision
                (by simp [firstMember])
                (by simp [secondMember])
                firstSelected secondSelected)
      | some output =>
          simp only [List.filterMap_cons, selected,
            List.nodup_cons]
          constructor
          · intro outputMember
            obtain ⟨second, secondMember, secondSelected⟩ :=
              List.mem_filterMap.mp outputMember
            have same :
                head = second :=
              noCollision
                (by simp) (by simp [secondMember])
                selected secondSelected
            subst second
            exact headFresh secondMember
          · exact inductionHypothesis tailNodup
              (fun {first second output}
                  firstMember secondMember
                  firstSelected secondSelected =>
                noCollision
                  (by simp [firstMember])
                  (by simp [secondMember])
                  firstSelected secondSelected)

/-- A selected invocation identifies its unique cycle and operation. -/
theorem invocationId?_event_eq_some
    {time operation : Nat}
    (selected :
      invocationId? (source.event time) =
        some operation) :
    time % 5 = 0 ∧
      operation = time / 5 + 1 := by
  rcases phase_cases time with
      phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase, invocationId?] at selected
  exact ⟨phase, selected.symm⟩

/-- A selected push node identifies its unique source cycle. -/
theorem pushNode?_event_eq_some
    {time node : Nat}
    (selected :
      pushNode? (source.event time) =
        some node) :
    time % 5 = 0 ∧
      node = time / 5 + 1 := by
  rcases phase_cases time with
      phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase, pushNode?] at selected
  exact ⟨phase, selected.symm⟩

/-- Invocation identifiers in every finite source prefix are duplicate-free. -/
theorem tracePrefix_invocationIds_nodup
    (length : Nat) :
    (invocationIds (source.tracePrefix length)).Nodup := by
  unfold invocationIds InfiniteExecution.tracePrefix
  rw [List.filterMap_map]
  apply filterMap_nodup_of_no_collision List.nodup_range
  intro first second operation firstMember secondMember
      firstSelected secondSelected
  obtain ⟨firstPhase, firstOperation⟩ :=
    invocationId?_event_eq_some firstSelected
  obtain ⟨secondPhase, secondOperation⟩ :=
    invocationId?_event_eq_some secondSelected
  have sameQuotient : first / 5 = second / 5 := by
    omega
  have firstShape := Nat.mod_add_div first 5
  have secondShape := Nat.mod_add_div second 5
  omega

/-- Push-reserved node identifiers in every finite prefix are duplicate-free. -/
theorem tracePrefix_pushNodes_nodup
    (length : Nat) :
    (pushNodes (source.tracePrefix length)).Nodup := by
  unfold pushNodes InfiniteExecution.tracePrefix
  rw [List.filterMap_map]
  apply filterMap_nodup_of_no_collision List.nodup_range
  intro first second node firstMember secondMember
      firstSelected secondSelected
  obtain ⟨firstPhase, firstNode⟩ :=
    pushNode?_event_eq_some firstSelected
  obtain ⟨secondPhase, secondNode⟩ :=
    pushNode?_event_eq_some secondSelected
  have sameQuotient : first / 5 = second / 5 := by
    omega
  have firstShape := Nat.mod_add_div first 5
  have secondShape := Nat.mod_add_div second 5
  omega

/-- The constant payload also satisfies the client-facing payload predicate. -/
theorem unitPayloadAgrees
    (traceEvent : TraceEvent Unit) :
    PayloadAgrees (fun _ => ()) traceEvent := by
  cases traceEvent with
  | invokePush thread operation node value =>
      cases value
      rfl
  | atomic atomicOccurrence =>
      rcases atomicOccurrence with ⟨id, action⟩
      cases action <;> simp [PayloadAgrees]
  | _ =>
      simp [PayloadAgrees]

/-- The push-only witness never emits a non-atomic `readNext`. -/
theorem event_ne_readNext
    (time thread operation node : Nat)
    (next : Ptr) :
    source.event time ≠
      .readNext thread operation node next := by
  rcases phase_cases time with
      phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase]

/-- Every finite candidate satisfies the independent client contract. -/
theorem prefixCandidate_clientContract
    (length : Nat) :
    ClientContract (prefixCandidate length) := by
  refine {
    globalRun := ?_
    invocationIdsNodup := ?_
    pushNodesNodup := ?_
    payloadAgreement := ?_
    immutableNextReads := ?_
  }
  · exact source.prefix_globalRun length
  · exact tracePrefix_invocationIds_nodup length
  · exact tracePrefix_pushNodes_nodup length
  · intro traceEvent _
    exact unitPayloadAgrees traceEvent
  · intro leading trailing thread operation node next shape
    have member :
        TraceEvent.readNext thread operation node next ∈
          source.tracePrefix length := by
      change
        source.tracePrefix length =
          leading ++
            .readNext thread operation node next :: trailing
          at shape
      rw [shape]
      simp
    unfold InfiniteExecution.tracePrefix at member
    obtain ⟨time, timeMember, eventExact⟩ :=
      List.mem_map.mp member
    exact
      (event_ne_readNext time thread operation node next
        eventExact).elim

/-- Every committed atom in this prefix belongs to thread zero. -/
theorem prefixCandidate_commit_thread_zero
    (length : Nat)
    {atom : RC11.Atom Unit}
    {operation : ClientOperation}
    (member : atom ∈ (prefixCandidate length).atoms)
    (commits : atom.commitOperation? = some operation) :
    operation.1 = 0 := by
  rw [prefixCandidate_atoms] at member
  simp only [List.mem_cons] at member
  rcases member with initial | occurrenceMember
  · subst atom
    simp [RC11.Atom.commitOperation?] at commits
  · obtain ⟨index, _, atomExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst atom
    rcases Nat.mod_two_eq_zero_or_one index with even | odd
    · simp [occurrence, even,
        RC11.Atom.commitOperation?] at commits
    · simp [occurrence, odd,
        RC11.Atom.commitOperation?] at commits
      rw [← commits]

/-- Cross-thread committed real-time edges are absent in a one-thread prefix. -/
theorem prefixCandidate_commitRealTime_false
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (sourceMember :
      sourceAtom ∈ (prefixCandidate length).atoms)
    (targetMember :
      targetAtom ∈ (prefixCandidate length).atoms) :
    ¬ CommitRealTimeEdge
        (prefixCandidate length) sourceAtom targetAtom := by
  rintro ⟨first, second, sourceCommit,
      targetCommit, realTime⟩
  have firstZero :=
    prefixCandidate_commit_thread_zero
      length sourceMember sourceCommit
  have secondZero :=
    prefixCandidate_commit_thread_zero
      length targetMember targetCommit
  apply realTime.1
  rw [firstZero, secondZero]

/-- Every client-order generator points forward in dense event IDs. -/
theorem prefixCandidate_clientOrderEdge_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (edge :
      ClientOrderEdge
        (prefixCandidate length) sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  obtain ⟨sourceMember, targetMember,
      programOrder | extendedCoherence | realTime⟩ := edge
  · exact prefixCandidate_po_id_lt length programOrder
  · exact prefixCandidate_eco_id_lt length extendedCoherence
  · exact
      (prefixCandidate_commitRealTime_false
        length sourceMember targetMember realTime).elim

/-- Every client-order path points forward in dense event IDs. -/
theorem prefixCandidate_clientOrderPath_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (path :
      Relation.TransGen
        (ClientOrderEdge (prefixCandidate length))
        sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  induction path with
  | single edge =>
      exact prefixCandidate_clientOrderEdge_id_lt
        length edge
  | tail _ edge prefixBefore =>
      exact Nat.lt_trans prefixBefore
        (prefixCandidate_clientOrderEdge_id_lt
          length edge)

/-- Adding client real time preserves acyclicity in every finite prefix. -/
theorem prefixCandidate_clientOrderAcyclic
    (length : Nat) :
    ClientOrderAcyclic (prefixCandidate length) := by
  intro atom cycle
  exact Nat.lt_irrefl atom.id
    (prefixCandidate_clientOrderPath_id_lt length cycle)

/-- One fully declarative RC11 execution for every finite source prefix. -/
def finitePrefix
    (length : Nat) :
    DeclarativeExecution Unit where
  candidate := prefixCandidate length
  rc11 := prefixCandidate_valid length
  client := prefixCandidate_clientContract length
  clientOrderAcyclic :=
    prefixCandidate_clientOrderAcyclic length

@[simp] theorem finitePrefix_candidate
    (length : Nat) :
    (finitePrefix length).candidate =
      prefixCandidate length :=
  rfl

@[simp] theorem finitePrefix_trace
    (length : Nat) :
    (finitePrefix length).candidate.trace =
      source.tracePrefix length :=
  rfl

/-- Every write generation represented by a prefix bound has its carrier atom. -/
theorem writeAtom_mem_of_generation_lt
    (length generation : Nat)
    (inRange :
      generation < atomCount length / 2 + 1) :
    writeAtom generation ∈
      (prefixCandidate length).atoms := by
  rw [prefixCandidate_atoms]
  cases generation with
  | zero =>
      simp [writeAtom]
  | succ generation =>
      simp only [List.mem_cons]
      apply Or.inr
      apply List.mem_map.mpr
      refine
        ⟨2 * generation + 1, ?_, rfl⟩
      simp only [List.mem_range]
      have generationLe :
          generation + 1 ≤ atomCount length / 2 := by
        omega
      have productLe :
          (generation + 1) * 2 ≤
            atomCount length :=
        (Nat.le_div_iff_mul_le (k := 2)
          (x := generation + 1)
          (y := atomCount length)
          (by decide)).1 generationLe
      omega

/-- The global modification order is irreflexive. -/
theorem modificationOrder_irreflexive
    (eventId : EventId) :
    ¬ modificationOrder eventId eventId := by
  rintro ⟨firstGeneration, secondGeneration,
      firstExact, secondExact, before⟩
  have sameGeneration :
      firstGeneration = secondGeneration :=
    writeId_injective
      (firstExact.symm.trans secondExact)
  omega

/-- The global modification order is transitive. -/
theorem modificationOrder_transitive
    {first middle last : EventId}
    (firstBefore :
      modificationOrder first middle)
    (secondBefore :
      modificationOrder middle last) :
    modificationOrder first last := by
  obtain ⟨firstGeneration, middleGeneration,
      firstExact, middleExact, beforeFirst⟩ :=
    firstBefore
  obtain ⟨middleGeneration', lastGeneration,
      middleExact', lastExact, beforeSecond⟩ :=
    secondBefore
  have sameMiddle :
      middleGeneration = middleGeneration' :=
    writeId_injective
      (middleExact.symm.trans middleExact')
  subst middleGeneration'
  exact
    ⟨firstGeneration, lastGeneration,
      firstExact, lastExact,
      Nat.lt_trans beforeFirst beforeSecond⟩

/-- Every global RF association has both endpoints in one finite prefix. -/
theorem readSource_supported
    {targetId sourceId : EventId}
    (readsFrom : readSource targetId = some sourceId) :
    ∃ length,
      ∃ sourceAtom targetAtom : RC11.Atom Unit,
        sourceAtom ∈ (finitePrefix length).candidate.atoms ∧
          targetAtom ∈ (finitePrefix length).candidate.atoms ∧
          sourceAtom.id = sourceId ∧
          targetAtom.id = targetId := by
  cases targetId with
  | zero =>
      simp [readSource] at readsFrom
  | succ index =>
      have sourceExact :
          writeId (index / 2) = sourceId :=
        Option.some.inj readsFrom
      let length := 5 * (index / 2 + 1)
      have atomCountExact :
          atomCount length = 2 * (index / 2 + 1) := by
        simp [length, atomCount]
      have divisionShape := Nat.mod_add_div index 2
      have remainderLt : index % 2 < 2 :=
        Nat.mod_lt index (by decide)
      have targetInRange :
          index < atomCount length := by
        rw [atomCountExact]
        omega
      let sourceAtom := writeAtom (index / 2)
      let targetAtom :=
        RC11.Atom.occurrence (occurrence index)
      refine
        ⟨length, sourceAtom, targetAtom, ?_, ?_, ?_, ?_⟩
      · change
          sourceAtom ∈ (prefixCandidate length).atoms
        apply writeAtom_mem_of_generation_lt
        rw [atomCountExact]
        omega
      · change
          targetAtom ∈ (prefixCandidate length).atoms
        rw [prefixCandidate_atoms]
        simp only [List.mem_cons]
        apply Or.inr
        exact List.mem_map.mpr
          ⟨index, by simpa using targetInRange, rfl⟩
      · dsimp [sourceAtom]
        rw [writeAtom_id, sourceExact]
      · dsimp [targetAtom]
        simp [RC11.Atom.id, occurrence_id]

/-- Every global MO edge has both endpoints in one finite prefix. -/
theorem modificationOrder_supported
    {firstId secondId : EventId}
    (ordered :
      modificationOrder firstId secondId) :
    ∃ length,
      ∃ first second : RC11.Atom Unit,
        first ∈ (finitePrefix length).candidate.atoms ∧
          second ∈ (finitePrefix length).candidate.atoms ∧
          first.id = firstId ∧
          second.id = secondId := by
  obtain ⟨firstGeneration, secondGeneration,
      firstExact, secondExact, before⟩ := ordered
  let length := 5 * secondGeneration
  have atomCountExact :
      atomCount length = 2 * secondGeneration := by
    simp [length, atomCount]
  let first := writeAtom firstGeneration
  let second := writeAtom secondGeneration
  refine ⟨length, first, second, ?_, ?_, ?_, ?_⟩
  · change first ∈ (prefixCandidate length).atoms
    apply writeAtom_mem_of_generation_lt
    rw [atomCountExact]
    omega
  · change second ∈ (prefixCandidate length).atoms
    apply writeAtom_mem_of_generation_lt
    rw [atomCountExact]
    omega
  · dsimp [first]
    rw [writeAtom_id, firstExact]
  · dsimp [second]
    rw [writeAtom_id, secondExact]

/--
The concrete coherent infinite RC11 execution assembled from the uniform
finite declarative family.
-/
def execution : InfiniteRC11Execution Unit 1 where
  source := source
  payload := fun _ => ()
  readSource := readSource
  modificationOrder := modificationOrder
  modificationOrderIrreflexive :=
    modificationOrder_irreflexive
  modificationOrderTransitive :=
    modificationOrder_transitive
  finitePrefix := finitePrefix
  prefixTrace := finitePrefix_trace
  prefixPayload := by
    intro length
    rfl
  prefixReadSource := by
    intro length atom member
    exact prefixCandidate_sourceId_eq_readSource
      length atom member
  readSourceSupported := readSource_supported
  prefixModificationOrder := by
    intro length first second firstMember secondMember
    exact prefixCandidate_mo_iff_modificationOrder
      length first second firstMember secondMember
  modificationOrderSupported :=
    modificationOrder_supported

@[simp] theorem execution_source :
    execution.source = source :=
  rfl

@[simp] theorem execution_readSource :
    execution.readSource = readSource :=
  rfl

@[simp] theorem execution_modificationOrder :
    execution.modificationOrder = modificationOrder :=
  rfl

@[simp] theorem execution_finitePrefix
    (length : Nat) :
    execution.finitePrefix length = finitePrefix length :=
  rfl

end InfiniteWitness

end WeakMemory.TreiberC11V1
