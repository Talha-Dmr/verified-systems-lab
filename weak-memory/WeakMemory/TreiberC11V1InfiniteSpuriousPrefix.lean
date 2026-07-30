import WeakMemory.TreiberC11V1InfiniteSpurious

namespace WeakMemory.TreiberC11V1

/-!
# Coherent finite RC11 prefixes of the all-spurious execution

Every dynamic atomic occurrence reads null from the initializer.  Failed weak
CAS attempts do not write, so the only write is the initializer and both the
finite and global modification orders are empty.
-/

namespace InfiniteSpurious

/-- Number of atomic occurrences in the first `length` source events. -/
def atomCount : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | retry + 3 => (retry + 1) / 2 + 1

/-- Dense atomic stream: one load followed by failed weak CAS attempts. -/
def occurrence : Nat → AtomicOccurrence Unit
  | 0 =>
      ⟨1, .pushLoad 0 1 .null⟩
  | retry + 1 =>
      ⟨retry + 2,
        .pushCas 0 1 1 () .null .null false⟩

@[simp] theorem occurrence_id (index : Nat) :
    (occurrence index).id = index + 1 := by
  cases index <;> rfl

/-- Every dynamic read observes the null initializer. -/
def readSource : EventId → Option EventId
  | 0 => none
  | _ + 1 => some 0

/-- There are no global modification-order edges with only one write. -/
def modificationOrder (_first _second : EventId) : Prop :=
  False

/-- Finite RF table for a dense atomic prefix. -/
def prefixReadSources
    (count : Nat) : List (EventId × EventId) :=
  (List.range count).map fun index =>
    (index + 1, 0)

/-- RC11 candidate attached to a finite raw source prefix. -/
def prefixCandidate
    (length : Nat) : RC11.Candidate Unit where
  trace := source.tracePrefix length
  payload := fun _ => ()
  readSources := prefixReadSources (atomCount length)
  modificationOrder := []

/-- Atomic projection of every raw prefix is the dense occurrence prefix. -/
theorem prefixCandidate_nonInitialAtoms
    (length : Nat) :
    (prefixCandidate length).nonInitialAtoms =
      (List.range (atomCount length)).map fun index =>
        .occurrence (occurrence index) := by
  induction length with
  | zero =>
      rfl
  | succ length inductionHypothesis =>
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
      cases length with
      | zero =>
          simp [source, event, atomCount,
            RC11.atomOfTraceEvent?]
      | succ length =>
          cases length with
          | zero =>
              simp [source, event, atomCount, occurrence,
                RC11.atomOfTraceEvent?, List.range_succ]
          | succ length =>
              cases length with
              | zero =>
                  simp [source, event, atomCount,
                    RC11.atomOfTraceEvent?]
              | succ retry =>
                  rcases Nat.mod_two_eq_zero_or_one retry with
                      even | odd
                  · have currentCount :
                        (retry + 1) / 2 + 1 =
                          retry / 2 + 1 := by
                      omega
                    have nextCount :
                        (retry + 2) / 2 + 1 =
                          retry / 2 + 2 := by
                      omega
                    simp [source, event, atomCount, even,
                      occurrence, currentCount, nextCount,
                      RC11.atomOfTraceEvent?, List.range_succ]
                  · have sameCount :
                        (retry + 2) / 2 + 1 =
                          (retry + 1) / 2 + 1 := by
                      omega
                    simp [source, event, atomCount, odd,
                      sameCount, RC11.atomOfTraceEvent?]

/-- Exact atom carrier of a finite prefix. -/
theorem prefixCandidate_atoms
    (length : Nat) :
    (prefixCandidate length).atoms =
      .initial ::
        ((List.range (atomCount length)).map fun index =>
          .occurrence (occurrence index)) := by
  simp [RC11.Candidate.atoms,
    prefixCandidate_nonInitialAtoms]

/-- Atom identifiers are the canonical initial segment. -/
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
  exact occurrence_id index

/-- The full finite write order contains only the initializer. -/
@[simp] theorem prefixCandidate_writeOrder
    (length : Nat) :
    (prefixCandidate length).writeOrder = [0] :=
  rfl

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

/-- RF target identifiers are exactly `1, ..., count`. -/
theorem prefixReadSources_targets
    (count : Nat) :
    (prefixReadSources count).map Prod.fst =
      List.range' 1 count := by
  simp [prefixReadSources, List.map_map,
    List.range'_eq_map_range, Function.comp_def,
    Nat.add_comm]

theorem prefixReadSources_targets_nodup
    (count : Nat) :
    ((prefixReadSources count).map Prod.fst).Nodup := by
  rw [prefixReadSources_targets]
  exact List.nodup_range'

@[simp] theorem prefixCandidate_sourceId_initial
    (length : Nat) :
    (prefixCandidate length).sourceId 0 = none := by
  apply sourceFor_eq_none_of_not_mem
  change
    0 ∉ (prefixReadSources (atomCount length)).map Prod.fst
  rw [prefixReadSources_targets]
  simp

@[simp] theorem prefixCandidate_sourceId_occurrence
    (length index : Nat)
    (inPrefix : index < atomCount length) :
    (prefixCandidate length).sourceId (index + 1) =
      some 0 := by
  apply sourceFor_eq_of_mem
    (prefixReadSources_targets_nodup (atomCount length))
  apply List.mem_map.mpr
  exact
    ⟨index, by simpa using inPrefix, rfl⟩

/-- Finite RF lookup is the global lookup on every carrier atom. -/
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

/-- The serialized RF table is canonical. -/
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
    (project := fun index => (index + 1, 0))]
  · rfl
  intro index indexMember
  have indexLt : index < atomCount length := by
    simpa using indexMember
  simp [prefixCandidate_sourceId_occurrence
    length index indexLt]

@[simp] theorem occurrence_readValue (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).readValue =
      some .null := by
  cases index <;>
    simp [occurrence, RC11.Atom.readValue,
      AtomicAction.readValue]

@[simp] theorem occurrence_not_write (index : Nat) :
    ¬ (RC11.Atom.occurrence (occurrence index)).IsWrite := by
  cases index <;>
    simp [occurrence, RC11.Atom.IsWrite,
      RC11.Atom.writtenValue, AtomicAction.writtenValue]

@[simp] theorem occurrence_not_rmw (index : Nat) :
    ¬ (RC11.Atom.occurrence (occurrence index)).IsRMW := by
  cases index <;>
    simp [occurrence, RC11.Atom.IsRMW,
      RC11.Atom.isRMW, AtomicAction.isRMW]

@[simp] theorem occurrence_hasAcquire (index : Nat) :
    (RC11.Atom.occurrence (occurrence index)).order.hasAcquire =
      false := by
  cases index <;>
    simp [occurrence, RC11.Atom.order,
      AtomicAction.order, MemoryOrder.hasAcquire]

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

/-- Same-thread program order points forward in dense IDs. -/
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

/-- Exact reads-from shape: the initializer supplies one dynamic read. -/
theorem prefixCandidate_rf_shape
    (length : Nat)
    {sourceAtom readAtom : RC11.Atom Unit}
    (edge :
      RC11.RF (prefixCandidate length)
        sourceAtom readAtom) :
    ∃ index,
      index < atomCount length ∧
        readAtom = .occurrence (occurrence index) ∧
        sourceAtom.id = 0 := by
  obtain ⟨_, readMember, chosen⟩ := edge
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
    have sourceExact : sourceAtom.id = 0 := by
      change
        (prefixCandidate length).sourceId
            ((occurrence index).id) =
          some sourceAtom.id at chosen
      rw [occurrence_id,
        prefixCandidate_sourceId_occurrence
          length index indexLt] at chosen
      exact Option.some.inj chosen.symm
    exact ⟨index, indexLt, rfl, sourceExact⟩

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
  simp [RC11.Atom.id, occurrence_id]

/-- A singleton write order induces no strict modification-order edge. -/
theorem prefixCandidate_mo_false
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit} :
    ¬ RC11.MO (prefixCandidate length)
        sourceAtom targetAtom := by
  rintro ⟨_, _, ordered⟩
  change
    sourceAtom.id ∈ [0] ∧
      targetAtom.id ∈ [0] ∧
      [0].idxOf sourceAtom.id <
        [0].idxOf targetAtom.id at ordered
  obtain ⟨sourceZero, targetZero, before⟩ := ordered
  simp only [List.mem_singleton] at sourceZero targetZero
  rw [sourceZero, targetZero] at before
  exact Nat.lt_irrefl _ before

theorem prefixCandidate_rb_false
    (length : Nat)
    {readAtom laterWrite : RC11.Atom Unit} :
    ¬ RC11.RB (prefixCandidate length)
        readAtom laterWrite := by
  rintro ⟨_, _, ordered, _⟩
  exact prefixCandidate_mo_false length ordered

/-- Extended coherence is forward (in fact it consists only of RF paths). -/
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
      exact (prefixCandidate_mo_false length edge).elim
  | readsBefore edge =>
      exact (prefixCandidate_rb_false length edge).elim
  | transitive _ _ firstBefore secondBefore =>
      exact Nat.lt_trans firstBefore secondBefore

/-- Synchronizes-with is empty because every dynamic read is relaxed. -/
theorem prefixCandidate_sw_false
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit} :
    ¬ RC11.SW (prefixCandidate length)
        sourceAtom targetAtom := by
  rintro ⟨_, _, readsFrom, _, targetAcquire⟩
  obtain ⟨index, _, targetExact, _⟩ :=
    prefixCandidate_rf_shape length readsFrom
  subst targetAtom
  simp at targetAcquire

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

/-- The empty write tail contains exactly all non-initial writes: none. -/
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
  · simp [prefixCandidate]
  · rintro ⟨atom, atomMember, _, isWrite, notInitial⟩
    rw [prefixCandidate_atoms] at atomMember
    simp only [List.mem_cons] at atomMember
    rcases atomMember with initial | occurrenceMember
    · subst atom
      simp [RC11.Atom.IsInitial] at notInitial
    · obtain ⟨index, _, atomExact⟩ :=
        List.mem_map.mp occurrenceMember
      subst atom
      exact (occurrence_not_write index isWrite).elim

/-- Unit payload is consistent with all source events. -/
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

/-- Every dynamic read has the initializer as a present, matching source. -/
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
    refine ⟨.initial, by simp [prefixCandidate_atoms], rfl, ?_⟩
    simpa [RC11.Atom.id] using
      prefixCandidate_sourceId_occurrence
        length index indexLt

/-- No dynamic atom is an RMW, so adjacency is vacuous. -/
theorem prefixCandidate_rmwAdjacent
    (length : Nat)
    {sourceAtom rmw : RC11.Atom Unit}
    (_sourceMember :
      sourceAtom ∈ (prefixCandidate length).atoms)
    (rmwMember :
      rmw ∈ (prefixCandidate length).atoms)
    (_chosen :
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
  · obtain ⟨index, _, rmwExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst rmw
    exact (occurrence_not_rmw index rmwShape).elim

/-- Every finite raw prefix satisfies independent RC11. -/
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
  · simp [prefixCandidate]
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

/-- Invocation IDs are either empty or the singleton `[1]`. -/
theorem tracePrefix_invocationIds_nodup
    (length : Nat) :
    (invocationIds (source.tracePrefix length)).Nodup := by
  induction length with
  | zero =>
      simp [InfiniteExecution.tracePrefix,
        invocationIds]
  | succ length inductionHypothesis =>
      rw [InfiniteExecution.tracePrefix_succ]
      rw [invocationIds, List.filterMap_append]
      change
        ((source.tracePrefix length).filterMap invocationId? ++
          [source.event length].filterMap invocationId?).Nodup
      cases length with
      | zero =>
          simp [source, event, invocationId?]
      | succ length =>
          have noInvocation :
              invocationId? (source.event (length + 1)) = none := by
            cases length with
            | zero =>
                rfl
            | succ length =>
                cases length with
                | zero =>
                    rfl
                | succ retry =>
                    by_cases even : retry % 2 = 0
                    · simp [source, event, even, invocationId?]
                    · simp [source, event, even, invocationId?]
          change
            ((source.tracePrefix (length + 1)).filterMap
              invocationId?).Nodup at inductionHypothesis
          simpa [noInvocation] using inductionHypothesis

/-- Reserved push nodes are either empty or the singleton `[1]`. -/
theorem tracePrefix_pushNodes_nodup
    (length : Nat) :
    (pushNodes (source.tracePrefix length)).Nodup := by
  induction length with
  | zero =>
      simp [InfiniteExecution.tracePrefix,
        pushNodes]
  | succ length inductionHypothesis =>
      rw [InfiniteExecution.tracePrefix_succ]
      rw [pushNodes, List.filterMap_append]
      change
        ((source.tracePrefix length).filterMap pushNode? ++
          [source.event length].filterMap pushNode?).Nodup
      cases length with
      | zero =>
          simp [source, event, pushNode?]
      | succ length =>
          have noPush :
              pushNode? (source.event (length + 1)) = none := by
            cases length with
            | zero =>
                rfl
            | succ length =>
                cases length with
                | zero =>
                    rfl
                | succ retry =>
                    by_cases even : retry % 2 = 0
                    · simp [source, event, even, pushNode?]
                    · simp [source, event, even, pushNode?]
          change
            ((source.tracePrefix (length + 1)).filterMap
              pushNode?).Nodup at inductionHypothesis
          simpa [noPush] using inductionHypothesis

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

theorem event_ne_readNext
    (time thread operation node : Nat)
    (next : Ptr) :
    source.event time ≠
      .readNext thread operation node next := by
  cases time with
  | zero =>
      simp [source, event]
  | succ time =>
      cases time with
      | zero =>
          simp [source, event]
      | succ time =>
          cases time with
          | zero =>
              simp [source, event]
          | succ retry =>
              simp [source, event]
              split <;> simp

/-- Every finite candidate satisfies the client contract. -/
theorem prefixCandidate_clientContract
    (length : Nat) :
    ClientContract (prefixCandidate length) := by
  refine {
    globalRun := source.prefix_globalRun length
    invocationIdsNodup := tracePrefix_invocationIds_nodup length
    pushNodesNodup := tracePrefix_pushNodes_nodup length
    payloadAgreement := ?_
    immutableNextReads := ?_
  }
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
    obtain ⟨time, _, eventExact⟩ :=
      List.mem_map.mp member
    exact
      (event_ne_readNext time thread operation node next
        eventExact).elim

/-- No atom in this execution commits a client operation. -/
theorem prefixCandidate_commit_none
    (length : Nat)
    {atom : RC11.Atom Unit}
    (member : atom ∈ (prefixCandidate length).atoms) :
    atom.commitOperation? = none := by
  rw [prefixCandidate_atoms] at member
  simp only [List.mem_cons] at member
  rcases member with initial | occurrenceMember
  · subst atom
    rfl
  · obtain ⟨index, _, atomExact⟩ :=
      List.mem_map.mp occurrenceMember
    subst atom
    cases index <;>
      simp [occurrence, RC11.Atom.commitOperation?]

theorem prefixCandidate_commitRealTime_false
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (sourceMember :
      sourceAtom ∈ (prefixCandidate length).atoms) :
    ¬ CommitRealTimeEdge
        (prefixCandidate length) sourceAtom targetAtom := by
  rintro ⟨first, second, sourceCommit, _, _⟩
  rw [prefixCandidate_commit_none length sourceMember] at sourceCommit
  simp at sourceCommit

theorem prefixCandidate_clientOrderEdge_id_lt
    (length : Nat)
    {sourceAtom targetAtom : RC11.Atom Unit}
    (edge :
      ClientOrderEdge
        (prefixCandidate length) sourceAtom targetAtom) :
    sourceAtom.id < targetAtom.id := by
  obtain ⟨sourceMember, _, programOrder |
      extendedCoherence | realTime⟩ := edge
  · exact prefixCandidate_po_id_lt length programOrder
  · exact prefixCandidate_eco_id_lt length extendedCoherence
  · exact
      (prefixCandidate_commitRealTime_false
        length sourceMember realTime).elim

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

theorem prefixCandidate_clientOrderAcyclic
    (length : Nat) :
    ClientOrderAcyclic (prefixCandidate length) := by
  intro atom cycle
  exact Nat.lt_irrefl atom.id
    (prefixCandidate_clientOrderPath_id_lt length cycle)

/-- Fully declarative execution for every finite raw source prefix. -/
def finitePrefix
    (length : Nat) :
    DeclarativeExecution Unit where
  candidate := prefixCandidate length
  rc11 := prefixCandidate_valid length
  client := prefixCandidate_clientContract length
  clientOrderAcyclic :=
    prefixCandidate_clientOrderAcyclic length

@[simp] theorem finitePrefix_trace
    (length : Nat) :
    (finitePrefix length).candidate.trace =
      source.tracePrefix length :=
  rfl

/-- Every global RF edge has both endpoints in one finite prefix. -/
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
      have sourceExact : sourceId = 0 :=
        Option.some.inj readsFrom.symm
      let length := 2 * index + 2
      have countExact :
          atomCount length = index + 1 := by
        cases index with
        | zero =>
            rfl
        | succ index =>
            change
              atomCount (2 * (index + 1) + 2) =
                index + 1 + 1
            rw [show
              2 * (index + 1) + 2 =
                (2 * index + 1) + 3 by omega]
            simp [atomCount]
            omega
      refine
        ⟨length, .initial,
          .occurrence (occurrence index), ?_, ?_, ?_, ?_⟩
      · simp [finitePrefix, prefixCandidate_atoms]
      · change
          RC11.Atom.occurrence (occurrence index) ∈
            (prefixCandidate length).atoms
        rw [prefixCandidate_atoms]
        simp only [List.mem_cons]
        apply Or.inr
        exact List.mem_map.mpr
          ⟨index, by simp [countExact], rfl⟩
      · simpa [RC11.Atom.id] using sourceExact.symm
      · simp [RC11.Atom.id, occurrence_id]

/-- Finite and global modification order are both empty. -/
theorem prefixCandidate_mo_iff_modificationOrder
    (length : Nat)
    (first second : RC11.Atom Unit)
    (_firstMember : first ∈ (prefixCandidate length).atoms)
    (_secondMember : second ∈ (prefixCandidate length).atoms) :
    RC11.MO (prefixCandidate length) first second ↔
      modificationOrder first.id second.id := by
  constructor
  · exact fun edge =>
      (prefixCandidate_mo_false length edge).elim
  · simp [modificationOrder]

/-- The coherent infinite RC11 all-spurious counterexecution. -/
def execution : InfiniteRC11Execution Unit 1 where
  source := source
  payload := fun _ => ()
  readSource := readSource
  modificationOrder := modificationOrder
  modificationOrderIrreflexive := by
    intro event
    simp [modificationOrder]
  modificationOrderTransitive := by
    intro first middle last firstBefore
    simp [modificationOrder] at firstBefore
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
  modificationOrderSupported := by
    intro firstId secondId ordered
    simp [modificationOrder] at ordered

@[simp] theorem execution_source :
    execution.source = source :=
  rfl

@[simp] theorem execution_readSource :
    execution.readSource = readSource :=
  rfl

@[simp] theorem execution_modificationOrder :
    execution.modificationOrder = modificationOrder :=
  rfl

end InfiniteSpurious

end WeakMemory.TreiberC11V1
