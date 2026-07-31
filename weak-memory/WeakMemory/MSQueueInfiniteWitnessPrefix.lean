import WeakMemory.MSQueueInfiniteWitness
import WeakMemory.MSQueueSourceSchedule

namespace WeakMemory.MSQueue.Source

open MultiLocationRC11

/-!
# Coherent finite RC11 prefixes of the successful infinite queue witness

The dynamic atomic carrier is dense: enqueue `k` contributes identifiers
`6*k+3` through `6*k+8`.  Reads observe either the preceding Tail write or
the initializer of the current tail node.  Per-location modification order
is the identifier-sorted restriction of one global write-site classifier.
-/

namespace InfiniteWitness

/-- Number of dynamic atomic occurrences in the first `length` source events. -/
def atomCount (length : Nat) : Nat :=
  6 * (length / 9) +
    match length % 9 with
    | 0 | 1 | 2 => 0
    | 3 => 1
    | 4 => 2
    | 5 => 3
    | 6 => 4
    | 7 => 5
    | _ => 6

/-- The dense zero-based stream of dynamic atomic occurrences. -/
def occurrence (index : Nat) : AtomicOccurrence Unit :=
  let operation := index / 6
  match index % 6 with
  | 0 =>
      ⟨index + 3,
        .initializeNext 0 (operation + 1) (operation + 1)⟩
  | 1 =>
      ⟨index + 3,
        .enqueueTailLoad 0 (operation + 1) (.node operation)⟩
  | 2 =>
      ⟨index + 3,
        .enqueueNextLoad 0 (operation + 1) operation .null⟩
  | 3 =>
      ⟨index + 3,
        .enqueueTailValidate 0 (operation + 1) (.node operation)⟩
  | 4 =>
      ⟨index + 3,
        .enqueueLinkCAS 0 (operation + 1) operation (operation + 1)
          () .null true⟩
  | _ =>
      ⟨index + 3,
        .enqueueFinishTailCAS 0 (operation + 1) operation
          (operation + 1) (.node operation) true⟩

@[simp] theorem occurrence_id (index : Nat) :
    (occurrence index).id = index + 3 := by
  simp [occurrence]
  split <;> rfl

private theorem source_phase_cases (time : Nat) :
    time % 9 = 0 ∨ time % 9 = 1 ∨ time % 9 = 2 ∨
      time % 9 = 3 ∨ time % 9 = 4 ∨ time % 9 = 5 ∨
      time % 9 = 6 ∨ time % 9 = 7 ∨ time % 9 = 8 := by
  omega

private theorem occurrence_phase_cases (index : Nat) :
    index % 6 = 0 ∨ index % 6 = 1 ∨ index % 6 = 2 ∨
      index % 6 = 3 ∨ index % 6 = 4 ∨ index % 6 = 5 := by
  omega

/-- Atomic projection of a finite source prefix is the dense occurrence prefix. -/
theorem tracePrefix_atomicOccurrences
    (length : Nat) :
    atomicOccurrences (source.tracePrefix length) =
      (List.range (atomCount length)).map occurrence := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      rcases source_phase_cases length with
          phase | phase | phase | phase | phase | phase | phase | phase | phase
      all_goals
        rw [InfiniteExecution.tracePrefix_succ]
        simp only [atomicOccurrences, List.filterMap_append]
        have densePrefix :
            List.filterMap TraceEvent.atomicOccurrence?
                (source.tracePrefix length) =
              (List.range (atomCount length)).map occurrence := by
          simpa [atomicOccurrences] using inductionHypothesis
        rw [densePrefix]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 1 := by omega
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          TraceEvent.atomicOccurrence?]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 2 := by omega
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          TraceEvent.atomicOccurrence?]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 3 := by omega
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 4 := by omega
        have atomDiv : (6 * (length / 9) + 1) / 6 = length / 9 := by
          rw [Nat.mul_add_div (by decide)]
          simp
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, atomDiv, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 5 := by omega
        have atomDiv : (6 * (length / 9) + 2) / 6 = length / 9 := by
          rw [Nat.mul_add_div (by decide)]
          simp
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, atomDiv, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 6 := by omega
        have atomDiv : (6 * (length / 9) + 3) / 6 = length / 9 := by
          rw [Nat.mul_add_div (by decide)]
          simp
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, atomDiv, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 7 := by omega
        have atomDiv : (6 * (length / 9) + 4) / 6 = length / 9 := by
          rw [Nat.mul_add_div (by decide)]
          simp
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, atomDiv, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 := by omega
        have nextMod : (length + 1) % 9 = 8 := by omega
        have atomDiv : (6 * (length / 9) + 5) / 6 = length / 9 := by
          rw [Nat.mul_add_div (by decide)]
          simp
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          occurrence, atomDiv, TraceEvent.atomicOccurrence?, List.range_succ]
      · have nextDiv : (length + 1) / 9 = length / 9 + 1 := by omega
        have nextMod : (length + 1) % 9 = 0 := by omega
        simp [source, event, phase, atomCount, nextDiv, nextMod,
          TraceEvent.atomicOccurrence?, Nat.mul_add]

/-- Exact atom carrier of one witness prefix. -/
def prefixAtoms (length : Nat) : List (Atom Site Ptr) :=
  staticAtoms 0 ++
    (List.range (atomCount length)).map
      (fun index => (occurrence index).toRC11Atom)

private theorem range_three_append (count : Nat) :
    [0, 1, 2] ++ (List.range count).map (fun index => index + 3) =
      List.range (count + 3) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [← List.append_assoc]
      rw [inductionHypothesis]
      have arithmetic : count + 1 + 3 = count + 3 + 1 := by omega
      rw [arithmetic]
      exact List.range_succ.symm

/-- Prefix atom identifiers form the canonical initial segment. -/
theorem prefixAtoms_ids (length : Nat) :
    (prefixAtoms length).map Atom.id =
      List.range (atomCount length + 3) := by
  simp only [prefixAtoms, staticAtoms, List.map_append,
    List.map_cons, List.map_nil, headInitializer, tailInitializer,
    dummyNextInitializer, List.map_map,
    AtomicOccurrence.toRC11Atom, occurrence_id]
  exact range_three_append (atomCount length)

/-- Global location of each write identifier in the concrete run. -/
def writeSite? : EventId → Option Site
  | 0 => some .head
  | 1 => some .tail
  | 2 => some (.next 0)
  | index + 3 =>
      match index % 6 with
      | 0 => some (.next (index / 6 + 1))
      | 4 => some (.next (index / 6))
      | 5 => some .tail
      | _ => none

/-- Tail generation observed during enqueue `operation`. -/
def tailSource (operation : Nat) : EventId :=
  if operation = 0 then 1 else 6 * operation + 2

/-- Null `next` generation observed during enqueue `operation`. -/
def nextSource (operation : Nat) : EventId :=
  if operation = 0 then 2 else 6 * operation - 3

/-- One global reads-from function for all finite witness prefixes. -/
def readSource (target : EventId) : Option EventId :=
  if target < 3 then none
  else
    let index := target - 3
    match index % 6 with
    | 0 => none
    | 1 | 3 | 5 => some (tailSource (index / 6))
    | _ => some (nextSource (index / 6))

/-- Canonical RF serialization restricted to one finite atom carrier. -/
def prefixReadSources (length : Nat) : List (EventId × EventId) :=
  (List.range (atomCount length + 3)).filterMap fun target =>
    (readSource target).map fun sourceId => (target, sourceId)

/-- Identifier-sorted per-site write order restricted to one prefix. -/
def prefixModificationOrder
    (length : Nat)
    (site : Site) : List EventId :=
  (List.range (atomCount length + 3)).filter fun eventId =>
    writeSite? eventId == some site

/-- The RC11 candidate attached to one finite source prefix. -/
def prefixCandidate (length : Nat) : Candidate Site Ptr where
  atoms := prefixAtoms length
  readSources := prefixReadSources length
  modificationOrder := prefixModificationOrder length

@[simp] theorem prefixCandidate_atoms (length : Nat) :
    (prefixCandidate length).atoms = prefixAtoms length :=
  rfl

@[simp] theorem prefixCandidate_atomIds (length : Nat) :
    (prefixCandidate length).atomIds =
      List.range (atomCount length + 3) := by
  exact prefixAtoms_ids length

/-- The candidate carrier is exactly the projection of the source prefix. -/
theorem prefixCandidate_atoms_projected (length : Nat) :
    (prefixCandidate length).atoms =
      projectedAtoms 0 (source.tracePrefix length) := by
  rw [prefixCandidate_atoms, prefixAtoms, projectedAtoms,
    tracePrefix_atomicOccurrences]
  simp [List.map_map]

/-- Generated atoms classify writes through the global write-site function. -/
theorem writeSite?_occurrence (index : Nat) :
    ((occurrence index).toRC11Atom.IsWrite ∧
        writeSite? (occurrence index).id =
          some (occurrence index).toRC11Atom.location) ∨
      (¬ (occurrence index).toRC11Atom.IsWrite ∧
        writeSite? (occurrence index).id = none) := by
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  all_goals
    simp [occurrence, writeSite?, phase,
      AtomicOccurrence.toRC11Atom, AtomicAction.site,
      AtomicAction.access, Atom.IsWrite, Access.IsWrite]

/-- On every represented atom, `writeSite?` exactly recognizes writes. -/
theorem writeSite?_eq_some_iff
    (length : Nat)
    {atom : Atom Site Ptr}
    (member : atom ∈ (prefixCandidate length).atoms)
    (site : Site) :
    writeSite? atom.id = some site ↔
      atom.IsWrite ∧ atom.location = site := by
  rw [prefixCandidate_atoms, prefixAtoms] at member
  simp only [staticAtoms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with static | dynamic
  rcases static with rfl | rfl | rfl
  · simp [writeSite?, headInitializer, Atom.IsWrite,
      Access.IsWrite]
  · simp [writeSite?, tailInitializer, Atom.IsWrite,
      Access.IsWrite]
  · simp [writeSite?, dummyNextInitializer, Atom.IsWrite,
      Access.IsWrite]
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp dynamic
    rcases writeSite?_occurrence index with
        ⟨write, classified⟩ | ⟨notWrite, classified⟩
    · have classified' :
          writeSite? (occurrence index).toRC11Atom.id =
            some (occurrence index).toRC11Atom.location := by
        simpa [AtomicOccurrence.toRC11Atom] using classified
      rw [classified']
      simp [write]
    · have classified' :
          writeSite? (occurrence index).toRC11Atom.id = none := by
        simpa [AtomicOccurrence.toRC11Atom] using classified
      rw [classified']
      simp [notWrite]

private theorem sourceFor_filterMap_eq_none_of_not_mem
    (select : EventId → Option EventId)
    {ids : List EventId}
    {target : EventId}
    (absent : target ∉ ids) :
    sourceFor
        (ids.filterMap fun eventId =>
          (select eventId).map fun sourceId => (eventId, sourceId))
        target = none := by
  induction ids with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons, not_or] at absent
      obtain ⟨headNe, tailAbsent⟩ := absent
      cases selected : select head with
      | none =>
          simp [selected, inductionHypothesis tailAbsent]
      | some sourceId =>
          have reversed : head ≠ target := Ne.symm headNe
          simp [selected, sourceFor, reversed,
            inductionHypothesis tailAbsent]

private theorem sourceFor_filterMap_eq_of_mem
    (select : EventId → Option EventId)
    {ids : List EventId}
    (idsNodup : ids.Nodup)
    {target : EventId}
    (member : target ∈ ids) :
    sourceFor
        (ids.filterMap fun eventId =>
          (select eventId).map fun sourceId => (eventId, sourceId))
        target = select target := by
  induction ids with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp idsNodup
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · subst target
        cases selected : select head with
        | none =>
            simp [selected,
              sourceFor_filterMap_eq_none_of_not_mem
                select parts.1]
        | some sourceId =>
            simp [selected, sourceFor]
      · have different : head ≠ target := by
          intro same
          subst head
          exact parts.1 tailMember
        cases selected : select head with
        | none =>
            simp [selected,
              inductionHypothesis parts.2 tailMember]
        | some sourceId =>
            simp [selected, sourceFor, different,
              inductionHypothesis parts.2 tailMember]

/-- Finite RF lookup is the global RF function on every prefix atom. -/
theorem prefixCandidate_sourceId_eq_readSource
    (length : Nat)
    (atom : Atom Site Ptr)
    (member : atom ∈ (prefixCandidate length).atoms) :
    (prefixCandidate length).sourceId atom.id = readSource atom.id := by
  have idMember : atom.id ∈ List.range (atomCount length + 3) := by
    rw [← prefixCandidate_atomIds]
    exact List.mem_map.mpr ⟨atom, member, rfl⟩
  exact sourceFor_filterMap_eq_of_mem readSource
    List.nodup_range idMember

private theorem filterMap_congr_of_forall_mem
    {items : List α}
    {left right : α → Option β}
    (equal : ∀ item, item ∈ items → left item = right item) :
    items.filterMap left = items.filterMap right := by
  induction items with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headEqual := equal head (by simp)
      have tailEqual := inductionHypothesis
        (fun item member => equal item (by simp [member]))
      cases leftSelected : left head <;>
        cases rightSelected : right head <;>
        simp_all

/-- The serialized RF table is the candidate's canonical fixed point. -/
theorem prefixCandidate_readSourcesCanonical
    (length : Nat) :
    (prefixCandidate length).readSources =
      (prefixCandidate length).canonicalReadSources := by
  rw [Candidate.canonicalReadSources]
  change
    prefixReadSources length =
      (prefixAtoms length).filterMap fun atom =>
        ((prefixCandidate length).sourceId atom.id).map fun sourceId =>
          (atom.id, sourceId)
  unfold prefixReadSources
  rw [← prefixAtoms_ids]
  rw [List.filterMap_map]
  apply filterMap_congr_of_forall_mem
  intro atom member
  have candidateMember : atom ∈ (prefixCandidate length).atoms :=
    member
  simp only [Function.comp_apply]
  rw [prefixCandidate_sourceId_eq_readSource
    length atom candidateMember]

/-- One global strict modification-order relation at every queue site. -/
def modificationOrder
    (site : Site)
    (first second : EventId) : Prop :=
  writeSite? first = some site ∧
    writeSite? second = some site ∧
    first < second

private theorem pair_sublist_of_idBefore
    {first second : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (before : IdBefore first second order) :
    [first, second].Sublist order := by
  induction order with
  | nil =>
      have impossible := before.first_mem
      simp at impossible
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp noDuplicates
      by_cases firstHead : first = head
      · subst head
        have secondNeFirst : second ≠ first := by
          intro same
          subst second
          exact IdBefore.irreflexive before
        have secondMember : second ∈ tail := by
          have member := before.second_mem
          simpa [secondNeFirst] using member
        exact .cons_cons first
          (List.singleton_sublist.mpr secondMember)
      · have firstMember : first ∈ tail := by
          have member := before.first_mem
          simpa [firstHead] using member
        have secondHead : second ≠ head := by
          intro same
          subst head
          have firstNeSecond : first ≠ second := firstHead
          have firstBeq : (second == first) = false :=
            beq_eq_false_iff_ne.mpr firstNeSecond.symm
          have impossible : tail.idxOf first + 1 < 0 := by
            simpa [List.idxOf_cons, firstBeq] using before.2.2
          omega
        have secondMember : second ∈ tail := by
          have member := before.second_mem
          simpa [secondHead] using member
        have headNeFirst : head ≠ first := Ne.symm firstHead
        have headNeSecond : head ≠ second := Ne.symm secondHead
        have tailBefore : IdBefore first second tail := by
          refine ⟨firstMember, secondMember, ?_⟩
          simpa [List.idxOf_cons,
            beq_eq_false_iff_ne.mpr headNeFirst,
            beq_eq_false_iff_ne.mpr headNeSecond] using before.2.2
        exact (inductionHypothesis parts.2 tailBefore).cons head

private theorem lt_of_idBefore_of_pairwise
    {first second : EventId}
    {order : List EventId}
    (sorted : order.Pairwise (fun left right => left < right))
    (noDuplicates : order.Nodup)
    (before : IdBefore first second order) :
    first < second :=
  sorted.forall_sublist
    (pair_sublist_of_idBefore noDuplicates before)

/-- The finite per-site MO list is strictly increasing. -/
theorem prefixModificationOrder_pairwise
    (length : Nat)
    (site : Site) :
    (prefixModificationOrder length site).Pairwise
      (fun first second => first < second) := by
  exact List.pairwise_lt_range.filter _

/-- Membership in one finite per-site write order. -/
theorem mem_prefixModificationOrder_iff
    (length : Nat)
    (site : Site)
    (eventId : EventId) :
    eventId ∈ prefixModificationOrder length site ↔
      eventId < atomCount length + 3 ∧
        writeSite? eventId = some site := by
  simp [prefixModificationOrder]

/-- Finite per-site list order is exactly the global MO restriction. -/
theorem prefixModificationOrder_before_iff
    (length : Nat)
    (site : Site)
    {first second : EventId}
    (firstBound : first < atomCount length + 3)
    (secondBound : second < atomCount length + 3)
    (firstSite : writeSite? first = some site)
    (secondSite : writeSite? second = some site) :
    IdBefore first second (prefixModificationOrder length site) ↔
      first < second := by
  have noDuplicates :
      (prefixModificationOrder length site).Nodup :=
    (List.nodup_range.filter _)
  have firstMember : first ∈ prefixModificationOrder length site :=
    (mem_prefixModificationOrder_iff length site first).2
      ⟨firstBound, firstSite⟩
  have secondMember : second ∈ prefixModificationOrder length site :=
    (mem_prefixModificationOrder_iff length site second).2
      ⟨secondBound, secondSite⟩
  constructor
  · exact lt_of_idBefore_of_pairwise
      (prefixModificationOrder_pairwise length site)
      noDuplicates
  · intro before
    have different : first ≠ second := Nat.ne_of_lt before
    rcases IdBefore.total noDuplicates firstMember secondMember different with
        forward | reverse
    · exact forward
    · have backwards : second < first :=
        lt_of_idBefore_of_pairwise
          (prefixModificationOrder_pairwise length site)
          noDuplicates reverse
      exact (Nat.not_lt_of_ge (Nat.le_of_lt before) backwards).elim

private theorem filterMap_nodup_of_no_collision
    {items : List α}
    {select : α → Option β}
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
  | nil => simp
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp itemsNodup
      cases selected : select head with
      | none =>
          simp [selected]
          exact inductionHypothesis parts.2
            (fun {first second output}
                firstMember secondMember firstSelected secondSelected =>
              noCollision
                (by simp [firstMember]) (by simp [secondMember])
                firstSelected secondSelected)
      | some output =>
          simp only [List.filterMap_cons, selected, List.nodup_cons]
          constructor
          · intro outputMember
            obtain ⟨second, secondMember, secondSelected⟩ :=
              List.mem_filterMap.mp outputMember
            have same := noCollision
              (by simp) (by simp [secondMember])
              selected secondSelected
            subst second
            exact parts.1 secondMember
          · exact inductionHypothesis parts.2
              (fun {first second output}
                  firstMember secondMember firstSelected secondSelected =>
                noCollision
                  (by simp [firstMember]) (by simp [secondMember])
                  firstSelected secondSelected)

/-- A selected invocation identifies its unique enqueue cycle. -/
theorem invocationId?_event_eq_some
    {time operation : Nat}
    (selected :
      TraceEvent.invocationId? (source.event time) = some operation) :
    time % 9 = 0 ∧ operation = time / 9 + 1 := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase, TraceEvent.invocationId?] at selected
  exact ⟨phase, selected.symm⟩

/-- A selected reserved node identifies its unique enqueue cycle. -/
theorem reservedNode?_event_eq_some
    {time node : Nat}
    (selected :
      TraceEvent.reservedNode? (source.event time) = some node) :
    time % 9 = 0 ∧ node = time / 9 + 1 := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase, TraceEvent.reservedNode?] at selected
  exact ⟨phase, selected.symm⟩

/-- Invocation identifiers in every finite source prefix are unique. -/
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
  have sameQuotient : first / 9 = second / 9 := by omega
  have firstShape := Nat.mod_add_div first 9
  have secondShape := Nat.mod_add_div second 9
  omega

/-- Reserved nodes in every finite source prefix are unique. -/
theorem tracePrefix_reservedNodes_nodup
    (length : Nat) :
    (reservedNodes (source.tracePrefix length)).Nodup := by
  unfold reservedNodes InfiniteExecution.tracePrefix
  rw [List.filterMap_map]
  apply filterMap_nodup_of_no_collision List.nodup_range
  intro first second node firstMember secondMember
      firstSelected secondSelected
  obtain ⟨firstPhase, firstNode⟩ :=
    reservedNode?_event_eq_some firstSelected
  obtain ⟨secondPhase, secondNode⟩ :=
    reservedNode?_event_eq_some secondSelected
  have sameQuotient : first / 9 = second / 9 := by omega
  have firstShape := Nat.mod_add_div first 9
  have secondShape := Nat.mod_add_div second 9
  omega

/-- The dummy node is never reserved by the witness client. -/
theorem dummy_not_mem_tracePrefix_reservedNodes
    (length : Nat) :
    0 ∉ reservedNodes (source.tracePrefix length) := by
  intro member
  unfold reservedNodes InfiniteExecution.tracePrefix at member
  rw [List.filterMap_map] at member
  obtain ⟨time, _, selected⟩ := List.mem_filterMap.mp member
  have shape := reservedNode?_event_eq_some selected
  omega

/-- A payload-initialization event has the unique cycle parameters. -/
theorem initializePayload_event_shape
    {time thread operation node : Nat}
    {value : Unit}
    (atTime :
      source.event time =
        .initializePayload thread operation node value) :
    time % 9 = 1 ∧
      thread = 0 ∧
      operation = time / 9 + 1 ∧
      node = time / 9 + 1 := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase] at atTime
  cases value
  obtain ⟨threadExact, operationExact, nodeExact⟩ := atTime
  exact ⟨phase, threadExact.symm, operationExact.symm, nodeExact.symm⟩

/-- A dynamic `next` initializer has the unique cycle parameters. -/
theorem initializeNext_event_shape
    {time id thread operation node : Nat}
    (atTime :
      source.event time =
        .atomic ⟨id, .initializeNext thread operation node⟩) :
    time % 9 = 2 ∧
      id = 6 * (time / 9) + 3 ∧
      thread = 0 ∧
      operation = time / 9 + 1 ∧
      node = time / 9 + 1 := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp [source, event, phase] at atTime
  obtain ⟨idExact, threadExact, operationExact, nodeExact⟩ := atTime
  exact ⟨phase, idExact.symm, threadExact.symm,
    operationExact.symm, nodeExact.symm⟩

private theorem invoke_event_at_cycle (operation : Nat) :
    source.event (9 * operation) =
      .invokeEnqueue 0 (operation + 1) (operation + 1) () := by
  have division : (9 * operation) / 9 = operation := by simp
  simp [source, event, division]

/-- The push-only source emits no payload reads. -/
theorem event_ne_readPayload
    (time thread operation node : Nat)
    (value : Unit) :
    source.event time ≠ .readPayload thread operation node value := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals simp [source, event, phase]

/-- The enqueue-only source emits no empty-dequeue validations. -/
theorem event_ne_emptyValidation
    (time validation thread operation head point : Nat) :
    source.event time ≠
      .atomic ⟨validation,
        .dequeueHeadValidateEmpty thread operation head point⟩ := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals simp [source, event, phase]

/-- Every finite source prefix satisfies the global source discipline. -/
theorem tracePrefix_sourceWellFormed
    (length : Nat) :
    SourceWellFormed 0 (source.tracePrefix length) := by
  refine {
    atomicIdsCanonical := ?_
    invocationIdsNodup := tracePrefix_invocationIds_nodup length
    reservedNodesNodup := tracePrefix_reservedNodes_nodup length
    dummyNotReserved := dummy_not_mem_tracePrefix_reservedNodes length
    threadRuns := ?_
    payloadInitializationMatches := ?_
    nextInitializationMatches := ?_
    payloadReadInitialized := ?_
    emptyAnchor := ?_
  }
  · simp [atomicIds, tracePrefix_atomicOccurrences,
      canonicalDynamicIds, List.range'_eq_map_range,
      List.map_map, Function.comp_def, occurrence_id,
      Nat.add_comm]
  · intro thread
    exact ⟨source.state length thread,
      source.prefix_run thread length⟩
  · intro thread operation node value member
    unfold InfiniteExecution.tracePrefix at member
    obtain ⟨time, timeMember, eventExact⟩ := List.mem_map.mp member
    have timeLt : time < length := by simpa using timeMember
    obtain ⟨phase, threadZero, operationExact, nodeExact⟩ :=
      initializePayload_event_shape eventExact
    subst thread
    subst operation
    subst node
    cases value
    unfold InfiniteExecution.tracePrefix
    apply List.mem_map.mpr
    refine ⟨9 * (time / 9), ?_, ?_⟩
    · simp only [List.mem_range]
      have timeShape := Nat.mod_add_div time 9
      omega
    · exact invoke_event_at_cycle (time / 9)
  · intro id thread operation node member
    unfold InfiniteExecution.tracePrefix at member
    obtain ⟨time, timeMember, eventExact⟩ := List.mem_map.mp member
    have timeLt : time < length := by simpa using timeMember
    obtain ⟨phase, idExact, threadZero, operationExact, nodeExact⟩ :=
      initializeNext_event_shape eventExact
    subst id
    subst thread
    subst operation
    subst node
    refine ⟨(), ?_⟩
    unfold InfiniteExecution.tracePrefix
    apply List.mem_map.mpr
    refine ⟨9 * (time / 9), ?_, ?_⟩
    · simp only [List.mem_range]
      have timeShape := Nat.mod_add_div time 9
      omega
    · exact invoke_event_at_cycle (time / 9)
  · intro index thread operation node value selected
    have eventMember :
        TraceEvent.readPayload thread operation node value ∈
          source.tracePrefix length :=
      List.fst_mem_of_mem_zipIdx selected
    unfold InfiniteExecution.tracePrefix at eventMember
    obtain ⟨time, _, eventExact⟩ := List.mem_map.mp eventMember
    exact (event_ne_readPayload time thread operation node value
      eventExact).elim
  · intro validation thread operation head point member
    unfold InfiniteExecution.tracePrefix at member
    obtain ⟨time, _, eventExact⟩ := List.mem_map.mp member
    exact (event_ne_emptyValidation
      time validation thread operation head point eventExact).elim

/-- Canonical initializer atom for every logical queue site. -/
def initializerAtom : Site → Atom Site Ptr
  | .head => headInitializer 0
  | .tail => tailInitializer 0
  | .next 0 => dummyNextInitializer 0
  | .next (node + 1) => (occurrence (6 * node)).toRC11Atom

@[simp] theorem initializerAtom_location (site : Site) :
    (initializerAtom site).location = site := by
  cases site with
  | head => rfl
  | tail => rfl
  | next node =>
      cases node with
      | zero => rfl
      | succ node =>
          simp [initializerAtom, occurrence,
            AtomicOccurrence.toRC11Atom, AtomicAction.site]

@[simp] theorem initializerAtom_isInitial (site : Site) :
    (initializerAtom site).IsInitial := by
  cases site with
  | head => simp [initializerAtom, headInitializer,
      Atom.IsInitial, Access.IsInitial]
  | tail => simp [initializerAtom, tailInitializer,
      Atom.IsInitial, Access.IsInitial]
  | next node =>
      cases node with
      | zero => simp [initializerAtom, dummyNextInitializer,
          Atom.IsInitial, Access.IsInitial]
      | succ node =>
          simp [initializerAtom, occurrence,
            AtomicOccurrence.toRC11Atom, AtomicAction.access,
            Atom.IsInitial, Access.IsInitial]

/-- All generated dynamic atoms satisfy their declared memory-order constraints. -/
theorem occurrence_orderSupported (index : Nat) :
    (occurrence index).toRC11Atom.access.Allows
      (occurrence index).toRC11Atom.order := by
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  all_goals
    simp [occurrence, phase, AtomicOccurrence.toRC11Atom,
      AtomicAction.access, AtomicAction.order, Access.Allows]

/-- Every dynamic witness atom is owned by thread zero. -/
@[simp] theorem occurrence_thread (index : Nat) :
    (occurrence index).toRC11Atom.thread? = some 0 := by
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  all_goals
    simp [occurrence, phase, AtomicOccurrence.toRC11Atom,
      AtomicAction.thread]

private theorem initializerAtom_mem_of_occurrence
    (length index : Nat)
    (inRange : index < atomCount length) :
    initializerAtom (occurrence index).toRC11Atom.location ∈
      (prefixCandidate length).atoms := by
  rw [prefixCandidate_atoms, prefixAtoms]
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  · apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨index, by simpa using inRange, ?_⟩
    have shape := Nat.mod_add_div index 6
    have exactIndex : 6 * (index / 6) = index := by omega
    simp [occurrence, phase, initializerAtom, exactIndex,
      AtomicOccurrence.toRC11Atom, AtomicAction.site]
  · simp [staticAtoms, initializerAtom, occurrence, phase,
      AtomicOccurrence.toRC11Atom, AtomicAction.site]
  · by_cases first : index / 6 = 0
    · simp [staticAtoms, initializerAtom, occurrence, phase, first,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]
    · apply List.mem_append.mpr
      apply Or.inr
      let sourceIndex := 6 * (index / 6 - 1)
      have shape := Nat.mod_add_div index 6
      have sourceBefore : sourceIndex < index := by
        dsimp [sourceIndex]
        omega
      apply List.mem_map.mpr
      refine ⟨sourceIndex, by simpa using Nat.lt_trans sourceBefore inRange, ?_⟩
      obtain ⟨predecessor, quotient⟩ :=
        Nat.exists_eq_succ_of_ne_zero first
      have sourceIndexExact : sourceIndex = 6 * predecessor := by
        dsimp [sourceIndex]
        omega
      rw [sourceIndexExact]
      simp [occurrence, phase, quotient, initializerAtom,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]
  · simp [staticAtoms, initializerAtom, occurrence, phase,
      AtomicOccurrence.toRC11Atom, AtomicAction.site]
  · by_cases first : index / 6 = 0
    · simp [staticAtoms, initializerAtom, occurrence, phase, first,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]
    · apply List.mem_append.mpr
      apply Or.inr
      let sourceIndex := 6 * (index / 6 - 1)
      have shape := Nat.mod_add_div index 6
      have sourceBefore : sourceIndex < index := by
        dsimp [sourceIndex]
        omega
      apply List.mem_map.mpr
      refine ⟨sourceIndex, by simpa using Nat.lt_trans sourceBefore inRange, ?_⟩
      obtain ⟨predecessor, quotient⟩ :=
        Nat.exists_eq_succ_of_ne_zero first
      have sourceIndexExact : sourceIndex = 6 * predecessor := by
        dsimp [sourceIndex]
        omega
      rw [sourceIndexExact]
      simp [occurrence, phase, quotient, initializerAtom,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]
  · simp [staticAtoms, initializerAtom, occurrence, phase,
      AtomicOccurrence.toRC11Atom, AtomicAction.site]

/-- Every represented site has its canonical initializer in the prefix. -/
theorem initializerAtom_mem_of_represents
    (length : Nat)
    (site : Site)
    (represented : (prefixCandidate length).Represents site) :
    initializerAtom site ∈ (prefixCandidate length).atoms := by
  obtain ⟨atom, member, location⟩ := represented
  rw [← location]
  rw [prefixCandidate_atoms, prefixAtoms] at member
  simp only [staticAtoms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with static | dynamic
  · rcases static with rfl | rfl | rfl
    · simp [initializerAtom, prefixCandidate, prefixAtoms, staticAtoms,
        headInitializer]
    · simp [initializerAtom, prefixCandidate, prefixAtoms, staticAtoms,
        tailInitializer]
    · simp [initializerAtom, prefixCandidate, prefixAtoms, staticAtoms,
        dummyNextInitializer]
  · obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp dynamic
    have inRange : index < atomCount length := by simpa using indexMember
    exact initializerAtom_mem_of_occurrence length index inRange

/-- A represented initial atom is the canonical initializer of its site. -/
theorem initial_eq_initializerAtom
    (length : Nat)
    {atom : Atom Site Ptr}
    (member : atom ∈ (prefixCandidate length).atoms)
    (initial : atom.IsInitial) :
    atom = initializerAtom atom.location := by
  rw [prefixCandidate_atoms, prefixAtoms] at member
  simp only [staticAtoms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with static | dynamic
  · rcases static with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp dynamic
    rcases occurrence_phase_cases index with
        phase | phase | phase | phase | phase | phase
    all_goals
      simp [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, AtomicAction.site, Atom.IsInitial,
        Access.IsInitial] at initial ⊢
    have shape := Nat.mod_add_div index 6
    have exactIndex : 6 * (index / 6) = index := by omega
    rw [← exactIndex]
    simp [occurrence, initializerAtom,
      AtomicOccurrence.toRC11Atom, AtomicAction.site,
      AtomicAction.access]

/-- Canonical initializers are unique at every represented site. -/
theorem prefixCandidate_initializerExistsUnique
    (length : Nat) :
    ∀ site,
      (prefixCandidate length).Represents site →
      ∃ initializer,
        (prefixCandidate length).InitializerAt site initializer ∧
          ∀ other,
            (prefixCandidate length).InitializerAt site other →
            other = initializer := by
  intro site represented
  refine ⟨initializerAtom site, ?_, ?_⟩
  · exact ⟨initializerAtom_mem_of_represents length site represented,
      initializerAtom_location site, initializerAtom_isInitial site⟩
  · intro other otherInitial
    have canonical := initial_eq_initializerAtom
      length otherInitial.1 otherInitial.2.2
    rw [canonical, otherInitial.2.1]

/-- The finite MO lists contain exactly represented writes at their sites. -/
theorem prefixCandidate_modificationOrderExact
    (length : Nat)
    (site : Site)
    (eventId : EventId) :
    eventId ∈ (prefixCandidate length).modificationOrder site ↔
      ∃ atom,
        atom ∈ (prefixCandidate length).atoms ∧
          atom.location = site ∧
          atom.id = eventId ∧
          atom.IsWrite := by
  change eventId ∈ prefixModificationOrder length site ↔ _
  rw [mem_prefixModificationOrder_iff]
  constructor
  · rintro ⟨bound, classified⟩
    have idMember : eventId ∈ (prefixCandidate length).atomIds := by
      rw [prefixCandidate_atomIds]
      simpa using bound
    obtain ⟨atom, atomMember, atomId⟩ := List.mem_map.mp idMember
    have atomClassified : writeSite? atom.id = some site := by
      simpa [atomId] using classified
    have writeShape :=
      (writeSite?_eq_some_iff length atomMember site).1 atomClassified
    exact ⟨atom, atomMember, writeShape.2, atomId, writeShape.1⟩
  · rintro ⟨atom, atomMember, location, rfl, write⟩
    have idMember : atom.id ∈ List.range (atomCount length + 3) := by
      rw [← prefixCandidate_atomIds]
      exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩
    have classified :=
      (writeSite?_eq_some_iff length atomMember site).2
        ⟨write, location⟩
    exact ⟨by simpa using idMember, classified⟩

private theorem initializer_id_lt_of_later_write
    (length : Nat)
    {initializer later : Atom Site Ptr}
    (initializerAt :
      (prefixCandidate length).InitializerAt
        initializer.location initializer)
    (laterMember : later ∈ (prefixCandidate length).atoms)
    (sameLocation : later.location = initializer.location)
    (laterWrite : later.IsWrite)
    (different : later ≠ initializer) :
    initializer.id < later.id := by
  have canonical := initial_eq_initializerAtom
    length initializerAt.1 initializerAt.2.2
  have initializerEq : initializer = initializerAtom later.location := by
    calc
      initializer = initializerAtom initializer.location := canonical
      _ = initializerAtom later.location := by rw [sameLocation]
  rw [initializerEq] at different ⊢
  rw [prefixCandidate_atoms, prefixAtoms] at laterMember
  simp only [staticAtoms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at laterMember
  rcases laterMember with static | dynamic
  · rcases static with rfl | rfl | rfl
    all_goals
      simp [initializerAtom, headInitializer, tailInitializer,
        dummyNextInitializer] at different ⊢
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp dynamic
    rcases occurrence_phase_cases index with
        phase | phase | phase | phase | phase | phase
    all_goals
      simp [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, AtomicAction.site, Atom.IsWrite,
        Access.IsWrite] at laterWrite different ⊢
    · have shape := Nat.mod_add_div index 6
      have exactIndex : 6 * (index / 6) = index := by omega
      apply False.elim
      apply different
      rw [← exactIndex]
      simp [occurrence, initializerAtom,
        AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access]
    · have shape := Nat.mod_add_div index 6
      by_cases first : index / 6 = 0
      · simp [initializerAtom, first, dummyNextInitializer]
      · obtain ⟨predecessor, quotient⟩ :=
        Nat.exists_eq_succ_of_ne_zero first
        rw [phase, quotient] at shape
        rw [quotient]
        simp only [initializerAtom, AtomicOccurrence.toRC11Atom,
          occurrence_id]
        show 6 * predecessor + 3 < index + 3
        omega
    · simp [initializerAtom, tailInitializer]

/-- Every site's initializer is first in finite modification order. -/
theorem prefixCandidate_initializerFirst
    (length : Nat)
    {initializer later : Atom Site Ptr}
    (initializerAt :
      (prefixCandidate length).InitializerAt
        initializer.location initializer)
    (laterMember : later ∈ (prefixCandidate length).atoms)
    (sameLocation : later.location = initializer.location)
    (laterWrite : later.IsWrite)
    (different : later ≠ initializer) :
    IdBefore initializer.id later.id
      ((prefixCandidate length).modificationOrder initializer.location) := by
  have initializerBound : initializer.id < atomCount length + 3 := by
    have member : initializer.id ∈ (prefixCandidate length).atomIds :=
      List.mem_map.mpr ⟨initializer, initializerAt.1, rfl⟩
    rw [prefixCandidate_atomIds] at member
    simpa using member
  have laterBound : later.id < atomCount length + 3 := by
    have member : later.id ∈ (prefixCandidate length).atomIds :=
      List.mem_map.mpr ⟨later, laterMember, rfl⟩
    rw [prefixCandidate_atomIds] at member
    simpa using member
  have initializerSite :=
    (writeSite?_eq_some_iff length initializerAt.1 initializer.location).2
      ⟨(by
          have initInitial := initializerAt.2.2
          change initializer.access.IsWrite
          change initializer.access.IsInitial at initInitial
          generalize initializer.access = access at initInitial ⊢
          cases access <;>
            simp_all [Access.IsInitial, Access.IsWrite]), rfl⟩
  have laterSite :=
    (writeSite?_eq_some_iff length laterMember initializer.location).2
      ⟨laterWrite, sameLocation⟩
  apply (prefixModificationOrder_before_iff
    length initializer.location initializerBound laterBound
    initializerSite laterSite).2
  exact initializer_id_lt_of_later_write length initializerAt
    laterMember sameLocation laterWrite different

/-- Atom supplying the current Tail generation to enqueue `operation`. -/
def tailSourceAtom : Nat → Atom Site Ptr
  | 0 => tailInitializer 0
  | operation + 1 =>
      (occurrence (6 * operation + 5)).toRC11Atom

/-- Atom supplying null from `next(operation)` before its successful link. -/
def nextSourceAtom : Nat → Atom Site Ptr
  | 0 => dummyNextInitializer 0
  | operation + 1 =>
      (occurrence (6 * operation)).toRC11Atom

@[simp] theorem tailSourceAtom_id (operation : Nat) :
    (tailSourceAtom operation).id = tailSource operation := by
  cases operation with
  | zero => rfl
  | succ operation =>
      change (occurrence (6 * operation + 5)).id =
        6 * (operation + 1) + 2
      rw [occurrence_id]
      simp [Nat.mul_add, Nat.add_assoc]

@[simp] theorem nextSourceAtom_id (operation : Nat) :
    (nextSourceAtom operation).id = nextSource operation := by
  cases operation with
  | zero => rfl
  | succ operation =>
      change (occurrence (6 * operation)).id =
        6 * (operation + 1) - 3
      rw [occurrence_id]
      simp [Nat.mul_add, Nat.add_sub_assoc]

@[simp] theorem tailSourceAtom_location (operation : Nat) :
    (tailSourceAtom operation).location = .tail := by
  cases operation with
  | zero => rfl
  | succ operation =>
      simp [tailSourceAtom, occurrence,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]

@[simp] theorem nextSourceAtom_location (operation : Nat) :
    (nextSourceAtom operation).location = .next operation := by
  cases operation with
  | zero => rfl
  | succ operation =>
      simp [nextSourceAtom, occurrence,
        AtomicOccurrence.toRC11Atom, AtomicAction.site]

@[simp] theorem tailSourceAtom_writtenValue (operation : Nat) :
    (tailSourceAtom operation).writtenValue = some (.node operation) := by
  cases operation with
  | zero => rfl
  | succ operation =>
      simp [tailSourceAtom, occurrence,
        AtomicOccurrence.toRC11Atom, AtomicAction.access,
        Atom.writtenValue, Access.writtenValue]
      omega

@[simp] theorem nextSourceAtom_writtenValue (operation : Nat) :
    (nextSourceAtom operation).writtenValue = some .null := by
  cases operation with
  | zero => rfl
  | succ operation =>
      simp [nextSourceAtom, occurrence,
        AtomicOccurrence.toRC11Atom, AtomicAction.access,
        Atom.writtenValue, Access.writtenValue]

private theorem tailSourceAtom_mem_of_occurrence
    (length index : Nat)
    (inRange : index < atomCount length)
    (tailPhase : index % 6 = 1 ∨ index % 6 = 3 ∨ index % 6 = 5) :
    tailSourceAtom (index / 6) ∈ (prefixCandidate length).atoms := by
  rw [prefixCandidate_atoms, prefixAtoms]
  cases operationEq : index / 6 with
  | zero =>
      simp [tailSourceAtom, staticAtoms]
  | succ operation =>
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨6 * operation + 5, ?_, ?_⟩
      simp only [List.mem_range]
      have shape := Nat.mod_add_div index 6
      rcases tailPhase with phase | phase | phase <;>
        rw [phase, operationEq] at shape <;>
        omega
      rfl

private theorem nextSourceAtom_mem_of_occurrence
    (length index : Nat)
    (inRange : index < atomCount length)
    (nextPhase : index % 6 = 2 ∨ index % 6 = 4) :
    nextSourceAtom (index / 6) ∈ (prefixCandidate length).atoms := by
  rw [prefixCandidate_atoms, prefixAtoms]
  cases operationEq : index / 6 with
  | zero =>
      simp [nextSourceAtom, staticAtoms]
  | succ operation =>
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨6 * operation, ?_, ?_⟩
      simp only [List.mem_range]
      have shape := Nat.mod_add_div index 6
      rcases nextPhase with phase | phase <;>
        rw [phase, operationEq] at shape <;>
        omega
      rfl

/-- Every represented read has its typed source in the same prefix. -/
theorem prefixCandidate_sourceSpec
    (length : Nat) :
    ∀ target,
      target ∈ (prefixCandidate length).atoms →
      match target.readValue with
      | none => (prefixCandidate length).sourceId target.id = none
      | some value =>
          ∃ source,
            source ∈ (prefixCandidate length).atoms ∧
              source.location = target.location ∧
              source.writtenValue = some value ∧
              (prefixCandidate length).sourceId target.id = some source.id := by
  intro target member
  rw [prefixCandidate_atoms, prefixAtoms] at member
  simp only [staticAtoms, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with static | dynamic
  · rcases static with rfl | rfl | rfl
    all_goals
      rw [prefixCandidate_sourceId_eq_readSource]
      simp [headInitializer, tailInitializer, dummyNextInitializer,
        readSource, Atom.readValue, Access.readValue]
      simp [prefixCandidate, prefixAtoms, staticAtoms]
  · obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp dynamic
    have inRange : index < atomCount length := by simpa using indexMember
    have sourceRestriction := prefixCandidate_sourceId_eq_readSource
      length (occurrence index).toRC11Atom
      (by
        rw [prefixCandidate_atoms, prefixAtoms]
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨index, indexMember, rfl⟩)))
    have targetNotSmall : ¬ index + 3 < 3 := by omega
    rcases occurrence_phase_cases index with
        phase | phase | phase | phase | phase | phase
    · simpa [occurrence, phase, readSource,
        AtomicOccurrence.toRC11Atom, AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction
    · simp only [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.readValue, Access.readValue]
      refine ⟨tailSourceAtom (index / 6),
        tailSourceAtom_mem_of_occurrence length index inRange
          (Or.inl phase), ?_⟩
      simpa [occurrence, phase, readSource,
        targetNotSmall, AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction
    · simp only [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.readValue, Access.readValue]
      refine ⟨nextSourceAtom (index / 6),
        nextSourceAtom_mem_of_occurrence length index inRange
          (Or.inl phase), ?_⟩
      simpa [occurrence, phase, readSource,
        targetNotSmall, AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction
    · simp only [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.readValue, Access.readValue]
      refine ⟨tailSourceAtom (index / 6),
        tailSourceAtom_mem_of_occurrence length index inRange
          (Or.inr (Or.inl phase)), ?_⟩
      simpa [occurrence, phase, readSource,
        targetNotSmall, AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction
    · simp only [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.readValue, Access.readValue]
      refine ⟨nextSourceAtom (index / 6),
        nextSourceAtom_mem_of_occurrence length index inRange
          (Or.inr phase), ?_⟩
      simpa [occurrence, phase, readSource,
        targetNotSmall, AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction
    · simp only [occurrence, phase, AtomicOccurrence.toRC11Atom,
        AtomicAction.access, Atom.readValue, Access.readValue]
      refine ⟨tailSourceAtom (index / 6),
        tailSourceAtom_mem_of_occurrence length index inRange
          (Or.inr (Or.inr phase)), ?_⟩
      simpa [occurrence, phase, readSource,
        targetNotSmall, AtomicOccurrence.toRC11Atom, AtomicAction.site,
        AtomicAction.access,
        Atom.readValue, Access.readValue] using sourceRestriction

/-- Tail writes are exactly the initializer and successful finish CASes. -/
theorem writeSite?_tail_iff (eventId : EventId) :
    writeSite? eventId = some .tail ↔
      eventId = 1 ∨ ∃ operation, eventId = 6 * operation + 8 := by
  rcases eventId with _ | _ | _ | index
  · simp [writeSite?]
  · simp [writeSite?]
  · simp [writeSite?]
  · rcases occurrence_phase_cases index with
        phase | phase | phase | phase | phase | phase
    all_goals have shape := Nat.mod_add_div index 6
    · simp [writeSite?, phase]
      intro operation equal
      omega
    · simp [writeSite?, phase]
      intro operation equal
      omega
    · simp [writeSite?, phase]
      intro operation equal
      omega
    · simp [writeSite?, phase]
      intro operation equal
      omega
    · simp [writeSite?, phase]
      intro operation equal
      omega
    · simp [writeSite?, phase]
      exact ⟨index / 6, by omega⟩

/-- Writes at `next node` are its initializer and eventual successful link. -/
theorem writeSite?_next_iff (eventId node : Nat) :
    writeSite? eventId = some (.next node) ↔
      (node = 0 ∧ eventId = 2) ∨
        (∃ operation, node = operation + 1 ∧
          eventId = 6 * operation + 3) ∨
        (∃ operation, node = operation ∧
          eventId = 6 * operation + 7) := by
  rcases eventId with _ | _ | _ | index
  · simp [writeSite?]
  · simp [writeSite?]
  · simp [writeSite?, eq_comm]
  · rcases occurrence_phase_cases index with
        phase | phase | phase | phase | phase | phase
    all_goals have shape := Nat.mod_add_div index 6
    · constructor
      · intro selected
        have nodeExact : node = index / 6 + 1 := by
          simpa [writeSite?, phase] using selected.symm
        exact Or.inr (Or.inl
          ⟨index / 6, nodeExact, by omega⟩)
      · rintro (static | ⟨operation, nodeExact, idExact⟩ |
          ⟨operation, nodeExact, idExact⟩)
        · omega
        · have indexExact : index = 6 * operation := by omega
          subst index
          simp [writeSite?, nodeExact]
        · omega
    · simp [writeSite?, phase]
      constructor
      · intro operation nodeExact idExact
        omega
      · intro idExact
        omega
    · simp [writeSite?, phase]
      constructor
      · intro operation nodeExact idExact
        omega
      · intro idExact
        omega
    · simp [writeSite?, phase]
      constructor
      · intro operation nodeExact idExact
        omega
      · intro idExact
        omega
    · constructor
      · intro selected
        have nodeExact : node = index / 6 := by
          simpa [writeSite?, phase] using selected.symm
        exact Or.inr (Or.inr
          ⟨index / 6, nodeExact, by omega⟩)
      · rintro (static | ⟨operation, nodeExact, idExact⟩ |
          ⟨operation, nodeExact, idExact⟩)
        · omega
        · omega
        · have indexExact : index = 6 * operation + 4 := by omega
          subst index
          have quotient : (6 * operation + 4) / 6 = operation := by
            rw [Nat.mul_add_div (by decide)]
            simp
          simp [writeSite?, nodeExact, quotient]
    · simp [writeSite?, phase]
      constructor
      · intro operation nodeExact idExact
        omega
      · intro idExact
        omega

@[simp] theorem writeSite?_tailSource (operation : Nat) :
    writeSite? (tailSource operation) = some .tail := by
  cases operation with
  | zero => rfl
  | succ operation =>
      apply (writeSite?_tail_iff _).2
      right
      exact ⟨operation, by
        simp [tailSource, Nat.mul_add, Nat.add_assoc]⟩

@[simp] theorem writeSite?_nextSource (operation : Nat) :
    writeSite? (nextSource operation) = some (.next operation) := by
  cases operation with
  | zero => rfl
  | succ operation =>
      apply (writeSite?_next_iff _ _).2
      right
      left
      exact ⟨operation, rfl, by
        simp [nextSource, Nat.mul_add, Nat.add_sub_assoc]⟩

private theorem phaseTwo_before_link (scaled : Nat) :
    2 + scaled + 3 ≤ scaled + 7 := by omega

private theorem phaseFour_at_link (scaled : Nat) :
    4 + scaled + 3 ≤ scaled + 7 := by omega

private theorem tailPhaseOne_sourceBefore (scaled : Nat) :
    scaled + 8 < 1 + (scaled + 6) + 3 := by omega

private theorem nextPhaseTwo_sourceBefore (scaled : Nat) :
    scaled < 2 + (scaled + 6) := by omega

private theorem tailPhaseThree_sourceBefore (scaled : Nat) :
    scaled + 8 < 3 + (scaled + 6) + 3 := by omega

private theorem nextPhaseFour_sourceBefore (scaled : Nat) :
    scaled < 4 + (scaled + 6) := by omega

private theorem tailPhaseFive_sourceBefore (scaled : Nat) :
    scaled + 8 < 5 + (scaled + 6) + 3 := by omega

/-- A read target is no later than every MO-later write after its source. -/
theorem readSource_target_le_of_modificationOrder
    {target sourceId write : EventId}
    {site : Site}
    (readsFrom : readSource target = some sourceId)
    (ordered : modificationOrder site sourceId write) :
    target ≤ write := by
  obtain ⟨sourceSite, writeSite, sourceBefore⟩ := ordered
  have targetAtLeast : 3 ≤ target := by
    by_cases targetSmall : target < 3
    · simp [readSource, targetSmall] at readsFrom
    · exact Nat.le_of_not_gt targetSmall
  obtain ⟨index, targetExact⟩ :=
    Nat.exists_eq_add_of_le targetAtLeast
  subst target
  rw [Nat.add_comm 3 index] at readsFrom ⊢
  have targetNotSmall : ¬ index + 3 < 3 := by omega
  have shape := Nat.mod_add_div index 6
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  · simp [readSource, targetNotSmall, phase] at readsFrom
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at readsFrom
    have sourceExact : sourceId = tailSource (index / 6) := readsFrom.symm
    subst sourceId
    have siteExact : site = .tail := by
      rw [writeSite?_tailSource] at sourceSite
      exact (Option.some.inj sourceSite).symm
    subst site
    rcases (writeSite?_tail_iff write).1 writeSite with
        rfl | ⟨operation, rfl⟩
    · cases quotient : index / 6 <;>
        simp [tailSource, quotient] at sourceBefore
    · cases quotient : index / 6 with
      | zero =>
          rw [quotient] at shape
          exact Nat.le_trans (by omega)
            (Nat.le_add_left 8 (6 * operation))
      | succ predecessor =>
          rw [quotient] at shape
          have normalized :
              6 * predecessor + 8 < 6 * operation + 8 := by
            simpa [tailSource, quotient, Nat.mul_add,
              Nat.add_assoc] using sourceBefore
          have predecessorLt : predecessor < operation :=
            Nat.lt_of_mul_lt_mul_left
              ((Nat.add_lt_add_iff_right).mp normalized)
          exact Nat.le_trans (by omega)
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 6 predecessorLt) 8)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at readsFrom
    have sourceExact : sourceId = nextSource (index / 6) := readsFrom.symm
    subst sourceId
    have siteExact : site = .next (index / 6) := by
      rw [writeSite?_nextSource] at sourceSite
      exact (Option.some.inj sourceSite).symm
    subst site
    rcases (writeSite?_next_iff write (index / 6)).1 writeSite with
        ⟨nodeZero, rfl⟩ |
        ⟨operation, nodeExact, rfl⟩ |
        ⟨operation, nodeExact, rfl⟩
    · rw [nodeZero] at shape
      simp [nextSource, nodeZero] at sourceBefore
    · cases quotient : index / 6 with
      | zero =>
          rw [quotient] at shape
          omega
      | succ predecessor =>
          rw [quotient] at shape
          simp [nextSource, quotient, Nat.mul_add,
            Nat.add_sub_assoc] at sourceBefore
          omega
    · rw [nodeExact] at shape
      rw [← shape]
      exact phaseTwo_before_link (6 * operation)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at readsFrom
    have sourceExact : sourceId = tailSource (index / 6) := readsFrom.symm
    subst sourceId
    have siteExact : site = .tail := by
      rw [writeSite?_tailSource] at sourceSite
      exact (Option.some.inj sourceSite).symm
    subst site
    rcases (writeSite?_tail_iff write).1 writeSite with
        rfl | ⟨operation, rfl⟩
    · cases quotient : index / 6 <;>
        simp [tailSource, quotient] at sourceBefore
    · cases quotient : index / 6 with
      | zero =>
          rw [quotient] at shape
          exact Nat.le_trans (by omega)
            (Nat.le_add_left 8 (6 * operation))
      | succ predecessor =>
          rw [quotient] at shape
          have normalized :
              6 * predecessor + 8 < 6 * operation + 8 := by
            simpa [tailSource, quotient, Nat.mul_add,
              Nat.add_assoc] using sourceBefore
          have predecessorLt : predecessor < operation :=
            Nat.lt_of_mul_lt_mul_left
              ((Nat.add_lt_add_iff_right).mp normalized)
          exact Nat.le_trans (by omega)
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 6 predecessorLt) 8)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at readsFrom
    have sourceExact : sourceId = nextSource (index / 6) := readsFrom.symm
    subst sourceId
    have siteExact : site = .next (index / 6) := by
      rw [writeSite?_nextSource] at sourceSite
      exact (Option.some.inj sourceSite).symm
    subst site
    rcases (writeSite?_next_iff write (index / 6)).1 writeSite with
        ⟨nodeZero, rfl⟩ |
        ⟨operation, nodeExact, rfl⟩ |
        ⟨operation, nodeExact, rfl⟩
    · rw [nodeZero] at shape
      simp [nextSource, nodeZero] at sourceBefore
    · cases quotient : index / 6 with
      | zero =>
          rw [quotient] at shape
          omega
      | succ predecessor =>
          rw [quotient] at shape
          simp [nextSource, quotient, Nat.mul_add,
            Nat.add_sub_assoc] at sourceBefore
          omega
    · rw [nodeExact] at shape
      rw [← shape]
      exact phaseFour_at_link (6 * operation)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at readsFrom
    have sourceExact : sourceId = tailSource (index / 6) := readsFrom.symm
    subst sourceId
    have siteExact : site = .tail := by
      rw [writeSite?_tailSource] at sourceSite
      exact (Option.some.inj sourceSite).symm
    subst site
    rcases (writeSite?_tail_iff write).1 writeSite with
        rfl | ⟨operation, rfl⟩
    · cases quotient : index / 6 <;>
        simp [tailSource, quotient] at sourceBefore
    · cases quotient : index / 6 with
      | zero =>
          rw [quotient] at shape
          exact Nat.le_trans (by omega)
            (Nat.le_add_left 8 (6 * operation))
      | succ predecessor =>
          rw [quotient] at shape
          have normalized :
              6 * predecessor + 8 < 6 * operation + 8 := by
            simpa [tailSource, quotient, Nat.mul_add,
              Nat.add_assoc] using sourceBefore
          have predecessorLt : predecessor < operation :=
            Nat.lt_of_mul_lt_mul_left
              ((Nat.add_lt_add_iff_right).mp normalized)
          exact Nat.le_trans (by omega)
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 6 predecessorLt) 8)

/-- Every selected RF source is chronologically earlier than its target. -/
theorem readSource_source_lt_target
    {target sourceId : EventId}
    (selected : readSource target = some sourceId) :
    sourceId < target := by
  have targetAtLeast : 3 ≤ target := by
    by_cases targetSmall : target < 3
    · simp [readSource, targetSmall] at selected
    · exact Nat.le_of_not_gt targetSmall
  obtain ⟨index, targetExact⟩ :=
    Nat.exists_eq_add_of_le targetAtLeast
  subst target
  rw [Nat.add_comm 3 index] at selected ⊢
  have targetNotSmall : ¬ index + 3 < 3 := by omega
  have shape := Nat.mod_add_div index 6
  rcases occurrence_phase_cases index with
      phase | phase | phase | phase | phase | phase
  · simp [readSource, targetNotSmall, phase] at selected
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at selected
    subst sourceId
    cases quotient : index / 6 with
    | zero =>
        rw [quotient] at shape
        simp [tailSource]
    | succ predecessor =>
        rw [quotient] at shape
        simp [tailSource, Nat.mul_add, Nat.add_assoc]
        rw [← shape]
        simpa [Nat.mul_add, Nat.add_assoc] using
          tailPhaseOne_sourceBefore (6 * predecessor)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at selected
    subst sourceId
    cases quotient : index / 6 with
    | zero =>
        rw [quotient] at shape
        simp [nextSource]
    | succ predecessor =>
        rw [quotient] at shape
        simp [nextSource, Nat.mul_add, Nat.add_sub_assoc]
        rw [← shape]
        simpa [Nat.mul_add, Nat.add_assoc] using
          nextPhaseTwo_sourceBefore (6 * predecessor)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at selected
    subst sourceId
    cases quotient : index / 6 with
    | zero =>
        rw [quotient] at shape
        simp [tailSource]
    | succ predecessor =>
        rw [quotient] at shape
        simp [tailSource, Nat.mul_add, Nat.add_assoc]
        rw [← shape]
        simpa [Nat.mul_add, Nat.add_assoc] using
          tailPhaseThree_sourceBefore (6 * predecessor)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at selected
    subst sourceId
    cases quotient : index / 6 with
    | zero =>
        rw [quotient] at shape
        simp [nextSource]
    | succ predecessor =>
        rw [quotient] at shape
        simp [nextSource, Nat.mul_add, Nat.add_sub_assoc]
        rw [← shape]
        simpa [Nat.mul_add, Nat.add_assoc] using
          nextPhaseFour_sourceBefore (6 * predecessor)
  · rw [phase] at shape
    simp [readSource, targetNotSmall, phase] at selected
    subst sourceId
    cases quotient : index / 6 with
    | zero =>
        rw [quotient] at shape
        simp [tailSource]
    | succ predecessor =>
        rw [quotient] at shape
        simp [tailSource, Nat.mul_add, Nat.add_assoc]
        rw [← shape]
        simpa [Nat.mul_add, Nat.add_assoc] using
          tailPhaseFive_sourceBefore (6 * predecessor)

/-- Every successful RMW reads the immediately preceding site generation. -/
theorem prefixCandidate_rmwReadsImmediatePredecessor
    (length : Nat) :
    ∀ {source rmw : Atom Site Ptr},
      RF (prefixCandidate length) source rmw →
      rmw.IsRMW →
      ImmediateMO (prefixCandidate length) source rmw := by
  intro source rmw readsFrom rmwShape
  have sourceMember := readsFrom.1
  have rmwMember := readsFrom.2.1
  have sourceWrite := readsFrom.2.2.1
  have rmwWrite : rmw.IsWrite :=
    (Atom.isNoninitialWrite_of_isRMW rmwShape).1
  have sameLocation := readsFrom.sameLocation
  have selected : readSource rmw.id = some source.id := by
    rw [← prefixCandidate_sourceId_eq_readSource length rmw rmwMember]
    exact readsFrom.2.2.2.2.2.2
  have sourceBefore : source.id < rmw.id :=
    readSource_source_lt_target selected
  have sourceBound : source.id < atomCount length + 3 := by
    have member : source.id ∈ (prefixCandidate length).atomIds :=
      List.mem_map.mpr ⟨source, sourceMember, rfl⟩
    rw [prefixCandidate_atomIds] at member
    simpa using member
  have rmwBound : rmw.id < atomCount length + 3 := by
    have member : rmw.id ∈ (prefixCandidate length).atomIds :=
      List.mem_map.mpr ⟨rmw, rmwMember, rfl⟩
    rw [prefixCandidate_atomIds] at member
    simpa using member
  have sourceSite : writeSite? source.id = some source.location :=
    (writeSite?_eq_some_iff length sourceMember source.location).2
      ⟨sourceWrite, rfl⟩
  have rmwSite : writeSite? rmw.id = some source.location :=
    (writeSite?_eq_some_iff length rmwMember source.location).2
      ⟨rmwWrite, sameLocation.symm⟩
  have before :
      IdBefore source.id rmw.id
        ((prefixCandidate length).modificationOrder source.location) :=
    (prefixModificationOrder_before_iff length source.location
      sourceBound rmwBound sourceSite rmwSite).2 sourceBefore
  refine ⟨sourceMember, rmwMember, sourceWrite, rmwWrite,
    sameLocation, before, ?_⟩
  intro middle
  rintro ⟨sourceMiddle, middleRmw⟩
  have middleData :=
    (mem_prefixModificationOrder_iff
      length source.location middle).1 sourceMiddle.second_mem
  obtain ⟨middleBound, middleSite⟩ := middleData
  have sourceMiddleLt : source.id < middle :=
    lt_of_idBefore_of_pairwise
      (prefixModificationOrder_pairwise length source.location)
      (List.nodup_range.filter _) sourceMiddle
  have middleRmwLt : middle < rmw.id :=
    lt_of_idBefore_of_pairwise
      (prefixModificationOrder_pairwise length source.location)
      (List.nodup_range.filter _) middleRmw
  have targetLeMiddle : rmw.id ≤ middle :=
    readSource_target_le_of_modificationOrder selected
      ⟨sourceSite, middleSite, sourceMiddleLt⟩
  exact (Nat.not_le_of_gt middleRmwLt) targetLeMiddle

/-- Every finite successful prefix satisfies all structural RC11 clauses. -/
theorem prefixCandidate_wellFormed
    (length : Nat) :
    WellFormed (prefixCandidate length) where
  atomIdsNodup := by
    rw [prefixCandidate_atomIds]
    exact List.nodup_range
  orderSupported := by
    intro atom member
    rw [prefixCandidate_atoms, prefixAtoms] at member
    simp only [staticAtoms, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with static | dynamic
    · rcases static with rfl | rfl | rfl
      all_goals
        simp [headInitializer, tailInitializer,
          dummyNextInitializer, Access.Allows]
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp dynamic
      exact occurrence_orderSupported index
  threadlessIsInitial := by
    intro atom member threadless
    rw [prefixCandidate_atoms, prefixAtoms] at member
    simp only [staticAtoms, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with static | dynamic
    · rcases static with rfl | rfl | rfl
      all_goals
        simp [headInitializer, tailInitializer,
          dummyNextInitializer, Atom.IsInitial,
          Access.IsInitial]
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp dynamic
      rw [occurrence_thread] at threadless
      simp at threadless
  initializerExistsUnique :=
    prefixCandidate_initializerExistsUnique length
  modificationOrderNodup := by
    intro site
    change (prefixModificationOrder length site).Nodup
    exact List.nodup_range.filter _
  modificationOrderExact :=
    prefixCandidate_modificationOrderExact length
  initializerFirst := by
    intro initializer later initializerAt laterMember sameLocation
      laterWrite different
    exact prefixCandidate_initializerFirst length initializerAt
      laterMember sameLocation laterWrite different
  sourceSpec := by
    intro target member
    cases selected : target.readValue with
    | none =>
        simpa [selected] using
          prefixCandidate_sourceSpec length target member
    | some value =>
        simpa [selected] using
          prefixCandidate_sourceSpec length target member
  readSourcesCanonical := prefixCandidate_readSourcesCanonical length
  rmwReadsImmediatePredecessor :=
    prefixCandidate_rmwReadsImmediatePredecessor length

private theorem prefixCandidate_idBefore_lt
    (length : Nat)
    {first second : EventId}
    (before :
      IdBefore first second (prefixCandidate length).atomIds) :
    first < second := by
  rw [prefixCandidate_atomIds] at before
  exact lt_of_idBefore_of_pairwise List.pairwise_lt_range
    List.nodup_range before

/-- Program order follows the canonical dynamic identifier chronology. -/
theorem prefixCandidate_po_id_lt
    (length : Nat)
    {source target : Atom Site Ptr}
    (edge : PO (prefixCandidate length) source target) :
    source.id < target.id := by
  obtain ⟨sourceMember, targetMember, order⟩ := edge
  rcases order with global | sameThread
  · obtain ⟨sourceGlobal, targetNotGlobal⟩ := global
    rw [prefixCandidate_atoms, prefixAtoms] at sourceMember targetMember
    simp only [staticAtoms, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at sourceMember targetMember
    have sourceStatic :
        source = headInitializer 0 ∨
          source = tailInitializer 0 ∨
          source = dummyNextInitializer 0 := by
      rcases sourceMember with static | dynamic
      · exact static
      · obtain ⟨index, _, sourceExact⟩ := List.mem_map.mp dynamic
        have owned : source.thread? = some 0 := by
          rw [← sourceExact]
          exact occurrence_thread index
        exact False.elim (by
          rw [sourceGlobal.2] at owned
          simp at owned)
    have targetDynamic :
        ∃ index,
          index ∈ List.range (atomCount length) ∧
            (occurrence index).toRC11Atom = target := by
      rcases targetMember with static | dynamic
      · rcases static with head | tail | next
        · exfalso
          rw [head] at targetNotGlobal
          exact targetNotGlobal ⟨by
            simp [headInitializer, Atom.IsInitial,
              Access.IsInitial], rfl⟩
        · exfalso
          rw [tail] at targetNotGlobal
          exact targetNotGlobal ⟨by
            simp [tailInitializer, Atom.IsInitial,
              Access.IsInitial], rfl⟩
        · exfalso
          rw [next] at targetNotGlobal
          exact targetNotGlobal ⟨by
            simp [dummyNextInitializer, Atom.IsInitial,
              Access.IsInitial], rfl⟩
      · exact List.mem_map.mp dynamic
    have sourceSmall : source.id < 3 := by
      rcases sourceStatic with head | tail | next
      · rw [head]
        decide
      · rw [tail]
        decide
      · rw [next]
        decide
    obtain ⟨index, _, targetExact⟩ := targetDynamic
    have targetLarge : 3 ≤ target.id := by
      rw [← targetExact]
      change 3 ≤ (occurrence index).id
      rw [occurrence_id]
      exact Nat.le_add_left 3 index
    exact Nat.lt_of_lt_of_le sourceSmall targetLarge
  · obtain ⟨thread, _, _, before⟩ := sameThread
    exact prefixCandidate_idBefore_lt length before

/-- Reads-from edges point from an earlier global generation to the read. -/
theorem prefixCandidate_rf_id_lt
    (length : Nat)
    {source target : Atom Site Ptr}
    (edge : RF (prefixCandidate length) source target) :
    source.id < target.id := by
  have selected : readSource target.id = some source.id := by
    rw [← prefixCandidate_sourceId_eq_readSource
      length target edge.2.1]
    exact edge.2.2.2.2.2.2
  exact readSource_source_lt_target selected

/-- Per-site modification order is strictly increasing in semantic IDs. -/
theorem prefixCandidate_mo_id_lt
    (length : Nat)
    {source target : Atom Site Ptr}
    (edge : MO (prefixCandidate length) source target) :
    source.id < target.id := by
  exact lt_of_idBefore_of_pairwise
    (prefixModificationOrder_pairwise length source.location)
    (List.nodup_range.filter _) edge.2.2.2.2.2

/-- From-read edges also point forward in the concrete source chronology. -/
theorem prefixCandidate_rb_id_lt
    (length : Nat)
    {read later : Atom Site Ptr}
    (edge : RB (prefixCandidate length) read later) :
    read.id < later.id := by
  obtain ⟨source, readsFrom, ordered, different⟩ := edge
  have selected : readSource read.id = some source.id := by
    rw [← prefixCandidate_sourceId_eq_readSource
      length read readsFrom.2.1]
    exact readsFrom.2.2.2.2.2.2
  have sourceSite : writeSite? source.id = some source.location :=
    (writeSite?_eq_some_iff length ordered.1 source.location).2
      ⟨ordered.2.2.1, rfl⟩
  have laterSite : writeSite? later.id = some source.location :=
    (writeSite?_eq_some_iff length ordered.2.1 source.location).2
      ⟨ordered.2.2.2.1, ordered.sameLocation.symm⟩
  have sourceLaterLt : source.id < later.id :=
    prefixCandidate_mo_id_lt length ordered
  have readLeLater : read.id ≤ later.id :=
    readSource_target_le_of_modificationOrder selected
      ⟨sourceSite, laterSite, sourceLaterLt⟩
  have idsDifferent : read.id ≠ later.id := by
    intro sameId
    apply different
    exact (prefixCandidate_wellFormed length).atom_eq_of_id_eq
      readsFrom.2.1 ordered.2.1 sameId
  exact Nat.lt_of_le_of_ne readLeLater idsDifferent

/-- One common numeric rank certifies all finite RC11 consistency clauses. -/
def prefixCandidate_orderWitness
    (length : Nat) :
    OrderWitness (prefixCandidate length) where
  rank := Atom.id
  programOrderIncreases := prefixCandidate_po_id_lt length
  readsFromIncreases := prefixCandidate_rf_id_lt length
  modificationOrderIncreases := prefixCandidate_mo_id_lt length
  readsBeforeIncreases := prefixCandidate_rb_id_lt length

/-- Every finite successful source prefix is an independently valid RC11 model. -/
theorem prefixCandidate_valid
    (length : Nat) :
    Valid (prefixCandidate length) where
  toWellFormed := prefixCandidate_wellFormed length
  noThinAir := (prefixCandidate_orderWitness length).noThinAir
  coherence := (prefixCandidate_orderWitness length).coherent

end InfiniteWitness

end WeakMemory.MSQueue.Source
