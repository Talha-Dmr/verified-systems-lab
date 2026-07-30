import WeakMemory.TreiberC11V1InfiniteMemory

namespace WeakMemory.TreiberC11V1

/-!
# Stable finite modification-order tails

This module extracts the last write of each finite declarative RC11 prefix and
relates it to the coherent global modification order.  The construction uses
the candidate's explicit finite write order; it never identifies modification
order with numerical event-identifier order.

No memory-fairness or liveness premise is used here.  In particular, the
reads-from result below keeps the equality case separate rather than turning
it into a from-read self-edge for an RMW.
-/

namespace RC11

/--
In a duplicate-free nonempty list, every member other than the last member is
strictly before the last member.
-/
private theorem idBefore_getLast
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (nonempty : order ≠ [])
    {eventId : EventId}
    (member : eventId ∈ order)
    (different : eventId ≠ order.getLast nonempty) :
    IdBefore eventId (order.getLast nonempty) order := by
  let leading := order.dropLast
  let last := order.getLast nonempty
  have shape :
      leading ++ [last] = order :=
    List.dropLast_concat_getLast nonempty
  have noDuplicatesAppend :
      (leading ++ [last]).Nodup := by
    rw [shape]
    exact noDuplicates
  have lastFresh :
      last ∉ leading := by
    intro lastMember
    exact
      (List.nodup_append.mp noDuplicatesAppend).2.2
        last lastMember last (by simp) rfl
  have eventInLeading :
      eventId ∈ leading := by
    rw [← shape] at member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with inLeading | isLast
    · exact inLeading
    · exact (different isLast).elim
  refine ⟨member, List.getLast_mem nonempty, ?_⟩
  change order.idxOf eventId < order.idxOf last
  rw [← shape]
  simpa [List.idxOf_append, eventInLeading, lastFresh] using
    List.idxOf_lt_length_of_mem eventInLeading

namespace Valid

/-- Every identifier in the finite write order is represented by a write atom. -/
theorem exists_write_of_id_mem_writeOrder
    {candidate : Candidate α}
    (valid : Valid candidate)
    {eventId : EventId}
    (member : eventId ∈ candidate.writeOrder) :
    ∃ atom,
      atom ∈ candidate.atoms ∧
        atom.id = eventId ∧
        atom.IsWrite := by
  change eventId ∈ 0 :: candidate.modificationOrder at member
  simp only [List.mem_cons] at member
  rcases member with eventIdZero | inTail
  · subst eventId
    exact
      ⟨.initial,
        by simp [Candidate.atoms],
        rfl,
        ⟨.null, rfl⟩⟩
  · obtain ⟨atom, atomMember, atomId, atomWrites, _⟩ :=
      (valid.writeTailExact eventId).mp inTail
    exact ⟨atom, atomMember, atomId, atomWrites⟩

/-- Every finite candidate write atom occurs in its explicit write order. -/
theorem id_mem_writeOrder_of_isWrite
    {candidate : Candidate α}
    (valid : Valid candidate)
    {atom : Atom α}
    (member : atom ∈ candidate.atoms)
    (writes : atom.IsWrite) :
    atom.id ∈ candidate.writeOrder := by
  cases atom with
  | initial =>
      simp [Candidate.writeOrder, Atom.id]
  | occurrence occurrence =>
      have inTail :
          (Atom.occurrence occurrence).id ∈
            candidate.modificationOrder :=
        (valid.writeTailExact
          (Atom.occurrence occurrence).id).mpr
          ⟨.occurrence occurrence, member, rfl, writes,
            by simp [Atom.IsInitial]⟩
      simp [Candidate.writeOrder, inTail]

/-- The initializer and exact duplicate-free write tail form a nodup order. -/
theorem writeOrder_nodup
    {candidate : Candidate α}
    (valid : Valid candidate) :
    candidate.writeOrder.Nodup := by
  rw [Candidate.writeOrder, List.nodup_cons]
  refine ⟨?_, valid.writeTailNodup⟩
  intro initializerInTail
  obtain ⟨atom, atomMember, atomId, _, notInitial⟩ :=
    (valid.writeTailExact 0).mp initializerInTail
  have initialMember :
      (Atom.initial : Atom α) ∈ candidate.atoms := by
    simp [Candidate.atoms]
  have atomIsInitial :
      atom = (.initial : Atom α) :=
    valid.atom_eq_of_id_eq atomMember initialMember
      (by simpa [Atom.id] using atomId)
  subst atom
  simp [Atom.IsInitial] at notInitial

/-- Membership in the write order characterizes writes on the atom carrier. -/
theorem isWrite_of_id_mem_writeOrder
    {candidate : Candidate α}
    (valid : Valid candidate)
    {atom : Atom α}
    (member : atom ∈ candidate.atoms)
    (idMember : atom.id ∈ candidate.writeOrder) :
    atom.IsWrite := by
  obtain ⟨write, writeMember, writeId, writeShape⟩ :=
    valid.exists_write_of_id_mem_writeOrder idMember
  have same :
      atom = write :=
    valid.atom_eq_of_id_eq member writeMember writeId.symm
  simpa [same] using writeShape

/-- Finite modification order relates writes at both endpoints. -/
theorem modificationOrder_writes
    {candidate : Candidate α}
    (valid : Valid candidate)
    {first second : Atom α}
    (ordered : MO candidate first second) :
    first.IsWrite ∧ second.IsWrite := by
  exact
    ⟨valid.isWrite_of_id_mem_writeOrder
        ordered.1 ordered.2.2.1,
      valid.isWrite_of_id_mem_writeOrder
        ordered.2.1 ordered.2.2.2.1⟩

/-- The source endpoint of every finite RF edge is a write. -/
theorem readsFrom_source_isWrite
    {candidate : Candidate α}
    (valid : Valid candidate)
    {source target : Atom α}
    (readsFrom : RF candidate source target) :
    source.IsWrite := by
  cases target with
  | initial =>
      have noSource :=
        valid.sourceSpec
          (Atom.initial : Atom α) readsFrom.2.1
      simp [Atom.readValue] at noSource
      have selected := readsFrom.2.2
      rw [noSource] at selected
      simp at selected
  | occurrence occurrence =>
      obtain ⟨chosen, chosenMember, chosenWrites, chosenId⟩ := by
        simpa [Atom.readValue] using
          valid.sourceSpec
            (Atom.occurrence occurrence) readsFrom.2.1
      have sameId :
          source.id = chosen.id :=
        Option.some.inj
          (readsFrom.2.2.symm.trans chosenId)
      have sameAtom :
          source = chosen :=
        valid.atom_eq_of_id_eq
          readsFrom.1 chosenMember sameId
      subst chosen
      exact ⟨_, chosenWrites⟩

end Valid

/--
A finite write tail dominates every write in the candidate: each write is the
tail itself or is strictly modification-order before it.
-/
structure MaximalWrite (candidate : Candidate α) where
  atom :
    Atom α
  member :
    atom ∈ candidate.atoms
  isWrite :
    atom.IsWrite
  dominates :
    ∀ {write : Atom α},
      write ∈ candidate.atoms →
      write.IsWrite →
        write = atom ∨ MO candidate write atom

private theorem mo_irreflexive
    (candidate : Candidate α)
    (atom : Atom α) :
    ¬ MO candidate atom atom := by
  intro cycle
  exact
    (Nat.lt_irrefl
      (candidate.writeOrder.idxOf atom.id))
      cycle.2.2.2.2

private theorem mo_transitive
    {candidate : Candidate α}
    {first middle last : Atom α}
    (firstMiddle : MO candidate first middle)
    (middleLast : MO candidate middle last) :
    MO candidate first last := by
  refine ⟨firstMiddle.1, middleLast.2.1, ?_⟩
  exact
    ⟨firstMiddle.2.2.1,
      middleLast.2.2.2.1,
      Nat.lt_trans firstMiddle.2.2.2.2
        middleLast.2.2.2.2⟩

namespace MaximalWrite

/-- No finite modification can be strictly after a maximal write. -/
theorem maximal
    {candidate : Candidate α}
    (tail : MaximalWrite candidate)
    (valid : Valid candidate)
    {later : Atom α} :
    ¬ MO candidate tail.atom later := by
  intro afterTail
  have laterWrites :=
    valid.modificationOrder_writes afterTail
  rcases tail.dominates afterTail.2.1 laterWrites.2 with
    same | beforeTail
  · subst later
    exact mo_irreflexive candidate tail.atom afterTail
  · exact
      mo_irreflexive candidate tail.atom
        (mo_transitive afterTail beforeTail)

/--
Every finite RF source is the maximal write itself or is modification-order
before it.  The equality branch is intentionally not represented as `RB`.
-/
theorem readsFromSource_eq_or_before
    {candidate : Candidate α}
    (tail : MaximalWrite candidate)
    (valid : Valid candidate)
    {source target : Atom α}
    (readsFrom : RF candidate source target) :
    source = tail.atom ∨
      MO candidate source tail.atom :=
  tail.dominates readsFrom.1
    (valid.readsFrom_source_isWrite readsFrom)

end MaximalWrite

namespace Valid

/-- Every valid finite candidate has a maximal write, including the initializer. -/
theorem exists_maximalWrite
    {candidate : Candidate α}
    (valid : Valid candidate) :
    Nonempty (MaximalWrite candidate) := by
  have orderNonempty :
      candidate.writeOrder ≠ [] := by
    simp [Candidate.writeOrder]
  have tailIdMember :
      candidate.writeOrder.getLast orderNonempty ∈
        candidate.writeOrder :=
    List.getLast_mem orderNonempty
  obtain ⟨tail, tailMember, tailId, tailWrites⟩ :=
    valid.exists_write_of_id_mem_writeOrder tailIdMember
  refine
    ⟨{
      atom := tail
      member := tailMember
      isWrite := tailWrites
      dominates := ?_
    }⟩
  intro write writeMember writeWrites
  by_cases sameId : write.id = tail.id
  · exact Or.inl
      (valid.atom_eq_of_id_eq
        writeMember tailMember sameId)
  · apply Or.inr
    refine ⟨writeMember, tailMember, ?_⟩
    rw [tailId]
    apply idBefore_getLast
      valid.writeOrder_nodup orderNonempty
      (valid.id_mem_writeOrder_of_isWrite
        writeMember writeWrites)
    intro writeIsLast
    exact sameId (writeIsLast.trans tailId.symm)

end Valid

end RC11

namespace DeclarativeExecution

/-- The chosen maximal write of one finite declarative execution. -/
noncomputable def maximalWrite
    (execution : DeclarativeExecution α) :
    RC11.MaximalWrite execution.candidate :=
  Classical.choice execution.rc11.exists_maximalWrite

/-- With no dynamic writes, the chosen maximal write is the initializer. -/
theorem maximalWrite_eq_initial_of_no_dynamicWrites
    (execution : DeclarativeExecution α)
    (noDynamicWrites :
      execution.candidate.modificationOrder = []) :
    execution.maximalWrite.atom =
      (.initial : RC11.Atom α) := by
  have tailIdMember :=
    execution.rc11.id_mem_writeOrder_of_isWrite
      execution.maximalWrite.member
      execution.maximalWrite.isWrite
  have tailIdZero :
      execution.maximalWrite.atom.id = 0 := by
    simpa [RC11.Candidate.writeOrder, noDynamicWrites] using
      tailIdMember
  have initialMember :
      (.initial : RC11.Atom α) ∈
        execution.candidate.atoms := by
    simp [RC11.Candidate.atoms]
  exact
    execution.rc11.atom_eq_of_id_eq
      execution.maximalWrite.member initialMember
      (by simpa [RC11.Atom.id] using tailIdZero)

end DeclarativeExecution

namespace InfiniteRC11Execution

/-- The chosen maximal finite write at one source-prefix boundary. -/
noncomputable def prefixTail
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    RC11.MaximalWrite
      (execution.declarativePrefix length).candidate :=
  (execution.declarativePrefix length).maximalWrite

/--
Every write in a finite prefix is the chosen tail or globally
modification-order before it.
-/
theorem prefixWrite_eq_tail_or_before
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    {write : RC11.Atom α}
    (writeMember :
      write ∈ (execution.declarativePrefix length).candidate.atoms)
    (writeShape : write.IsWrite) :
    write = (execution.prefixTail length).atom ∨
      execution.modificationOrder
        write.id (execution.prefixTail length).atom.id := by
  rcases (execution.prefixTail length).dominates
      writeMember writeShape with same | before
  · exact Or.inl same
  · exact Or.inr
      ((execution.declarativePrefix_modificationOrder
        length write (execution.prefixTail length).atom
        writeMember (execution.prefixTail length).member).mp
          before)

/-- The finite tail remains maximal under the exact global MO restriction. -/
theorem prefixTail_global_maximal
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    {write : RC11.Atom α}
    (writeMember :
      write ∈ (execution.declarativePrefix length).candidate.atoms) :
    ¬ execution.modificationOrder
        (execution.prefixTail length).atom.id write.id := by
  intro globallyAfter
  have finiteAfter :
      RC11.MO
        (execution.declarativePrefix length).candidate
        (execution.prefixTail length).atom write :=
    (execution.declarativePrefix_modificationOrder
      length (execution.prefixTail length).atom write
      (execution.prefixTail length).member writeMember).mpr
        globallyAfter
  exact
    (execution.prefixTail length).maximal
      (execution.declarativePrefix length).rc11
      finiteAfter

/--
Every RF source in a finite prefix is the chosen tail or globally
modification-order before it.
-/
theorem prefixReadSource_eq_tail_or_before
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    {source target : RC11.Atom α}
    (readsFrom :
      RC11.RF
        (execution.declarativePrefix length).candidate
        source target) :
    source = (execution.prefixTail length).atom ∨
      execution.modificationOrder
        source.id (execution.prefixTail length).atom.id := by
  rcases (execution.prefixTail length).readsFromSource_eq_or_before
      (execution.declarativePrefix length).rc11
      readsFrom with same | before
  · exact Or.inl same
  · exact Or.inr
      ((execution.declarativePrefix_modificationOrder
        length source (execution.prefixTail length).atom
        readsFrom.1 (execution.prefixTail length).member).mp
          before)

private theorem atomic_mem_trace_of_mem_atoms
    {candidate : RC11.Candidate α}
    {occurrence : AtomicOccurrence α}
    (member :
      RC11.Atom.occurrence occurrence ∈ candidate.atoms) :
    TraceEvent.atomic occurrence ∈ candidate.trace := by
  simp only [RC11.Candidate.atoms, List.mem_cons] at member
  rcases member with impossible | filtered
  · cases impossible
  · change
      RC11.Atom.occurrence occurrence ∈
        candidate.trace.filterMap RC11.atomOfTraceEvent? at filtered
    obtain ⟨event, eventMember, projects⟩ :=
      List.mem_filterMap.mp filtered
    cases event <;>
      simp [RC11.atomOfTraceEvent?] at projects
    rename_i sourceOccurrence
    cases projects
    exact eventMember

/-- A dynamic write atom is exactly a successful source CAS occurrence. -/
private theorem successfulCAS_of_occurrence_isWrite
    (occurrence : AtomicOccurrence α)
    (writes :
      (RC11.Atom.occurrence occurrence).IsWrite) :
    (TraceEvent.atomic occurrence).IsSuccessfulCAS := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | pushLoad =>
      simp [RC11.Atom.IsWrite, RC11.Atom.writtenValue,
        AtomicAction.writtenValue] at writes
  | pushCas thread operation node value expected observed succeeded =>
      cases succeeded <;>
        simp [RC11.Atom.IsWrite, RC11.Atom.writtenValue,
          AtomicAction.writtenValue,
          TraceEvent.IsSuccessfulCAS] at writes ⊢
  | popLoad =>
      simp [RC11.Atom.IsWrite, RC11.Atom.writtenValue,
        AtomicAction.writtenValue] at writes
  | popCas thread operation expected value next observed succeeded =>
      cases succeeded <;>
        simp [RC11.Atom.IsWrite, RC11.Atom.writtenValue,
          AtomicAction.writtenValue,
          TraceEvent.IsSuccessfulCAS] at writes ⊢
  | isEmptyLoad =>
      simp [RC11.Atom.IsWrite, RC11.Atom.writtenValue,
        AtomicAction.writtenValue] at writes

/--
If no successful CAS occurs after `start`, every write in a later prefix was
already present at the `start` boundary.
-/
theorem write_mem_startPrefix_of_no_success
    (execution : InfiniteRC11Execution α threadCount)
    (start length : Nat)
    (_later : start ≤ length)
    (noSuccess :
      ∀ time,
        start ≤ time →
          ¬ (execution.source.event time).IsSuccessfulCAS)
    {write : RC11.Atom α}
    (writeMember :
      write ∈ (execution.declarativePrefix length).candidate.atoms)
    (writeShape : write.IsWrite) :
    write ∈ (execution.declarativePrefix start).candidate.atoms := by
  cases write with
  | initial =>
      simp [RC11.Candidate.atoms]
  | occurrence occurrence =>
      have eventMember :
          TraceEvent.atomic occurrence ∈
            execution.source.tracePrefix length := by
        rw [← execution.declarativePrefix_trace length]
        exact atomic_mem_trace_of_mem_atoms writeMember
      unfold InfiniteExecution.tracePrefix at eventMember
      obtain ⟨time, _, event⟩ :=
        List.mem_map.mp eventMember
      have successful :
          (execution.source.event time).IsSuccessfulCAS := by
        rw [event]
        exact successfulCAS_of_occurrence_isWrite
          occurrence writeShape
      have beforeStart : time < start := by
        by_cases before : time < start
        · exact before
        · exact False.elim
            ((noSuccess time (Nat.le_of_not_gt before))
              successful)
      exact
        execution.occurrence_mem_declarativePrefix_atoms_of_lt
          time start beforeStart occurrence event

/--
With no later successful CAS, the start-prefix tail dominates every write in
every later finite prefix.
-/
theorem laterWrite_eq_startTail_or_before
    (execution : InfiniteRC11Execution α threadCount)
    (start length : Nat)
    (later : start ≤ length)
    (noSuccess :
      ∀ time,
        start ≤ time →
          ¬ (execution.source.event time).IsSuccessfulCAS)
    {write : RC11.Atom α}
    (writeMember :
      write ∈ (execution.declarativePrefix length).candidate.atoms)
    (writeShape : write.IsWrite) :
    write = (execution.prefixTail start).atom ∨
      execution.modificationOrder
        write.id (execution.prefixTail start).atom.id :=
  execution.prefixWrite_eq_tail_or_before start
    (execution.write_mem_startPrefix_of_no_success
      start length later noSuccess writeMember writeShape)
    writeShape

/--
With no successful CAS after `start`, the RF source of every later atomic
event is the start-prefix tail or is globally modification-order before it.
-/
theorem laterReadSource_eq_startTail_or_before
    (execution : InfiniteRC11Execution α threadCount)
    (start time : Nat)
    (afterStart : start ≤ time)
    (noSuccess :
      ∀ laterTime,
        start ≤ laterTime →
          ¬ (execution.source.event laterTime).IsSuccessfulCAS)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    ∃ source : RC11.Atom α,
      source ∈
          (execution.declarativePrefix start).candidate.atoms ∧
        source.IsWrite ∧
        execution.readSource occurrence.id = some source.id ∧
        (source = (execution.prefixTail start).atom ∨
          execution.modificationOrder
            source.id (execution.prefixTail start).atom.id) := by
  let finiteExecution :=
    execution.declarativePrefix (time + 1)
  have targetMember :
      RC11.Atom.occurrence occurrence ∈
        finiteExecution.candidate.atoms :=
    execution.occurrence_mem_declarativePrefix_atoms
      time occurrence event
  obtain ⟨source, sourceMember, sourceValue, chosenSource⟩ := by
    simpa [finiteExecution, RC11.Atom.readValue] using
      finiteExecution.rc11.sourceSpec
        (RC11.Atom.occurrence occurrence) targetMember
  have sourceWrites : source.IsWrite :=
    ⟨_, sourceValue⟩
  have sourceAtStart :
      source ∈
        (execution.declarativePrefix start).candidate.atoms :=
    execution.write_mem_startPrefix_of_no_success
      start (time + 1) (by omega) noSuccess
      sourceMember sourceWrites
  have globalSource :
      execution.readSource occurrence.id = some source.id := by
    have restriction :=
      execution.declarativePrefix_readSource
        (time + 1)
        (RC11.Atom.occurrence occurrence)
        targetMember
    exact
      (by
        simpa [finiteExecution, RC11.Atom.id] using
          restriction.symm.trans chosenSource)
  exact
    ⟨source, sourceAtStart, sourceWrites, globalSource,
      execution.prefixWrite_eq_tail_or_before
        start sourceAtStart sourceWrites⟩

/--
The chosen prefix tail has a real position in the infinite source execution.
The initializer uses position zero; a dynamic tail uses the position
immediately after its source transition.
-/
theorem prefixTail_hasPosition
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    ∃ position,
      position ≤ length ∧
        execution.graphEventId? position =
          some (execution.prefixTail length).atom.id := by
  cases tailShape : (execution.prefixTail length).atom with
  | initial =>
      refine ⟨0, Nat.zero_le length, ?_⟩
      simp [RC11.Atom.id]
  | occurrence occurrence =>
      have atomMember :
          RC11.Atom.occurrence occurrence ∈
            (execution.declarativePrefix length).candidate.atoms := by
        simpa [tailShape] using
          (execution.prefixTail length).member
      have eventMember :
          TraceEvent.atomic occurrence ∈
            execution.source.tracePrefix length := by
        rw [← execution.declarativePrefix_trace length]
        exact atomic_mem_trace_of_mem_atoms atomMember
      unfold InfiniteExecution.tracePrefix at eventMember
      obtain ⟨time, timeMember, event⟩ :=
        List.mem_map.mp eventMember
      have beforeLength : time < length := by
        simpa using timeMember
      refine ⟨time + 1, by omega, ?_⟩
      simpa [tailShape, RC11.Atom.id] using
        execution.graphEventId?_atomic
          time occurrence event

/--
Prefix-finite `fr` eventually makes every selected later atomic event observe
the stable tail chosen at `start`, provided no successful CAS occurs on that
suffix.

The selected events may be all atomic events, all CAS attempts, or any other
atomic subsequence.  Equality with the tail is handled directly; only a
strictly earlier source creates the from-read edge used by the visibility
assumption.
-/
theorem eventually_selected_observes_prefixTail_of_fromReadFair
    (execution : InfiniteRC11Execution α threadCount)
    (fromReadFair : execution.FromReadFair)
    (start : Nat)
    (noSuccess :
      ∀ time,
        start ≤ time →
          ¬ (execution.source.event time).IsSuccessfulCAS)
    (selected : Nat → Prop)
    (selectedAfterStart :
      ∀ time,
        selected time →
          start ≤ time)
    (selectedAtomic :
      ∀ time,
        selected time →
          ∃ occurrence : AtomicOccurrence α,
            execution.source.event time =
              .atomic occurrence) :
    Liveness.EventuallyAlways (fun time =>
      selected time →
        execution.observedWrite time =
          (execution.prefixTail start).atom.id) := by
  obtain ⟨stablePosition, stableBeforeStart, stableAt⟩ :=
    execution.prefixTail_hasPosition start
  apply
    execution.eventually_observes_stable_write_of_fromReadFair
      fromReadFair selected selectedAtomic
      stablePosition
      (execution.prefixTail start).atom.id
      stableAt
      (fun time isSelected => by
        have afterStart :=
          selectedAfterStart time isSelected
        omega)
  intro time isSelected stale
  obtain ⟨occurrence, event⟩ :=
    selectedAtomic time isSelected
  obtain ⟨source, _, _, globalSource, sourceBound⟩ :=
    execution.laterReadSource_eq_startTail_or_before
      start time
      (selectedAfterStart time isSelected)
      noSuccess occurrence event
  have observedSource :
      execution.readSource occurrence.id =
        some (execution.observedWrite time) :=
    execution.readSource_eq_observedWrite_of_atomic
      time occurrence event
  have observedIsSource :
      execution.observedWrite time = source.id :=
    Option.some.inj
      (observedSource.symm.trans globalSource)
  rcases sourceBound with sourceIsTail | beforeTail
  · exact False.elim
      (stale
        (observedIsSource.trans
          (congrArg RC11.Atom.id sourceIsTail)))
  · rw [observedIsSource]
    exact beforeTail

/--
Conventional paired memory fairness supplies the `fr`-only stable-tail
visibility premise.
-/
theorem eventually_selected_observes_prefixTail
    (execution : InfiniteRC11Execution α threadCount)
    (memoryFair : execution.MemoryFair)
    (start : Nat)
    (noSuccess :
      ∀ time,
        start ≤ time →
          ¬ (execution.source.event time).IsSuccessfulCAS)
    (selected : Nat → Prop)
    (selectedAfterStart :
      ∀ time,
        selected time →
          start ≤ time)
    (selectedAtomic :
      ∀ time,
        selected time →
          ∃ occurrence : AtomicOccurrence α,
            execution.source.event time =
              .atomic occurrence) :
    Liveness.EventuallyAlways (fun time =>
      selected time →
        execution.observedWrite time =
          (execution.prefixTail start).atom.id) :=
  execution.eventually_selected_observes_prefixTail_of_fromReadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    start noSuccess selected selectedAfterStart selectedAtomic

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
