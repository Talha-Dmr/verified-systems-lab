import WeakMemory.MSQueueInfiniteMemory

namespace WeakMemory

/-!
# Stable selected-site visibility for the infinite queue

This module is independent of queue retry control.  It chooses the maximal
write at one represented site of a finite prefix and proves that, once that
site receives no later modification, prefix-finite `fr` makes selected later
reads observe exactly that write.
-/

namespace MultiLocationRC11

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
  have shape : leading ++ [last] = order :=
    List.dropLast_concat_getLast nonempty
  have noDuplicatesAppend : (leading ++ [last]).Nodup := by
    rw [shape]
    exact noDuplicates
  have lastFresh : last ∉ leading := by
    intro lastMember
    exact
      (List.nodup_append.mp noDuplicatesAppend).2.2
        last lastMember last (by simp) rfl
  have eventInLeading : eventId ∈ leading := by
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

/-- A finite write that dominates all writes at one represented site. -/
structure MaximalWriteAt
    (candidate : Candidate Location Value)
    (site : Location) where
  atom : Atom Location Value
  member : atom ∈ candidate.atoms
  location : atom.location = site
  isWrite : atom.IsWrite
  dominates :
    ∀ {write : Atom Location Value},
      write ∈ candidate.atoms →
      write.location = site →
      write.IsWrite →
        write = atom ∨ MO candidate write atom

private theorem isWrite_of_isInitial
    {atom : Atom Location Value}
    (initial : atom.IsInitial) :
    atom.IsWrite := by
  change atom.access.IsInitial at initial
  change atom.access.IsWrite
  generalize atom.access = access at initial ⊢
  cases access <;>
    simp_all [Access.IsInitial, Access.IsWrite]

namespace Valid

/-- Every represented site of a valid finite candidate has a maximal write. -/
theorem exists_maximalWriteAt
    {candidate : Candidate Location Value}
    (valid : Valid candidate)
    (site : Location)
    (represented : candidate.Represents site) :
    Nonempty (MaximalWriteAt candidate site) := by
  obtain ⟨initializer, initializerAt, _unique⟩ :=
    valid.initializerExistsUnique site represented
  have initializerWrite : initializer.IsWrite :=
    isWrite_of_isInitial initializerAt.2.2
  have initializerIdMember :
      initializer.id ∈ candidate.modificationOrder site :=
    (valid.modificationOrderExact site initializer.id).2
      ⟨initializer, initializerAt.1, initializerAt.2.1,
        rfl, initializerWrite⟩
  have orderNonempty : candidate.modificationOrder site ≠ [] := by
    intro empty
    simp [empty] at initializerIdMember
  have tailIdMember :
      (candidate.modificationOrder site).getLast orderNonempty ∈
        candidate.modificationOrder site :=
    List.getLast_mem orderNonempty
  obtain ⟨tail, tailMember, tailLocation, tailId, tailWrite⟩ :=
    (valid.modificationOrderExact site
      ((candidate.modificationOrder site).getLast orderNonempty)).1
      tailIdMember
  refine ⟨{
    atom := tail
    member := tailMember
    location := tailLocation
    isWrite := tailWrite
    dominates := ?_
  }⟩
  intro write writeMember writeLocation writeShape
  by_cases sameId : write.id = tail.id
  · exact Or.inl
      (valid.atom_eq_of_id_eq writeMember tailMember sameId)
  · apply Or.inr
    have writeIdMember :
        write.id ∈ candidate.modificationOrder site :=
      (valid.modificationOrderExact site write.id).2
        ⟨write, writeMember, writeLocation, rfl, writeShape⟩
    have beforeTail :
        IdBefore write.id tail.id
          (candidate.modificationOrder site) := by
      rw [tailId]
      exact idBefore_getLast
        (valid.modificationOrderNodup site)
        orderNonempty writeIdMember
        (fun equality => sameId (equality.trans tailId.symm))
    refine ⟨writeMember, tailMember, writeShape, tailWrite,
      writeLocation.trans tailLocation.symm, ?_⟩
    simpa [writeLocation] using beforeTail

end Valid

namespace MaximalWriteAt

/-- A maximal selected-site write has no later finite MO successor. -/
theorem maximal
    {candidate : Candidate Location Value}
    {site : Location}
    (tail : MaximalWriteAt candidate site)
    (_valid : Valid candidate)
    {later : Atom Location Value}
    (laterLocation : later.location = site) :
    ¬ MO candidate tail.atom later := by
  intro afterTail
  rcases tail.dominates afterTail.2.1 laterLocation afterTail.2.2.2.1 with
    same | beforeTail
  · subst later
    exact MO.irreflexive tail.atom afterTail
  · exact MO.irreflexive tail.atom (MO.transitive afterTail beforeTail)

end MaximalWriteAt

end MultiLocationRC11

namespace MSQueue.Source

namespace InfiniteRC11Execution

/-- The chosen maximal write at one represented site of a finite prefix. -/
noncomputable def prefixMaximalWriteAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (site : Site)
    (represented :
      (execution.supportedPrefix length).candidate.Represents site) :
    MultiLocationRC11.MaximalWriteAt
      (execution.supportedPrefix length).candidate site :=
  Classical.choice
    ((execution.supportedPrefix length).valid.exists_maximalWriteAt
      site represented)

/-- A prefix-selected maximal write globally dominates all same-site writes. -/
theorem prefixWrite_eq_maximal_or_before
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (site : Site)
    (represented :
      (execution.supportedPrefix length).candidate.Represents site)
    {write : MultiLocationRC11.Atom Site Ptr}
    (writeMember :
      write ∈ (execution.supportedPrefix length).candidate.atoms)
    (writeLocation : write.location = site)
    (writeShape : write.IsWrite) :
    write = (execution.prefixMaximalWriteAt length site represented).atom ∨
      execution.modificationOrder site write.id
        (execution.prefixMaximalWriteAt length site represented).atom.id := by
  rcases (execution.prefixMaximalWriteAt length site represented).dominates
      writeMember writeLocation writeShape with same | before
  · exact Or.inl same
  · apply Or.inr
    have finiteBeforeCandidate :
        MultiLocationRC11.IdBefore write.id
          (execution.prefixMaximalWriteAt length site represented).atom.id
          ((execution.supportedPrefix length).candidate.modificationOrder site) := by
      simpa [writeLocation] using before.2.2.2.2.2
    have finiteBefore :
        MultiLocationRC11.IdBefore write.id
          (execution.prefixMaximalWriteAt length site represented).atom.id
          ((execution.supportedPrefix length).modificationOrder site) := by
      simpa [SupportedExecution.candidate, projectCandidate] using
        finiteBeforeCandidate
    exact
      ((execution.prefixModificationOrder length site write
        (execution.prefixMaximalWriteAt length site represented).atom
        writeMember
        (execution.prefixMaximalWriteAt length site represented).member).mp
          finiteBefore)

/-- A dynamic write event modifies its exact projected logical site. -/
private theorem modifiedAt_of_atomic_write
    (occurrence : AtomicOccurrence Value)
    (write : occurrence.toRC11Atom.IsWrite) :
    (TraceEvent.atomic occurrence).ModifiedAt occurrence.action.site := by
  exact ⟨rfl, write⟩

/-!
If a selected site is modification-free from `start`, every same-site write
appearing in a later prefix was already represented at the `start` boundary.
-/
theorem write_mem_startPrefix_of_noModification
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site)
    (start length : Nat)
    (_later : start ≤ length)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    {write : MultiLocationRC11.Atom Site Ptr}
    (writeMember :
      write ∈ (execution.supportedPrefix length).candidate.atoms)
    (writeLocation : write.location = site)
    (writeShape : write.IsWrite) :
    write ∈ (execution.supportedPrefix start).candidate.atoms := by
  rw [(execution.supportedPrefix length).atoms_exact,
    projectedAtoms] at writeMember
  rw [(execution.supportedPrefix start).atoms_exact,
    projectedAtoms]
  rcases List.mem_append.mp writeMember with staticMember | dynamicMember
  · exact List.mem_append.mpr (Or.inl staticMember)
  · obtain ⟨occurrence, occurrenceMember, writeEq⟩ :=
      List.mem_map.mp dynamicMember
    subst write
    obtain ⟨event, eventMember, selected⟩ :=
      List.mem_filterMap.mp occurrenceMember
    cases event with
    | atomic emitted =>
        simp [TraceEvent.atomicOccurrence?] at selected
        subst emitted
        unfold InfiniteExecution.tracePrefix at eventMember
        obtain ⟨time, timeMember, eventEq⟩ := List.mem_map.mp eventMember
        have beforeStart : time < start := by
          by_cases before : time < start
          · exact before
          · have afterStart : start ≤ time := Nat.le_of_not_gt before
            have modified :
                (execution.source.event time).ModifiedAt site := by
              rw [eventEq]
              have atOwnSite := modifiedAt_of_atomic_write occurrence writeShape
              simpa [AtomicOccurrence.toRC11Atom] using
                (show occurrence.action.site = site from writeLocation)
                  ▸ atOwnSite
            exact False.elim (stable time afterStart modified)
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_map.mpr
        refine ⟨occurrence, ?_, rfl⟩
        apply List.mem_filterMap.mpr
        refine ⟨TraceEvent.atomic occurrence, ?_, rfl⟩
        unfold InfiniteExecution.tracePrefix
        apply List.mem_map.mpr
        exact ⟨time, by simpa using beforeStart, eventEq⟩
    | invokeEnqueue | initializePayload | invokeDequeue |
        readPayload | respondEnqueue | respondDequeue =>
        simp [TraceEvent.atomicOccurrence?] at selected

/-- The fixed start-prefix maximal write dominates every later RF source. -/
theorem laterReadSource_eq_startMaximal_or_before
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site)
    (start time : Nat)
    (afterStart : start ≤ time)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence)
    (atSite : occurrence.action.site = site)
    (read : occurrence.toRC11Atom.IsRead) :
    ∃ source : MultiLocationRC11.Atom Site Ptr,
      source ∈ (execution.supportedPrefix start).candidate.atoms ∧
        source.location = site ∧
        source.IsWrite ∧
        execution.readSource occurrence.id = some source.id ∧
        (source =
            (execution.prefixMaximalWriteAt start site represented).atom ∨
          execution.modificationOrder site source.id
            (execution.prefixMaximalWriteAt start site represented).atom.id) := by
  let finiteExecution := execution.supportedPrefix (time + 1)
  have targetMember : occurrence.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms time occurrence event
  obtain ⟨source, readsFrom⟩ :=
    finiteExecution.valid.everyRead_hasSource targetMember read
  have sourceLocation : source.location = site := by
    exact readsFrom.sameLocation.trans (by
      simpa [AtomicOccurrence.toRC11Atom] using atSite)
  have sourceAtStart :
      source ∈ (execution.supportedPrefix start).candidate.atoms :=
    execution.write_mem_startPrefix_of_noModification
      site start (time + 1) (by omega) stable
      readsFrom.1 sourceLocation readsFrom.2.2.1
  have globalSource :
      execution.readSource occurrence.id = some source.id := by
    have restrictionRaw :=
      execution.prefixReadSource (time + 1)
        occurrence.toRC11Atom targetMember
    have restriction :
        finiteExecution.candidate.sourceId occurrence.toRC11Atom.id =
          execution.readSource occurrence.toRC11Atom.id := by
      exact restrictionRaw
    exact restriction.symm.trans readsFrom.2.2.2.2.2.2
  exact ⟨source, sourceAtStart, sourceLocation, readsFrom.2.2.1,
    globalSource,
    execution.prefixWrite_eq_maximal_or_before
      start site represented sourceAtStart sourceLocation readsFrom.2.2.1⟩

/-- The selected maximal write has a concrete static or dynamic graph position. -/
theorem prefixMaximalWriteAt_hasPosition
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (site : Site)
    (represented :
      (execution.supportedPrefix length).candidate.Represents site) :
    ∃ position,
      position ≤ length + 2 ∧
        execution.graphEventId? position =
          some (execution.prefixMaximalWriteAt length site represented).atom.id := by
  have member :=
    (execution.prefixMaximalWriteAt length site represented).member
  rw [(execution.supportedPrefix length).atoms_exact, projectedAtoms] at member
  rcases List.mem_append.mp member with staticMember | dynamicMember
  · simp [staticAtoms] at staticMember
    rcases staticMember with head | tail | next
    · refine ⟨0, by omega, ?_⟩
      rw [head]
      rfl
    · refine ⟨1, by omega, ?_⟩
      rw [tail]
      rfl
    · refine ⟨2, by omega, ?_⟩
      rw [next]
      rfl
  · obtain ⟨occurrence, occurrenceMember, atomEq⟩ :=
      List.mem_map.mp dynamicMember
    obtain ⟨event, eventMember, selected⟩ :=
      List.mem_filterMap.mp occurrenceMember
    cases event with
    | atomic emitted =>
        simp [TraceEvent.atomicOccurrence?] at selected
        subst emitted
        unfold InfiniteExecution.tracePrefix at eventMember
        obtain ⟨time, timeMember, eventEq⟩ := List.mem_map.mp eventMember
        refine ⟨time + 3, by have := (show time < length by simpa using timeMember); omega, ?_⟩
        rw [← atomEq]
        exact execution.graphEventId?_atomic time occurrence eventEq
    | invokeEnqueue | initializePayload | invokeDequeue |
        readPayload | respondEnqueue | respondDequeue =>
        simp [TraceEvent.atomicOccurrence?] at selected

/-!
Selected-site prefix-finite `fr` exposes the stable maximal write to all
selected later atomic reads at that exact site.
-/
theorem eventually_selected_observes_prefixMaximal_of_fromReadFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (fromReadFair : execution.FromReadFair)
    (site : Site)
    (start : Nat)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    (selected : Nat → Prop)
    (selectedAfterStart :
      ∀ time, selected time → start ≤ time)
    (selectedAtomicAtSite :
      ∀ time,
        selected time →
        ∃ occurrence : AtomicOccurrence Value,
          execution.source.event time = .atomic occurrence ∧
            occurrence.action.site = site ∧
            occurrence.toRC11Atom.IsRead) :
    Liveness.EventuallyAlways (fun time =>
      selected time →
        execution.observedWrite time =
          (execution.prefixMaximalWriteAt start site represented).atom.id) := by
  obtain ⟨stablePosition, stableBeforeStart, stableAt⟩ :=
    execution.prefixMaximalWriteAt_hasPosition start site represented
  apply execution.eventually_observes_stable_write_of_fromReadFair
      fromReadFair site selected
      (fun time isSelected => by
        obtain ⟨occurrence, event, _atSite, read⟩ :=
          selectedAtomicAtSite time isSelected
        exact ⟨occurrence, event, read⟩)
      stablePosition
      (execution.prefixMaximalWriteAt start site represented).atom.id
      stableAt
      (fun time isSelected => by
        have afterStart := selectedAfterStart time isSelected
        omega)
  intro time isSelected stale
  obtain ⟨occurrence, event, atSite, read⟩ :=
    selectedAtomicAtSite time isSelected
  obtain ⟨source, _sourceMember, _sourceLocation, _sourceWrite,
      globalSource, sourceBound⟩ :=
    execution.laterReadSource_eq_startMaximal_or_before
      site start time (selectedAfterStart time isSelected)
      represented stable occurrence event atSite read
  have observedSource :
      execution.readSource occurrence.id =
        some (execution.observedWrite time) :=
    execution.readSource_eq_observedWrite_of_atomic
      time occurrence event read
  have observedIsSource : execution.observedWrite time = source.id :=
    Option.some.inj (observedSource.symm.trans globalSource)
  rcases sourceBound with sourceIsMaximal | beforeMaximal
  · exact False.elim
      (stale
        (observedIsSource.trans
          (congrArg MultiLocationRC11.Atom.id sourceIsMaximal)))
  · rw [observedIsSource]
    exact beforeMaximal

/-- Conventional per-site memory fairness supplies stable-site visibility. -/
theorem eventually_selected_observes_prefixMaximal
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (memoryFair : execution.MemoryFair)
    (site : Site)
    (start : Nat)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    (selected : Nat → Prop)
    (selectedAfterStart :
      ∀ time, selected time → start ≤ time)
    (selectedAtomicAtSite :
      ∀ time,
        selected time →
        ∃ occurrence : AtomicOccurrence Value,
          execution.source.event time = .atomic occurrence ∧
            occurrence.action.site = site ∧
            occurrence.toRC11Atom.IsRead) :
    Liveness.EventuallyAlways (fun time =>
      selected time →
        execution.observedWrite time =
          (execution.prefixMaximalWriteAt start site represented).atom.id) :=
  execution.eventually_selected_observes_prefixMaximal_of_fromReadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    site start represented stable selected selectedAfterStart selectedAtomicAtSite

end InfiniteRC11Execution

end MSQueue.Source

end WeakMemory
