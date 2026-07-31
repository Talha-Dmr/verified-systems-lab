import WeakMemory.MSQueueInfiniteWitnessPrefix
import WeakMemory.MSQueueInfiniteSafety

namespace WeakMemory.MSQueue.Source

open MultiLocationRC11

namespace InfiniteWitness

/-!
# Coherent infinite RC11 packaging for the successful witness

This module packages the independently checked finite candidates into one
global execution and supplies the structural prefix schedules consumed by the
queue safety and progress theorems.
-/

/-- The source projection and the explicit dense candidate are extensionally equal. -/
theorem projectCandidate_eq_prefixCandidate (length : Nat) :
    projectCandidate 0 (source.tracePrefix length)
        (prefixReadSources length) (prefixModificationOrder length) =
      prefixCandidate length := by
  have atoms :
      projectedAtoms 0 (source.tracePrefix length) =
        prefixAtoms length :=
    (prefixCandidate_atoms_projected length).symm
  unfold projectCandidate prefixCandidate
  rw [atoms]

/-- Every source prefix is a fully checked source-backed RC11 execution. -/
def finitePrefix (length : Nat) :
    SupportedExecution 0 (source.tracePrefix length) where
  sourceWellFormed := tracePrefix_sourceWellFormed length
  readSources := prefixReadSources length
  modificationOrder := prefixModificationOrder length
  valid := by
    rw [projectCandidate_eq_prefixCandidate]
    exact prefixCandidate_valid length

private theorem prefixAtom_id_bound
    (length : Nat)
    {atom : Atom Site Ptr}
    (member : atom ∈ (prefixCandidate length).atoms) :
    atom.id < atomCount length + 3 := by
  have idMember : atom.id ∈ (prefixCandidate length).atomIds :=
    List.mem_map.mpr ⟨atom, member, rfl⟩
  rw [prefixCandidate_atomIds] at idMember
  simpa using idMember

/-- The coherent infinite RC11 execution shared by every finite restriction. -/
def execution : InfiniteRC11Execution Unit 1 0 where
  source := source
  readSource := readSource
  modificationOrder := modificationOrder
  modificationOrderIrreflexive := by
    intro site event
    rintro ⟨_, _, before⟩
    exact Nat.lt_irrefl event before
  modificationOrderTransitive := by
    intro site first middle last firstMiddle middleLast
    exact ⟨firstMiddle.1, middleLast.2.1,
      Nat.lt_trans firstMiddle.2.2 middleLast.2.2⟩
  finitePrefix := finitePrefix
  prefixReadSource := by
    intro length atom member
    have candidateMember : atom ∈ (prefixCandidate length).atoms := by
      change atom ∈ projectedAtoms 0 (source.tracePrefix length) at member
      rw [prefixCandidate_atoms_projected length]
      exact member
    change
      sourceFor (prefixReadSources length) atom.id = readSource atom.id
    exact prefixCandidate_sourceId_eq_readSource
      length atom candidateMember
  prefixModificationOrder := by
    intro length site first second firstMember secondMember
    have firstCandidateMember :
        first ∈ (prefixCandidate length).atoms := by
      change first ∈ projectedAtoms 0 (source.tracePrefix length) at firstMember
      rw [prefixCandidate_atoms_projected length]
      exact firstMember
    have secondCandidateMember :
        second ∈ (prefixCandidate length).atoms := by
      change second ∈ projectedAtoms 0 (source.tracePrefix length) at secondMember
      rw [prefixCandidate_atoms_projected length]
      exact secondMember
    change
      IdBefore first.id second.id (prefixModificationOrder length site) ↔
        modificationOrder site first.id second.id
    constructor
    · intro before
      have firstData :=
        (mem_prefixModificationOrder_iff
          length site first.id).1 before.first_mem
      have secondData :=
        (mem_prefixModificationOrder_iff
          length site second.id).1 before.second_mem
      exact ⟨firstData.2, secondData.2,
        (prefixModificationOrder_before_iff
          length site firstData.1 secondData.1
          firstData.2 secondData.2).1 before⟩
    · rintro ⟨firstSite, secondSite, before⟩
      exact (prefixModificationOrder_before_iff length site
        (prefixAtom_id_bound length firstCandidateMember)
        (prefixAtom_id_bound length secondCandidateMember)
        firstSite secondSite).2 before

private theorem execution_source_phase_cases (time : Nat) :
    time % 9 = 0 ∨ time % 9 = 1 ∨ time % 9 = 2 ∨
      time % 9 = 3 ∨ time % 9 = 4 ∨ time % 9 = 5 ∨
      time % 9 = 6 ∨ time % 9 = 7 ∨ time % 9 = 8 := by
  omega

private theorem completedOperation_thread_zero
    {length : Nat}
    {entry : MSQueue.HW.IdentifiedCompleted Unit}
    (member :
      entry ∈ sourceCompletedOperations (source.tracePrefix length)) :
    entry.thread = 0 := by
  rw [sourceCompletedOperations] at member
  obtain ⟨record, recordMember, entryExact⟩ :=
    List.mem_map.mp member
  subst entry
  obtain ⟨emitted, emittedMember, selected⟩ :=
    List.mem_filterMap.mp recordMember
  unfold InfiniteExecution.tracePrefix at emittedMember
  obtain ⟨time, _, emittedExact⟩ :=
    List.mem_map.mp emittedMember
  subst emitted
  rcases execution_source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp_all [source, event, TraceEvent.commitRecord?,
      AtomicOccurrence.commitRecord?, identifiedCommit]
  all_goals subst record
  all_goals rfl

/-- Every finite prefix admits a client-compatible structural atom schedule. -/
theorem execution_prefixSchedules :
    execution.PrefixSchedules := by
  intro length
  have witness :
      OrderWitness (execution.supportedPrefix length).candidate := by
    change OrderWitness
      (projectCandidate 0 (source.tracePrefix length)
        (prefixReadSources length) (prefixModificationOrder length))
    rw [projectCandidate_eq_prefixCandidate]
    exact prefixCandidate_orderWitness length
  obtain ⟨schedule⟩ :=
    Structural.AtomSchedule.exists_of_orderWitness
      (execution.supportedPrefix length) witness
  refine ⟨{
    schedule := schedule
    crossThreadRealTime := ?_
  }⟩
  intro first second firstMember secondMember different _
  have firstSource :
      first ∈ sourceCompletedOperations (source.tracePrefix length) :=
    schedule.scheduledOperations_perm_source.mem_iff.mp firstMember
  have secondSource :
      second ∈ sourceCompletedOperations (source.tracePrefix length) :=
    schedule.scheduledOperations_perm_source.mem_iff.mp secondMember
  exact (different
    ((completedOperation_thread_zero firstSource).trans
      (completedOperation_thread_zero secondSource).symm)).elim

end InfiniteWitness

end WeakMemory.MSQueue.Source
