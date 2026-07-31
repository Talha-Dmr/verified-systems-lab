import WeakMemory.MSQueueInfiniteWitnessExecution
import WeakMemory.MSQueueFairLockFreedom

namespace WeakMemory.MSQueue.Source

/-!
# Fairness of the successful infinite queue witness

This module packages the temporal assumptions of the concrete one-thread
enqueue execution.  The source run and its coherent finite RC11 prefixes live
in the two preceding witness modules; only infinite-position fairness,
site-wise primitive justice, and the final public theorem application belong
here.
-/

namespace InfiniteWitness

private theorem source_phase_cases (time : Nat) :
    time % 9 = 0 ∨
      time % 9 = 1 ∨
      time % 9 = 2 ∨
      time % 9 = 3 ∨
      time % 9 = 4 ∨
      time % 9 = 5 ∨
      time % 9 = 6 ∨
      time % 9 = 7 ∨
      time % 9 = 8 := by
  omega

/-- Every atomic source event lies in one of the six dense atomic phases and
has the corresponding dense identifier. -/
theorem source_atomic_id_shape
    (time : Nat)
    (occurrence : AtomicOccurrence Unit)
    (atTime : source.event time = .atomic occurrence) :
    ∃ phase,
      2 ≤ phase ∧
        phase ≤ 7 ∧
        time % 9 = phase ∧
        occurrence.id = 6 * (time / 9) + phase + 1 := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  · simp [source, event, phase] at atTime
  · simp [source, event, phase] at atTime
  · refine ⟨2, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · refine ⟨3, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · refine ⟨4, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · refine ⟨5, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · refine ⟨6, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · refine ⟨7, by omega, by omega, phase, ?_⟩
    simp [source, event, phase] at atTime
    subst occurrence
    simp [Nat.add_assoc]
  · simp [source, event, phase] at atTime

/-- Dense atomic identifier order respects chronological source time. -/
theorem source_atomic_time_le_of_id_le
    {firstTime secondTime : Nat}
    {first second : AtomicOccurrence Unit}
    (firstAt : source.event firstTime = .atomic first)
    (secondAt : source.event secondTime = .atomic second)
    (ordered : first.id ≤ second.id) :
    firstTime ≤ secondTime := by
  obtain ⟨firstPhase, firstLower, firstUpper,
      firstRemainder, firstId⟩ :=
    source_atomic_id_shape firstTime first firstAt
  obtain ⟨secondPhase, secondLower, secondUpper,
      secondRemainder, secondId⟩ :=
    source_atomic_id_shape secondTime second secondAt
  have numericOrder :
      6 * (firstTime / 9) + firstPhase + 1 ≤
        6 * (secondTime / 9) + secondPhase + 1 := by
    calc
      _ = first.id := firstId.symm
      _ ≤ second.id := ordered
      _ = _ := secondId
  have firstDivision := Nat.mod_add_div firstTime 9
  have secondDivision := Nat.mod_add_div secondTime 9
  omega

/-- Every dynamic source atomic identifier follows the three static queue
initializers. -/
theorem source_atomic_id_at_least_three
    {time : Nat}
    {occurrence : AtomicOccurrence Unit}
    (atTime : source.event time = .atomic occurrence) :
    3 ≤ occurrence.id := by
  obtain ⟨phase, lower, _, _, identifier⟩ :=
    source_atomic_id_shape time occurrence atTime
  rw [identifier]
  calc
    3 ≤ phase + 1 := Nat.add_le_add_right lower 1
    _ ≤ 6 * (time / 9) + phase + 1 := by omega

/-- A non-static graph position for any carrier with this source run exposes
the source atomic occurrence represented there. -/
theorem graphEventId?_add_three_shape
    (candidate : InfiniteRC11Execution Unit 1 0)
    (sourceExact : candidate.source = source)
    {time : Nat}
    {eventId : EventId}
    (atPosition :
      candidate.graphEventId? (time + 3) = some eventId) :
    ∃ occurrence : AtomicOccurrence Unit,
      source.event time = .atomic occurrence ∧
        occurrence.id = eventId := by
  cases eventAt : source.event time <;>
    simp [InfiniteRC11Execution.graphEventId?, sourceExact,
      eventAt] at atPosition
  rename_i occurrence
  exact ⟨occurrence, rfl, atPosition⟩

/-- Numeric identifier order in the concrete graph respects graph-position
order.  Positions zero through two are the static initializers; position
`time + 3` represents the atomic source event at `time`, when one exists. -/
theorem graph_position_le_of_id_le
    (candidate : InfiniteRC11Execution Unit 1 0)
    (sourceExact : candidate.source = source)
    {firstPosition secondPosition : Nat}
    {firstId secondId : EventId}
    (firstAt :
      candidate.graphEventId? firstPosition = some firstId)
    (secondAt :
      candidate.graphEventId? secondPosition = some secondId)
    (ordered : firstId ≤ secondId) :
    firstPosition ≤ secondPosition := by
  rcases firstPosition with _ | _ | _ | firstTime
  · exact Nat.zero_le _
  · rcases secondPosition with _ | _ | _ | secondTime
    · have firstIdExact : firstId = 1 := by
        exact Option.some.inj (firstAt.symm.trans rfl)
      have secondIdExact : secondId = 0 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [firstIdExact, secondIdExact] at ordered
      omega
    · exact Nat.le_refl 1
    · omega
    · omega
  · rcases secondPosition with _ | _ | _ | secondTime
    · have firstIdExact : firstId = 2 := by
        exact Option.some.inj (firstAt.symm.trans rfl)
      have secondIdExact : secondId = 0 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [firstIdExact, secondIdExact] at ordered
      omega
    · have firstIdExact : firstId = 2 := by
        exact Option.some.inj (firstAt.symm.trans rfl)
      have secondIdExact : secondId = 1 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [firstIdExact, secondIdExact] at ordered
      omega
    · exact Nat.le_refl 2
    · omega
  · obtain ⟨firstOccurrence, firstEvent, firstIdExact⟩ :=
      graphEventId?_add_three_shape
        candidate sourceExact firstAt
    have firstIdLower : 3 ≤ firstId := by
      rw [← firstIdExact]
      exact source_atomic_id_at_least_three firstEvent
    rcases secondPosition with _ | _ | _ | secondTime
    · have secondIdExact : secondId = 0 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [secondIdExact] at ordered
      exact False.elim
        ((Nat.not_le_of_gt
          (Nat.lt_of_lt_of_le (by decide : 0 < 3) firstIdLower)) ordered)
    · have secondIdExact : secondId = 1 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [secondIdExact] at ordered
      exact False.elim
        ((Nat.not_le_of_gt
          (Nat.lt_of_lt_of_le (by decide : 1 < 3) firstIdLower)) ordered)
    · have secondIdExact : secondId = 2 := by
        exact Option.some.inj (secondAt.symm.trans rfl)
      rw [secondIdExact] at ordered
      exact False.elim
        ((Nat.not_le_of_gt
          (Nat.lt_of_succ_le firstIdLower)) ordered)
    · obtain ⟨secondOccurrence, secondEvent, secondIdExact⟩ :=
        graphEventId?_add_three_shape
          candidate sourceExact secondAt
      rw [← firstIdExact, ← secondIdExact] at ordered
      have timeOrder :=
        source_atomic_time_le_of_id_le
          firstEvent secondEvent ordered
      omega

/-- Every compare-equal CAS attempt in the success-only source run succeeds
at that same logical queue site. -/
theorem source_matchingAttempt_succeeds
    {site : Site}
    {thread : ThreadId}
    {time : Nat}
    (matching :
      (source.event time).MatchingAttemptAt thread site) :
    (source.event time).SucceededAt site := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp_all [source, event,
      TraceEvent.MatchingAttemptAt, TraceEvent.SucceededAt,
      AtomicAction.IsMatchingCAS, AtomicAction.casView?,
      AtomicAction.site, AtomicAction.succeededCAS]

/-- Every completed source operation in this one-thread witness belongs to
thread zero. -/
theorem sourceCompletedOperations_thread_zero
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
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  all_goals
    simp_all [source, event, TraceEvent.commitRecord?,
      AtomicOccurrence.commitRecord?, identifiedCommit]
  all_goals subst record
  all_goals rfl

/-- Concrete modification-order edges point forward in graph positions. -/
theorem execution_modificationOrderAt_position_lt
    {site : Site}
    {firstPosition secondPosition : Nat}
    (edge :
      execution.ModificationOrderAt
        site firstPosition secondPosition) :
    firstPosition < secondPosition := by
  obtain ⟨firstId, secondId, firstAt, secondAt, ordered⟩ := edge
  have idOrder : firstId < secondId := ordered.2.2
  have positionOrder : firstPosition ≤ secondPosition :=
    graph_position_le_of_id_le execution rfl
      firstAt secondAt (Nat.le_of_lt idOrder)
  apply Nat.lt_of_le_of_ne positionOrder
  intro samePosition
  subst secondPosition
  have sameId : firstId = secondId :=
    Option.some.inj (firstAt.symm.trans secondAt)
  exact (Nat.ne_of_lt idOrder) sameId

/-- Concrete from-read edges point forward in graph positions. -/
theorem execution_fromReadAt_position_lt
    {site : Site}
    {readPosition writePosition : Nat}
    (edge :
      execution.FromReadAt site readPosition writePosition) :
    readPosition < writePosition := by
  obtain ⟨readId, sourceId, writeId,
      readAt, writeAt, readsFrom, ordered, different⟩ := edge
  have idOrder : readId ≤ writeId :=
    readSource_target_le_of_modificationOrder
      readsFrom ordered
  have positionOrder : readPosition ≤ writePosition :=
    graph_position_le_of_id_le execution rfl
      readAt writeAt idOrder
  exact Nat.lt_of_le_of_ne positionOrder different

/-- The position-indexed modification order and from-read relation are
prefix-finite independently at every queue site. -/
theorem execution_memoryFair :
    execution.MemoryFair := by
  intro site
  constructor
  · intro target
    refine ⟨target, ?_⟩
    intro sourcePosition edge
    exact execution_modificationOrderAt_position_lt edge
  · intro target
    refine ⟨target, ?_⟩
    intro readPosition edge
    exact execution_fromReadAt_position_lt edge

/-- Exact prefix-finite from-read fairness follows from conventional paired
memory fairness. -/
theorem execution_fromReadFair :
    execution.FromReadFair :=
  execution.fromReadFair_of_memoryFair execution_memoryFair

/-- The concrete execution inherits weak scheduling fairness from its source
run. -/
theorem execution_threadFair :
    execution.source.WeakThreadFair := by
  simpa [execution] using source_threadFair

/-- Every matching CAS attempt in the concrete RC11 execution succeeds at the
same site. -/
theorem execution_matchingAttemptsSucceed :
    ∀ site thread time,
      execution.progressInterface.matchingAttemptAt
          thread site time →
        execution.progressInterface.succeededAt site time := by
  intro site thread time matching
  change
    (execution.source.event time).MatchingAttemptAt
      thread site at matching
  change (execution.source.event time).SucceededAt site
  simpa [execution] using
    (source_matchingAttempt_succeeds matching)

/-- Site-wise primitive weak-CAS justice is derivable because the successful
witness contains no spurious or mismatching CAS attempt. -/
theorem execution_weakCASJustice :
    execution.WeakCASJustice :=
  WeakCAS.SiteProgressRule.primitiveJustice_of_matchingAttemptsSucceed
    execution.progressInterface execution_matchingAttemptsSucceed

/-- Active enqueue demand recurs arbitrarily late. -/
theorem execution_recurringDemand :
    execution.RecurringDemand := by
  simpa [InfiniteRC11Execution.RecurringDemand, execution] using
    source_enqueueDemand_often

/-- The explicit source already contains method responses at arbitrarily late
positions. -/
theorem execution_responses_often :
    execution.InfinitelyManyResponses := by
  simpa [InfiniteRC11Execution.InfinitelyManyResponses, execution] using
    source_responses_often

/-- Successful queue CAS events occur at arbitrarily late execution
positions. -/
theorem execution_successfulCAS_often :
    Liveness.InfinitelyOften (fun time =>
      ∃ site,
        execution.progressInterface.succeededAt site time) := by
  simpa [InfiniteRC11Execution.progressInterface, execution] using
    source_successfulCAS_often

/-- Client-compatible schedules also provide the weaker structural schedules
used by the concrete progress derivation. -/
theorem execution_prefixAtomSchedules :
    execution.PrefixAtomSchedules :=
  execution_prefixSchedules.toPrefixAtomSchedules

/-- Per-site memory fairness gives the selected-site visibility rule consumed
by stable retry control. -/
theorem execution_selectedSiteVisibilityFair :
    execution.SelectedSiteVisibilityFair :=
  execution.selectedSiteVisibilityFair_of_memoryFair execution_memoryFair

/-- The queue-specific progress-site package is derived from concrete
scheduling and memory fairness rather than postulated for the witness. -/
theorem execution_progressObligations :
    execution.ProgressObligations :=
  execution.progressObligations_of_memoryFairness
    execution_prefixAtomSchedules
    execution_threadFair
    execution_memoryFair

/-- The final fair-RC11 theorem applies to the successful coherent queue
execution, yielding finite-prefix FIFO linearizability, system lock-freedom,
and responses at arbitrarily late positions. -/
theorem successfulWitness_linearizableLongRun :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fairness
    execution_prefixSchedules
    execution_recurringDemand
    execution_threadFair
    execution_memoryFair
    execution_weakCASJustice

/-- All concrete premises of the public Michael--Scott fairness theorem are
jointly satisfiable on one success-rich coherent infinite RC11 execution. -/
theorem successfulAssumptionsJointlySatisfiable :
    ∃ candidate : InfiniteRC11Execution Unit 1 0,
      candidate.PrefixSchedules ∧
        candidate.PrefixAtomSchedules ∧
        candidate.source.WeakThreadFair ∧
        candidate.MemoryFair ∧
        candidate.FromReadFair ∧
        candidate.SelectedSiteVisibilityFair ∧
        candidate.ProgressObligations ∧
        candidate.RecurringDemand ∧
        candidate.WeakCASJustice ∧
        Liveness.InfinitelyOften (fun time =>
          ∃ site,
            candidate.progressInterface.succeededAt site time) ∧
        candidate.InfinitelyManyResponses ∧
        candidate.LinearizableLongRunGuarantees :=
  ⟨execution,
    execution_prefixSchedules,
    execution_prefixAtomSchedules,
    execution_threadFair,
    execution_memoryFair,
    execution_fromReadFair,
    execution_selectedSiteVisibilityFair,
    execution_progressObligations,
    execution_recurringDemand,
    execution_weakCASJustice,
    execution_successfulCAS_often,
    execution_responses_often,
    successfulWitness_linearizableLongRun⟩

end InfiniteWitness

end WeakMemory.MSQueue.Source
