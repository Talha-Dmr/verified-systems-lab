import WeakMemory.MSQueueInfiniteSpuriousPrefix
import WeakMemory.MSQueueInfiniteSafety

namespace WeakMemory.MSQueue.Source

/-!
# Site-specific justice separation for the all-spurious queue execution

The finite prefixes are genuine source-backed RC11 executions.  Nevertheless,
the pending enqueue retries forever at `next 0`, that exact site is never
modified, and no method response occurs.  This witnesses the missing primitive
weak-CAS justice assumption inside the Michael--Scott model itself.
-/

namespace InfiniteSpurious

open WeakCAS.SiteProgressRule

theorem execution_noModificationAt_nextDummy :
    NoModificationAtFrom execution.progressInterface (.next 0) 0 := by
  intro time _
  change ¬ (source.event time).ModifiedAt (.next 0)
  exact source_noModification_nextDummy time

theorem execution_matchingAttemptsAt_nextDummy :
    Liveness.InfinitelyOften
      (execution.progressInterface.matchingAttemptAt 0 (.next 0)) := by
  change
    Liveness.InfinitelyOften fun time =>
      (source.event time).MatchingAttemptAt 0 (.next 0)
  exact source_matchingAttempts_nextDummy

/-- The exact selected site has a stable pure-spurious suffix. -/
theorem execution_stablePureSpuriousSuffixAt_nextDummy :
    StablePureSpuriousSuffixAt
      execution.progressInterface (.next 0) 0 :=
  ⟨0, execution_noModificationAt_nextDummy,
    execution_matchingAttemptsAt_nextDummy⟩

theorem execution_notPrimitiveJusticeAt_nextDummy :
    ¬ PrimitiveJusticeAt execution.progressInterface (.next 0) := by
  intro justice
  obtain ⟨time, afterStart, succeeded⟩ :=
    justice 0 0
      execution_noModificationAt_nextDummy
      execution_matchingAttemptsAt_nextDummy
  exact execution_noModificationAt_nextDummy time afterStart
    (execution.progressInterface.success_is_modification
      (.next 0) time succeeded)

theorem execution_notWeakCASJustice :
    ¬ execution.WeakCASJustice := by
  intro justice
  exact execution_notPrimitiveJusticeAt_nextDummy
    (justice (.next 0))

theorem execution_notSystemResponseProgress :
    ¬ execution.SystemResponseProgress := by
  intro progress
  have activeAtOne :
      LocalState.Active (execution.source.state 1 0) := by
    simpa [execution] using
      source_active_from_one 1 (Nat.le_refl 1)
  obtain ⟨time, _, response⟩ :=
    progress 1 ⟨0, activeAtOne⟩
  change (execution.source.event time).IsResponse at response
  exact source_noResponse time
    (by simpa [execution] using response)

/-- The queue-specific progress-site obligation is itself satisfiable here. -/
theorem execution_progressObligations :
    execution.ProgressObligations := by
  refine {
    progressSite_on_responseFreeSuffix := ?_
  }
  intro start active noResponse
  refine ⟨0, start, Nat.le_refl start, .next 0, ?_, ?_⟩
  · intro time _
    exact execution_noModificationAt_nextDummy time (Nat.zero_le time)
  · exact execution_matchingAttemptsAt_nextDummy

theorem execution_recurringDemand :
    execution.RecurringDemand := by
  intro bound
  let time := max bound 1
  refine ⟨time, Nat.le_max_left bound 1, 0, ?_⟩
  have afterInvocation : 1 ≤ time := Nat.le_max_right bound 1
  simpa [execution] using
    source_active_from_one time afterInvocation

@[simp] theorem occurrence_commitRecord_none (index : Nat) :
    (occurrence index).commitRecord? = none := by
  cases index with
  | zero =>
      simp [occurrence, AtomicOccurrence.commitRecord?]
  | succ index =>
      cases index with
      | zero =>
          simp [occurrence, AtomicOccurrence.commitRecord?]
      | succ index =>
          cases index with
          | zero =>
              simp [occurrence, AtomicOccurrence.commitRecord?]
          | succ index =>
              cases index with
              | zero =>
                  simp [occurrence, AtomicOccurrence.commitRecord?]
              | succ retry =>
                  cases phase : retryPhase retry <;>
                    simp [occurrence, phase,
                      AtomicOccurrence.commitRecord?]

theorem sourceCompletedOperations_tracePrefix (length : Nat) :
    sourceCompletedOperations (source.tracePrefix length) = [] := by
  cases length with
  | zero => rfl
  | succ length =>
      cases length with
      | zero =>
          rfl
      | succ count =>
          rw [tracePrefix_two_add count]
          simp [sourceCompletedOperations, List.filterMap_map,
            Function.comp_def, TraceEvent.commitRecord?]

/-- Every finite prefix admits the structural schedule required for safety. -/
theorem execution_prefixSchedules :
    execution.PrefixSchedules := by
  intro length
  have witness :
      MultiLocationRC11.OrderWitness
        (execution.supportedPrefix length).candidate := by
    change MultiLocationRC11.OrderWitness (prefixCandidate length)
    rw [prefixCandidate_eq_denseCandidate]
    exact denseCandidate_orderWitness (atomCount length)
  obtain ⟨schedule⟩ :=
    Structural.AtomSchedule.exists_of_orderWitness
      (execution.supportedPrefix length) witness
  refine ⟨{
    schedule := schedule
    crossThreadRealTime := ?_
  }⟩
  intro first second firstMember secondMember different realTime
  have sourceEmpty :
      sourceCompletedOperations (source.tracePrefix length) = [] :=
    sourceCompletedOperations_tracePrefix length
  have executionSourceEmpty :
      sourceCompletedOperations
          (execution.source.tracePrefix length) = [] := by
    simpa [execution] using sourceEmpty
  have permutation := schedule.scheduledOperations_perm_source
  rw [executionSourceEmpty] at permutation
  have scheduledEmpty : schedule.scheduledOperations = [] :=
    List.Perm.eq_nil permutation
  rw [scheduledEmpty] at firstMember
  simp at firstMember

/-- Headline queue-specific independence theorem. -/
theorem nextDummy_allSpurious_separates_justice_from_progress :
    ∃ candidate : InfiniteRC11Execution Unit 1 0,
      candidate.PrefixSchedules ∧
        candidate.ProgressObligations ∧
        candidate.RecurringDemand ∧
        StablePureSpuriousSuffixAt
          candidate.progressInterface (.next 0) 0 ∧
        ¬ PrimitiveJusticeAt
          candidate.progressInterface (.next 0) ∧
        ¬ candidate.WeakCASJustice ∧
        ¬ candidate.SystemResponseProgress :=
  ⟨execution,
    execution_prefixSchedules,
    execution_progressObligations,
    execution_recurringDemand,
    execution_stablePureSpuriousSuffixAt_nextDummy,
    execution_notPrimitiveJusticeAt_nextDummy,
    execution_notWeakCASJustice,
    execution_notSystemResponseProgress⟩

end InfiniteSpurious

end WeakMemory.MSQueue.Source
