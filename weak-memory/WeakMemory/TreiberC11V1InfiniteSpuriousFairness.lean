import WeakMemory.TreiberC11V1InfiniteSpuriousPrefix

namespace WeakMemory.TreiberC11V1

/-!
# Fairness separation on the concrete all-spurious Treiber execution

The coherent RC11 carrier has no modification-order or from-read edges, so it
is memory-fair.  Its only thread is scheduled forever.  Nevertheless, the
single pending push never responds because every compare-equal weak CAS fails
spuriously.  This witnesses that primitive weak-CAS justice is independent of
scheduler and memory fairness inside the actual Treiber/RC11 model.
-/

namespace InfiniteSpurious

/-- Position-indexed modification order is empty. -/
theorem execution_modificationOrderAt_false
    (first second : Nat) :
    ¬ execution.ModificationOrderAt first second := by
  rintro ⟨firstId, secondId, _, _, ordered⟩
  exact ordered

/-- Position-indexed from-read is empty because global MO is empty. -/
theorem execution_fromReadAt_false
    (read laterWrite : Nat) :
    ¬ execution.FromReadAt read laterWrite := by
  rintro ⟨readId, sourceId, writeId, _, _, _,
    ordered, _⟩
  exact ordered

/--
Both memory-fairness relations are empty.  Infinite RF fan-out from the
initializer is intentionally permitted by prefix-finite `mo`/`fr` fairness.
-/
theorem execution_memoryFair :
    execution.MemoryFair := by
  constructor
  · intro target
    refine ⟨0, ?_⟩
    intro sourcePosition edge
    exact
      (execution_modificationOrderAt_false
        sourcePosition target edge).elim
  · intro target
    refine ⟨0, ?_⟩
    intro readPosition edge
    exact
      (execution_fromReadAt_false
        readPosition target edge).elim

/-- The concrete execution inherits weak scheduling fairness from its source. -/
theorem execution_threadFair :
    execution.source.WeakThreadFair := by
  simpa [execution] using source_threadFair

/-- The pending push remains genuine recurring push/pop demand. -/
theorem execution_recurringPushPopDemand :
    execution.RecurringPushPopDemand := by
  intro bound
  let time := max bound 1
  refine ⟨time, ?_, 0, ?_⟩
  · exact Nat.le_max_left bound 1
  · have afterInvocation : 1 ≤ time :=
      Nat.le_max_right bound 1
    simpa [execution] using
      source_pushPopActive_from_one time afterInvocation

/-- No successful CAS occurs on any suffix. -/
theorem execution_noSuccessfulCASFrom
    (start : Nat) :
    execution.NoSuccessfulCASFrom start := by
  intro time _
  simpa [execution] using source_noSuccessfulCAS time

/-- Matching attempts by the sole thread occur arbitrarily late. -/
theorem execution_matchingCASAttemptsByZero :
    Liveness.InfinitelyOften
      (execution.MatchingCASAttemptBy 0) := by
  change
    Liveness.InfinitelyOften
      (fun time =>
        (execution.source.event time).thread = 0 ∧
          (execution.source.event time).CASComparesEqual)
  simpa [execution] using source_matchingCASAttemptsByZero

/--
Primitive weak-CAS justice fails: its stable all-failure premise and matching
attempt premise both hold, but its successful-attempt conclusion never does.
-/
theorem execution_notWeakCASJustice :
    ¬ execution.WeakCASJustice := by
  intro justice
  obtain ⟨time, _, _, successful⟩ :=
    justice 0 0
      (execution_noSuccessfulCASFrom 0)
      execution_matchingCASAttemptsByZero
  exact source_noSuccessfulCAS time
    (by simpa [execution] using successful)

/-- The forever-active push has no later method response. -/
theorem execution_notSystemResponseProgress :
    ¬ execution.SystemResponseProgress := by
  intro progress
  have activeAtOne :
      Active (execution.source.state 1 0) := by
    simpa [execution] using
      source_active_from_one 1 (Nat.le_refl 1)
  obtain ⟨time, _, response⟩ :=
    progress 1 ⟨0, activeAtOne⟩
  exact source_noResponse time
    (by simpa [execution] using response)

/-- Consequently the source contains no method responses infinitely often. -/
theorem execution_notInfinitelyManyResponses :
    ¬ execution.InfinitelyManyResponses := by
  intro responses
  obtain ⟨time, _, response⟩ := responses 0
  exact source_noResponse time
    (by simpa [execution] using response)

/--
Headline Treiber-specific independence theorem: coherent finite-prefix RC11,
weak thread fairness, full prefix-finite memory fairness, and recurring client
demand coexist with failure of both primitive justice and response progress.
-/
theorem threadFair_memoryFair_do_not_imply_progress :
    ∃ candidate : InfiniteRC11Execution Unit 1,
      candidate.source.WeakThreadFair ∧
        candidate.MemoryFair ∧
        candidate.RecurringPushPopDemand ∧
        ¬ candidate.WeakCASJustice ∧
        ¬ candidate.SystemResponseProgress :=
  ⟨execution,
    execution_threadFair,
    execution_memoryFair,
    execution_recurringPushPopDemand,
    execution_notWeakCASJustice,
    execution_notSystemResponseProgress⟩

end InfiniteSpurious

end WeakMemory.TreiberC11V1
