import WeakMemory.MSQueueInfiniteSpuriousSeparation
import WeakMemory.MSQueueInfiniteFairProgress

namespace WeakMemory.MSQueue.Source

/-!
# Concrete fairness of the all-spurious queue execution

The all-spurious execution is not merely a model satisfying a packaged
progress premise.  Its sole active thread is weakly scheduled forever, every
finite prefix has the queue's client-compatible schedule, and its global
modification-order and from-read relations are empty.  It therefore satisfies
the concrete scheduler and RC11 memory-fairness assumptions while failing
primitive weak-CAS justice and system response progress at `next 0`.
-/

namespace InfiniteSpurious

open WeakCAS.SiteProgressRule

/-- The sole participating source thread is scheduled at every position. -/
theorem source_threadFair :
    source.WeakThreadFair := by
  intro thread continuouslyEnabled
  by_cases owner : thread = 0
  · subst thread
    change
      Liveness.InfinitelyOften (fun time =>
        some (source.event time).thread = some 0)
    exact Liveness.InfinitelyOften.of_forall
      (fun time => congrArg some (event_thread time))
  · obtain ⟨start, enabled⟩ := continuouslyEnabled
    have active :
        (source.state start thread).Active :=
      enabled start (Nat.le_refl start)
    have idle : source.state start thread = .idle := by
      simp [source, state, owner]
    rw [idle] at active
    simp [LocalState.Active] at active

/-- The concrete RC11 execution inherits weak fairness from its source. -/
theorem execution_threadFair :
    execution.source.WeakThreadFair := by
  simpa [execution] using source_threadFair

/-- The global position-indexed modification order has no edges. -/
theorem execution_modificationOrderAt_false
    (site : Site)
    (first second : Nat) :
    ¬ execution.ModificationOrderAt site first second := by
  rintro ⟨firstId, secondId, _, _, ordered⟩
  exact ordered

/-- The position-indexed from-read relation has no edges either. -/
theorem execution_fromReadAt_false
    (site : Site)
    (read laterWrite : Nat) :
    ¬ execution.FromReadAt site read laterWrite := by
  rintro ⟨readId, sourceId, writeId, _, _, _, ordered, _⟩
  exact ordered

/-!
Infinite RF fan-out from the static initializers is harmless here: memory
fairness asks for prefix-finite `mo` and `fr`, not prefix-finite inverse RF.
Both relations are empty because every represented site has only one write.
-/
theorem execution_memoryFair :
    execution.MemoryFair := by
  intro site
  constructor
  · intro target
    refine ⟨0, ?_⟩
    intro sourcePosition edge
    exact
      (execution_modificationOrderAt_false
        site sourcePosition target edge).elim
  · intro target
    refine ⟨0, ?_⟩
    intro readPosition edge
    exact
      (execution_fromReadAt_false
        site readPosition target edge).elim

/-- The exact prefix-finite from-read assumption used by visibility. -/
theorem execution_fromReadFair :
    execution.FromReadFair :=
  execution.fromReadFair_of_memoryFair execution_memoryFair

/-- RC11 memory fairness yields the queue's selected-site visibility rule. -/
theorem execution_selectedSiteVisibilityFair :
    execution.SelectedSiteVisibilityFair :=
  execution.selectedSiteVisibilityFair_of_fromReadFair
    execution_fromReadFair

/-- Client-compatible schedules also provide structural atom schedules. -/
theorem execution_prefixAtomSchedules :
    execution.PrefixAtomSchedules :=
  execution_prefixSchedules.toPrefixAtomSchedules

/-- The concrete scheduling and RC11 fairness facts derive, rather than
assume, the queue-specific progress-site obligation. -/
theorem execution_progressObligations_from_fairness :
    execution.ProgressObligations :=
  execution.progressObligations_of_memoryFairness
    execution_prefixAtomSchedules
    execution_threadFair
    execution_memoryFair

/-!
Headline concrete separation.  Scheduler fairness, per-site RC11 memory
fairness, and both finite-prefix scheduling layers all hold, while the exact
stable matching-attempt suffix at `next 0` refutes primitive justice and
system response progress.
-/
theorem concrete_fairness_without_primitive_justice :
    ∃ candidate : InfiniteRC11Execution Unit 1 0,
      candidate.PrefixSchedules ∧
        candidate.PrefixAtomSchedules ∧
        candidate.source.WeakThreadFair ∧
        candidate.MemoryFair ∧
        candidate.FromReadFair ∧
        candidate.SelectedSiteVisibilityFair ∧
        candidate.ProgressObligations ∧
        StablePureSpuriousSuffixAt
          candidate.progressInterface (.next 0) 0 ∧
        ¬ PrimitiveJusticeAt
          candidate.progressInterface (.next 0) ∧
        ¬ candidate.WeakCASJustice ∧
        ¬ candidate.SystemResponseProgress :=
  ⟨execution,
    execution_prefixSchedules,
    execution_prefixAtomSchedules,
    execution_threadFair,
    execution_memoryFair,
    execution_fromReadFair,
    execution_selectedSiteVisibilityFair,
    execution_progressObligations_from_fairness,
    execution_stablePureSpuriousSuffixAt_nextDummy,
    execution_notPrimitiveJusticeAt_nextDummy,
    execution_notWeakCASJustice,
    execution_notSystemResponseProgress⟩

end InfiniteSpurious

end WeakMemory.MSQueue.Source
