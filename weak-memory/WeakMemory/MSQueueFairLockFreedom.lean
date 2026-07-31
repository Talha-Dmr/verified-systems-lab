import WeakMemory.MSQueueInfiniteFairProgress
import WeakMemory.MSQueueInfiniteSafety

namespace WeakMemory.MSQueue.Source

/-!
# Fair RC11 lock-freedom for the Michael--Scott queue

This module closes the gap left by the earlier conditional infinite-execution
result.  Its public theorems no longer accept a packaged `ProgressObligations`
premise.  Instead, the queue source semantics derive those obligations from:

* a client-compatible structural schedule for every finite prefix;
* weak fairness of continuously enabled source threads;
* selected-site RC11 visibility, or the stronger prefix-finite `fr`/paired
  memory-fairness assumptions that imply it; and
* primitive weak-CAS justice independently at every logical queue site.

The safety half is Herlihy--Wing FIFO linearizability of every finite prefix.
The liveness half is system lock-freedom: every state containing an active
method has a response at some later source position.
-/

namespace InfiniteRC11Execution

/-- Concrete scheduler and selected-site visibility fairness yield a later
method response from every active state once site-wise weak-CAS justice is
assumed. -/
theorem systemResponseProgress_of_selectedSiteVisibilityFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (visibility : execution.SelectedSiteVisibilityFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_siteJustice
    (execution.progressObligations_of_selectedSiteVisibilityFair
      prefixSchedules.toPrefixAtomSchedules threadFair visibility)
    justice

/-- Prefix-finite per-site `fr` is the exact RC11 visibility assumption used
by the queue progress proof. -/
theorem systemResponseProgress_of_fromReadFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_selectedSiteVisibilityFair
    prefixSchedules threadFair
    (execution.selectedSiteVisibilityFair_of_fromReadFair fromReadFair)
    justice

/-- Conventional paired per-site RC11 memory fairness supplies the exact
prefix-finite `fr` premise consumed by progress. -/
theorem systemResponseProgress_of_fairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_fromReadFairness
    prefixSchedules threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

/-- The exact scheduler/visibility theorem already carries both finite-prefix
safety and response progress; no packaged progress obligation is exposed. -/
theorem linearizableLockFree_of_selectedSiteVisibilityFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (visibility : execution.SelectedSiteVisibilityFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees where
  finitePrefixSafety := by
    intro length
    obtain ⟨compatible⟩ := prefixSchedules length
    exact compatible.linearizable
  systemResponseProgress :=
    execution.systemResponseProgress_of_selectedSiteVisibilityFair
      prefixSchedules threadFair visibility justice

/--
Exact-assumption end-to-end result: every finite prefix is FIFO-linearizable,
and every active suffix eventually contains a method response.
-/
theorem linearizableLockFree_of_fromReadFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_selectedSiteVisibilityFair
    prefixSchedules threadFair
    (execution.selectedSiteVisibilityFair_of_fromReadFair fromReadFair)
    justice

/--
Public fairness theorem for the explicit reclamation-free RC11
Michael--Scott queue.  The result combines finite-prefix Herlihy--Wing FIFO
linearizability with system lock-freedom and has no packaged algorithmic
progress premise.
-/
theorem linearizableLockFree_of_fairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_fromReadFairness
    prefixSchedules threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

/-- With strong compare-equal CAS, primitive justice is derivable rather than
an additional premise. -/
theorem linearizableLockFree_of_strongCASFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (strong :
      ∀ site thread time,
        execution.progressInterface.matchingAttemptAt thread site time →
          execution.progressInterface.succeededAt site time) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_fairness
    prefixSchedules threadFair memoryFair
    (WeakCAS.SiteProgressRule.primitiveJustice_of_matchingAttemptsSucceed
      execution.progressInterface strong)

/-- Recurring active demand upgrades one-step lock-freedom to responses at
arbitrarily late positions under the exact `fr` assumption. -/
theorem linearizableLongRun_of_fromReadFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (recurring : execution.RecurringDemand)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees := by
  let lockFreedom := execution.linearizableLockFree_of_fromReadFairness
    prefixSchedules threadFair fromReadFair justice
  exact {
    lockFreedom := lockFreedom
    infinitelyManyResponses :=
      execution.infinitelyManyResponses_of_systemResponseProgress
        recurring lockFreedom.systemResponseProgress
  }

/-- Under recurring active demand, paired memory fairness yields responses at
arbitrarily late positions in addition to the finite-prefix safety theorem. -/
theorem linearizableLongRun_of_fairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (recurring : execution.RecurringDemand)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fromReadFairness
    prefixSchedules recurring threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
