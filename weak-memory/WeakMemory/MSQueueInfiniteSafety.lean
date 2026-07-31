import WeakMemory.MSQueueInfinite
import WeakMemory.MSQueueSourceHistoryBridge

namespace WeakMemory.MSQueue.Source

/-!
# Finite-prefix safety and conditional lock-freedom

This module combines the coherent infinite queue carrier with the finite
Herlihy--Wing bridge and the site-indexed progress theorem.  Cross-thread real
time is not an RC11 edge and therefore accompanies each chosen prefix schedule
explicitly.
-/

namespace InfiniteRC11Execution

/-- A client-compatible structural schedule is available at every prefix. -/
def PrefixSchedules
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  ∀ length,
    Nonempty
      (Structural.ClientCompatibleSchedule
        (execution.supportedPrefix length))

/-- Complete safety for every finite prefix and system-wide response progress. -/
structure LinearizableLockFreeGuarantees
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop where
  finitePrefixSafety :
    ∀ length,
      MSQueue.HW.Linearizable []
        (sourceHistory (execution.source.tracePrefix length))
  systemResponseProgress : execution.SystemResponseProgress

/-- The lock-free bundle plus unbounded responses under recurring demand. -/
structure LinearizableLongRunGuarantees
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop where
  lockFreedom : execution.LinearizableLockFreeGuarantees
  infinitelyManyResponses : execution.InfinitelyManyResponses

/--
End-to-end conditional result: every finite prefix is FIFO-linearizable and
every active suffix eventually contains a response.
-/
theorem linearizableLockFree_of_siteJustice
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (obligations : execution.ProgressObligations)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees where
  finitePrefixSafety := by
    intro length
    obtain ⟨compatible⟩ := prefixSchedules length
    exact compatible.linearizable
  systemResponseProgress :=
    execution.systemResponseProgress_of_siteJustice obligations justice

/-- Strong CAS supplies justice for the same finite-prefix safety bundle. -/
theorem linearizableLockFree_of_strongCAS
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (obligations : execution.ProgressObligations)
    (strong :
      ∀ site thread time,
        execution.progressInterface.matchingAttemptAt
            thread site time →
          execution.progressInterface.succeededAt site time) :
    execution.LinearizableLockFreeGuarantees where
  finitePrefixSafety := by
    intro length
    obtain ⟨compatible⟩ := prefixSchedules length
    exact compatible.linearizable
  systemResponseProgress :=
    execution.systemResponseProgress_of_strongCAS obligations strong

/-- Recurring active demand upgrades conditional lock-freedom to late responses. -/
theorem linearizableLongRun_of_siteJustice
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (recurring : execution.RecurringDemand)
    (obligations : execution.ProgressObligations)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees := by
  let lockFreedom := execution.linearizableLockFree_of_siteJustice
    prefixSchedules obligations justice
  exact {
    lockFreedom := lockFreedom
    infinitelyManyResponses :=
      execution.infinitelyManyResponses_of_systemResponseProgress
        recurring lockFreedom.systemResponseProgress
  }

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
