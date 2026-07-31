import WeakMemory.MSQueueFairLockFreedom
import WeakMemory.MSQueueInfiniteSpuriousFairness
import WeakMemory.MSQueueInfiniteWitnessFairness

namespace WeakMemory.MSQueueResult

/-!
# Public theorem surface for the Michael--Scott queue

This module collects the exact and conventional fairness results together
with concrete negative and positive executions.  It introduces no additional
semantic assumptions.
-/

/--
Exact progress theorem: client-compatible prefix schedules, weak thread
fairness, prefix-finite from-read, and site-wise weak-CAS justice imply a later
method response from every active source state.
-/
theorem systemResponseProgressOfFromReadFairness
    (execution :
      MSQueue.Source.InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_fromReadFairness
    prefixSchedules threadFair fromReadFair justice

/--
Under the exact prefix-finite from-read premise, every finite prefix is FIFO
linearizable and the infinite execution has system response progress.
-/
theorem linearizableLockFreeOfFromReadFairness
    (execution :
      MSQueue.Source.InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_fromReadFairness
    prefixSchedules threadFair fromReadFair justice

/--
Conventional paired modification-order/from-read memory fairness implies
finite-prefix FIFO linearizability and system lock-freedom.
-/
theorem linearizableLockFreeOfMemoryFairness
    (execution :
      MSQueue.Source.InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_fairness
    prefixSchedules threadFair memoryFair justice

/--
With recurring demand, conventional memory fairness additionally yields
responses at arbitrarily late source positions.
-/
theorem linearizableLongRunOfMemoryFairness
    (execution :
      MSQueue.Source.InfiniteRC11Execution Value threadCount dummy)
    (prefixSchedules : execution.PrefixSchedules)
    (recurring : execution.RecurringDemand)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fairness
    prefixSchedules recurring threadFair memoryFair justice

/--
Concrete separation: scheduling and RC11 memory fairness can coexist with a
stable all-spurious CAS suffix, while primitive justice and response progress
both fail.
-/
theorem allSpuriousSeparation :
    ∃ candidate :
        MSQueue.Source.InfiniteRC11Execution Unit 1 0,
      candidate.PrefixSchedules ∧
        candidate.PrefixAtomSchedules ∧
        candidate.source.WeakThreadFair ∧
        candidate.MemoryFair ∧
        candidate.FromReadFair ∧
        candidate.SelectedSiteVisibilityFair ∧
        candidate.ProgressObligations ∧
        WeakCAS.SiteProgressRule.StablePureSpuriousSuffixAt
          candidate.progressInterface (.next 0) 0 ∧
        ¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
          candidate.progressInterface (.next 0) ∧
        ¬ candidate.WeakCASJustice ∧
        ¬ candidate.SystemResponseProgress :=
  MSQueue.Source.InfiniteSpurious.concrete_fairness_without_primitive_justice

/--
All assumptions of the conventional positive theorem coexist on one concrete
infinite RC11 execution.  The same execution has recurring successful CAS
events, arbitrarily late responses, and the full linearizable long-run
guarantee.
-/
theorem positiveAssumptionsJointlySatisfiable :
    ∃ candidate :
        MSQueue.Source.InfiniteRC11Execution Unit 1 0,
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
  MSQueue.Source.InfiniteWitness.successfulAssumptionsJointlySatisfiable

end WeakMemory.MSQueueResult
