import WeakMemory.TreiberC11V1InfiniteWitnessFairness
import WeakMemory.TreiberC11V1InfiniteSpuriousFairness
import WeakMemory.WeakCASCounter

namespace WeakMemory.WeakCASTreiberResult

/-!
# Public theorem surface for fair weak CAS and Treiber

This module collects the result's independent pieces without adding a new
semantic layer:

* the generic and integrated Treiber all-spurious separation theorems;
* the Treiber-independent counter client of the generic progress rule;
* the exact `fr`-fair Treiber response-progress theorem;
* the conventional paired-memory-fairness corollary; and
* one concrete execution witnessing joint satisfiability of the positive
  assumptions.

The integrated negative witness uses the same `TreiberC11V1` justice and
system-response predicates as the positive theorem.  The smaller generic
one-location witness remains available as an algorithm-independent sanity
check.
-/

/--
Weak thread fairness and declarative memory fairness do not imply primitive
weak-CAS justice or primitive system progress in the generic one-location
machine.
-/
theorem genericAllSpuriousSeparation :
    ∃ candidate : WeakCAS.Run Nat 1,
      WeakCAS.WeakThreadFair candidate ∧
        WeakCAS.MemoryFair candidate ∧
        ¬ WeakCAS.WeakCASJustice candidate ∧
        ¬ WeakCAS.SystemProgress candidate :=
  WeakCAS.AllSpurious.threadFair_memoryFair_do_not_imply_progress

/--
Integrated negative theorem: a coherent `TreiberC11V1` execution can satisfy
weak thread fairness, full prefix-finite `mo`/`fr` memory fairness, and
recurring pending push demand while violating both Treiber weak-CAS justice
and system response progress.
-/
theorem treiberAllSpuriousSeparation :
    ∃ candidate :
        TreiberC11V1.InfiniteRC11Execution Unit 1,
      candidate.source.WeakThreadFair ∧
        candidate.MemoryFair ∧
        candidate.RecurringPushPopDemand ∧
        ¬ candidate.WeakCASJustice ∧
        ¬ candidate.SystemResponseProgress :=
  TreiberC11V1.InfiniteSpurious.threadFair_memoryFair_do_not_imply_progress

/--
The generic single-site primitive-justice rule has a second,
Treiber-independent client.
-/
theorem counterResponseProgress
    (run : WeakCASCounter.Run)
    (justice :
      WeakCAS.ProgressRule.PrimitiveJustice
        (WeakCASCounter.interface run)) :
    WeakCAS.ProgressRule.SystemResponseProgress
      (WeakCASCounter.interface run) :=
  WeakCASCounter.responseProgress_of_primitiveJustice
    run justice

/--
Exact Treiber progress theorem: weak thread fairness, prefix-finite `fr`, and
primitive weak-CAS justice imply system-wide method response progress.
-/
theorem treiberSystemResponseProgress_of_fromReadFairness
    (execution :
      TreiberC11V1.InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_fromReadFairness
    threadFair fromReadFair justice

/--
Conventional formulation using the standard paired prefix-finite `mo`/`fr`
memory-fairness contract.
-/
theorem treiberSystemResponseProgress_of_memoryFairness
    (execution :
      TreiberC11V1.InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_fairness
    threadFair memoryFair justice

/--
Finite-prefix safety and system lock-freedom, plus arbitrarily late responses
under recurring pending push/pop demand, using the exact `fr` premise.
-/
theorem treiberLinearizableLongRun_of_fromReadFairness
    [DecidableEq α]
    (execution :
      TreiberC11V1.InfiniteRC11Execution α threadCount)
    (recurring : execution.RecurringPushPopDemand)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fromReadFairness
    recurring threadFair fromReadFair justice

/--
All assumptions of the conventional positive theorem are jointly satisfiable
on one concrete infinite RC11 execution, and the theorem applies to it.
-/
theorem positiveAssumptionsJointlySatisfiable :
    ∃ execution :
        TreiberC11V1.InfiniteRC11Execution Unit 1,
      execution.RecurringPushPopDemand ∧
        execution.source.WeakThreadFair ∧
        execution.MemoryFair ∧
        execution.WeakCASJustice ∧
        execution.LinearizableLongRunGuarantees := by
  exact
    ⟨TreiberC11V1.InfiniteWitness.execution,
      TreiberC11V1.InfiniteWitness.execution_recurringPushPopDemand,
      TreiberC11V1.InfiniteWitness.execution_threadFair,
      TreiberC11V1.InfiniteWitness.execution_memoryFair,
      TreiberC11V1.InfiniteWitness.execution_weakCASJustice,
      TreiberC11V1.InfiniteWitness.execution_linearizableLongRun⟩

end WeakMemory.WeakCASTreiberResult
