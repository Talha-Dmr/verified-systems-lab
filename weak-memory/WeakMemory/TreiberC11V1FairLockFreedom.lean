import WeakMemory.TreiberC11V1LongRun
import WeakMemory.TreiberC11V1MatchingProgress
import WeakMemory.TreiberC11V1StableTail

namespace WeakMemory.TreiberC11V1

/-!
# Fair RC11 lock-freedom for reclamation-free Treiber

This is the final liveness assembly:

* weak thread fairness reaches retry boundaries and discharges post-commit
  local work;
* prefix-finite `fr` eventually exposes the stable modification-order tail;
* the source retry path turns a stable observation into compare-equal attempts;
* primitive weak-CAS justice excludes an all-spurious stable suffix; and
* recurring pending push/pop demand turns one-step system progress into
  infinitely many responses without presupposing fresh invocations.

Every finite prefix simultaneously receives the repository's existing full
RC11 safety and Herlihy--Wing linearizability bundle.
-/

namespace InfiniteRC11Execution

/-- Thread fairness and prefix-finite `fr` establish stable RF-source visibility. -/
theorem stableSourceProgress_of_fromReadFair
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair) :
    execution.StableSourceProgress := by
  intro query start activeAtStart noResponse
  have noSuccess :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsSuccessfulCAS :=
    execution.source
      |>.no_successfulCAS_on_response_free_suffix
        threadFair start noResponse
  let selected : Nat → Prop :=
    fun time =>
      start ≤ time ∧
        (execution.source.event time).thread = query ∧
        (execution.source.event time).IsCASAttempt
  have eventuallyStable :=
    execution.eventually_selected_observes_prefixTail_of_fromReadFair
      fromReadFair start noSuccess selected
      (fun time chosen => chosen.1)
      (fun time chosen =>
        TraceEvent.exists_atomic_of_CASAttempt
          chosen.2.2)
  obtain ⟨visibleStart, visible⟩ :=
    eventuallyStable
  refine
    ⟨(execution.prefixTail start).atom.id,
      max start visibleStart,
      ?_⟩
  intro time afterMaximum cas
  exact
    visible time
      (Nat.le_trans
        (Nat.le_max_right start visibleStart)
        afterMaximum)
      ⟨Nat.le_trans
          (Nat.le_max_left start visibleStart)
          afterMaximum,
        cas⟩

/-- Standard paired memory fairness supplies the exact `fr` premise. -/
theorem stableSourceProgress_of_memoryFair
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair) :
    execution.StableSourceProgress :=
  execution.stableSourceProgress_of_fromReadFair
    threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)

/--
Weak thread fairness, prefix-finite `fr`, and primitive weak-CAS justice give
system-wide method response progress.
-/
theorem systemResponseProgress_of_fromReadFairness
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_stableSourceProgress
    threadFair
    (execution.stableSourceProgress_of_fromReadFair
      threadFair fromReadFair)
    justice

/--
Conventional paired RC11 memory fairness gives the `fr`-only progress theorem.
-/
theorem systemResponseProgress_of_fairness
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_fromReadFairness
    threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

/--
The exact-assumption safety/liveness bundle: prefix-finite `fr` is sufficient
for the current Treiber proof.
-/
theorem linearizableLockFree_of_fromReadFairness
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_systemResponseProgress
    (execution.systemResponseProgress_of_fromReadFairness
      threadFair fromReadFair justice)

/--
Final combined theorem for the current model: all finite prefixes are fully
verified and every state with an active operation has a later response.
-/
theorem linearizableLockFree_of_fairness
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLockFreeGuarantees :=
  execution.linearizableLockFree_of_fromReadFairness
    threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

/--
Under recurring pending demand, the exact `fr`-only theorem has responses
arbitrarily late.
-/
theorem linearizableLongRun_of_fromReadFairness
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (recurring :
      execution.RecurringPushPopDemand)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_systemResponseProgress
    recurring
    (execution.systemResponseProgress_of_fromReadFairness
      threadFair fromReadFair justice)

/--
Under recurring pending push/pop demand, the same fair execution has method
responses arbitrarily late.
-/
theorem linearizableLongRun_of_fairness
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (recurring :
      execution.RecurringPushPopDemand)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair)
    (justice : execution.WeakCASJustice) :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fromReadFairness
    recurring
    threadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    justice

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
