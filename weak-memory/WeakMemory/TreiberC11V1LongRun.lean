import WeakMemory.TreiberC11V1InfiniteSafety
import WeakMemory.TreiberC11V1Progress

namespace WeakMemory.TreiberC11V1

/-!
# Unbounded responses and the safety/liveness bundle

One-step system response progress becomes ordinary unbounded lock-freedom when
some push or pop call is pending arbitrarily late.  This demand condition is
state-based: one call stuck forever satisfies it, so it does not presuppose
the responses that the theorem derives.  The same coherent execution already
supplies the complete finite-prefix linearizability theorem.
-/

namespace InfiniteRC11Execution

/--
At arbitrarily late states, some push or pop call is still pending.

In particular, a single forever-stuck call satisfies this predicate; it does
not require infinitely many fresh invocations.
-/
def RecurringPushPopDemand
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  Liveness.InfinitelyOften (fun time =>
    ∃ thread,
      PushPopActive
        (execution.source.state time thread))

/-- Source-level method responses occur arbitrarily late. -/
def InfinitelyManyResponses
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  Liveness.InfinitelyOften (fun time =>
    (execution.source.event time).IsResponse)

/--
Recurring pending push/pop demand plus system response progress yields
infinitely many method responses.
-/
theorem infinitelyManyResponses_of_systemResponseProgress
    (execution : InfiniteRC11Execution α threadCount)
    (recurring :
      execution.RecurringPushPopDemand)
    (progress :
      execution.SystemResponseProgress) :
    execution.InfinitelyManyResponses := by
  intro bound
  obtain ⟨activeTime, afterBound, thread, pending⟩ :=
    recurring bound
  obtain ⟨responseTime, afterActive, response⟩ :=
    progress activeTime
      ⟨thread, pending.active⟩
  exact
    ⟨responseTime,
      Nat.le_trans afterBound afterActive,
      response⟩

/--
Combined theorem object: complete safety for every finite prefix and
system-wide lock-freedom from every state containing an active operation.
-/
structure LinearizableLockFreeGuarantees
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount) : Prop where
  finitePrefixSafety :
    ∀ length,
      Nonempty
        (ExecutionFrontend.FullDeclarativeGuarantees
          (execution.declarativePrefix length))
  systemResponseProgress :
    execution.SystemResponseProgress

/--
The lock-freedom bundle plus its unbounded-response consequence under
recurring pending push/pop demand.
-/
structure LinearizableLongRunGuarantees
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount) : Prop where
  lockFreedom :
    execution.LinearizableLockFreeGuarantees
  infinitelyManyResponses :
    execution.InfinitelyManyResponses

/-- Assemble the combined safety/liveness guarantee. -/
theorem linearizableLockFree_of_systemResponseProgress
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (progress :
      execution.SystemResponseProgress) :
    execution.LinearizableLockFreeGuarantees where
  finitePrefixSafety :=
    execution.finitePrefix_fullyVerified
  systemResponseProgress :=
    progress

/-- Add the recurring-demand consequence to the core lock-freedom bundle. -/
theorem linearizableLongRun_of_systemResponseProgress
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (recurring :
      execution.RecurringPushPopDemand)
    (progress :
      execution.SystemResponseProgress) :
    execution.LinearizableLongRunGuarantees where
  lockFreedom :=
    execution.linearizableLockFree_of_systemResponseProgress
      progress
  infinitelyManyResponses :=
    execution.infinitelyManyResponses_of_systemResponseProgress
      recurring progress

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
