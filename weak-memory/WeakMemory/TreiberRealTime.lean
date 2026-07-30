import WeakMemory.TreiberArbitrarySchedule

namespace WeakMemory.TreiberRC11

/-!
# Client real-time compatibility

The atomic RC11 graph contains implementation events, program order, and
memory-model edges.  A Herlihy--Wing history additionally observes that one
method returned before another method was invoked.  For different client
threads this wall-clock edge is not, by itself, a C11 happens-before edge.

This module keeps that boundary explicit. Same-thread real-time compatibility
will be derived from source control flow and generated program order. Only the
cross-thread predicate is an external client/execution compatibility
condition.
-/

/-- Real-time edges whose endpoints belong to different client threads. -/
def CrossThreadRealTimeCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) : Prop :=
  ∀ {first second : HerlihyWing.IdentifiedCompleted α},
    first ∈ scheduledOperations execution schedule →
      second ∈ scheduledOperations execution schedule →
      first.thread ≠ second.thread →
      HerlihyWing.RealTimePrecedes
        (sourceHistory execution.source.skeleton)
        first second →
      HerlihyWing.Before first second
        (scheduledOperations execution schedule)

/-- Real-time edges whose endpoints belong to one client thread. -/
def SameThreadRealTimeCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) : Prop :=
  ∀ {first second : HerlihyWing.IdentifiedCompleted α},
    first ∈ scheduledOperations execution schedule →
      second ∈ scheduledOperations execution schedule →
      first.thread = second.thread →
      HerlihyWing.RealTimePrecedes
        (sourceHistory execution.source.skeleton)
        first second →
      HerlihyWing.Before first second
        (scheduledOperations execution schedule)

/-- Same-thread and cross-thread cases cover classical real-time preservation. -/
theorem preservesRealTime_of_thread_cases
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    {schedule : List (Event α)}
    (sameThread :
      SameThreadRealTimeCompatible execution schedule)
    (crossThread :
      CrossThreadRealTimeCompatible execution schedule) :
    HerlihyWing.PreservesRealTime
      (sourceHistory execution.source.skeleton)
      (scheduledOperations execution schedule) := by
  intro first second firstMember secondMember realTime
  by_cases sameOwner : first.thread = second.thread
  · exact sameThread
      firstMember secondMember sameOwner realTime
  · exact crossThread
      firstMember secondMember sameOwner realTime

/--
A schedule suitable for the classical Herlihy--Wing witness.

`respectsGraph` is the implementation/memory-model obligation.
`crossThreadRealTime` is the separate client-order obligation.
-/
structure ClientCompatibleSchedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) : Prop where
  respectsGraph :
    RespectsGraph execution.relations.graph schedule
  crossThreadRealTime :
    CrossThreadRealTimeCompatible execution schedule

/-- A respecting schedule with every classical real-time edge discharged. -/
structure FullyRealTimeCompatibleSchedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) : Prop where
  respectsGraph :
    RespectsGraph execution.relations.graph schedule
  preservesRealTime :
    HerlihyWing.PreservesRealTime
      (sourceHistory execution.source.skeleton)
      (scheduledOperations execution schedule)

/-- Derived same-thread order upgrades the cross-thread client condition. -/
theorem ClientCompatibleSchedule.toFullyCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    {schedule : List (Event α)}
    (compatible :
      ClientCompatibleSchedule execution schedule)
    (sameThread :
      SameThreadRealTimeCompatible execution schedule) :
    FullyRealTimeCompatibleSchedule execution schedule where
  respectsGraph :=
    compatible.respectsGraph
  preservesRealTime :=
    preservesRealTime_of_thread_cases
      sameThread compatible.crossThreadRealTime

/-- Existence of one graph schedule compatible with the observed client time. -/
def HasClientCompatibleSchedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) : Prop :=
  ∃ schedule,
    ClientCompatibleSchedule execution schedule

end WeakMemory.TreiberRC11
