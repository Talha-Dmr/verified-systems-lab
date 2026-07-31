import WeakMemory.MSQueueSourceHistory

namespace WeakMemory.MSQueue.Source

/-!
# Client real-time compatibility for the Michael--Scott queue

The RC11 execution orders implementation atoms.  A classical Herlihy--Wing
history additionally records when one method response was observed before a
later invocation.  For different client threads that wall-clock edge is not,
by itself, an RC11 happens-before edge, so the boundary remains explicit.

The same-thread half will be derived from the checked source machine and
program order in a later module.  This file isolates the definitions and the
small composition theorem that combines the two thread cases.
-/

namespace Structural

/-- Real-time edges whose endpoints belong to different client threads. -/
def CrossThreadRealTimeCompatible
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) : Prop :=
  ∀ {first second : MSQueue.HW.IdentifiedCompleted Value},
    first ∈ schedule.scheduledOperations →
      second ∈ schedule.scheduledOperations →
      first.thread ≠ second.thread →
      MSQueue.HW.RealTimePrecedes
        (Source.sourceHistory trace) first second →
      HerlihyWing.Before first second schedule.scheduledOperations

/-- Real-time edges whose endpoints belong to one client thread. -/
def SameThreadRealTimeCompatible
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) : Prop :=
  ∀ {first second : MSQueue.HW.IdentifiedCompleted Value},
    first ∈ schedule.scheduledOperations →
      second ∈ schedule.scheduledOperations →
      first.thread = second.thread →
      MSQueue.HW.RealTimePrecedes
        (Source.sourceHistory trace) first second →
      HerlihyWing.Before first second schedule.scheduledOperations

/-- Same-thread and cross-thread cases cover every classical real-time edge. -/
theorem preservesRealTime_of_thread_cases
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {schedule : AtomSchedule execution}
    (sameThread : SameThreadRealTimeCompatible schedule)
    (crossThread : CrossThreadRealTimeCompatible schedule) :
    MSQueue.HW.PreservesRealTime
      (Source.sourceHistory trace) schedule.scheduledOperations := by
  intro first second firstMember secondMember realTime
  by_cases sameOwner : first.thread = second.thread
  · exact sameThread firstMember secondMember sameOwner realTime
  · exact crossThread firstMember secondMember sameOwner realTime

/--
A structural schedule suitable for a classical Herlihy--Wing witness.

The atom schedule already packages the RC11 program-order and coherence
obligations.  Only cross-thread client real time remains as an explicit
compatibility boundary.
-/
structure ClientCompatibleSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) where
  schedule : AtomSchedule execution
  crossThreadRealTime : CrossThreadRealTimeCompatible schedule

/-- A fixed atom schedule with all classical real-time edges discharged. -/
structure FullyRealTimeCompatibleSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) where
  schedule : AtomSchedule execution
  preservesRealTime :
    MSQueue.HW.PreservesRealTime
      (Source.sourceHistory trace) schedule.scheduledOperations

/-- Derived same-thread order upgrades the cross-thread client condition. -/
def ClientCompatibleSchedule.toFullyCompatible
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (compatible : ClientCompatibleSchedule execution)
    (sameThread :
      SameThreadRealTimeCompatible compatible.schedule) :
    FullyRealTimeCompatibleSchedule execution where
  schedule := compatible.schedule
  preservesRealTime :=
    preservesRealTime_of_thread_cases
      sameThread compatible.crossThreadRealTime

/-- Existence of one structural schedule compatible with observed client time. -/
def HasClientCompatibleSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) : Prop :=
  Nonempty (ClientCompatibleSchedule execution)

end Structural

end WeakMemory.MSQueue.Source
