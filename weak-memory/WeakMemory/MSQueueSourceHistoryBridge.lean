import WeakMemory.MSQueueSourceUniversalReplay
import WeakMemory.MSQueueSourceHistoryWellFormed
import WeakMemory.MSQueueSourceCompletion
import WeakMemory.MSQueueSourceSameThreadRealTime

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Finite source-to-history linearizability bridge

The source machine supplies a well-formed client history and its standard
completion.  An atom schedule supplies the identity-preserving sequential
order and the canonical FIFO replay.  This module assembles those layers into
one Herlihy--Wing witness; cross-thread client real time is the only boundary
that is not internal to the checked source execution.
-/

namespace AtomSchedule

/-- Core assembly theorem, factored so the derived schedule-equivalence and
same-thread results can be supplied independently. -/
theorem linearizable_of_equivalent_and_thread_cases
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (equivalent :
      MSQueue.HW.Equivalent
        (Source.sourceCompletedOperations trace)
        schedule.scheduledOperations)
    (sameThread : SameThreadRealTimeCompatible schedule)
    (crossThread : CrossThreadRealTimeCompatible schedule) :
    MSQueue.HW.Linearizable [] (Source.sourceHistory trace) := by
  let certificate := schedule.canonicalCertificate
  refine ⟨{
    wellFormed := execution.sourceWellFormed.historyWellFormed
    completionOperations := Source.sourceCompletedOperations trace
    completion := execution.sourceWellFormed.sourceCompletion
    sequentialOperations := schedule.scheduledOperations
    equivalent := equivalent
    preservesRealTime :=
      preservesRealTime_of_thread_cases sameThread crossThread
    final := certificate.finalState.contents
    legal := ?_
  }⟩
  change QueueSpec.Legal []
    (MSQueue.HW.eraseIdentities schedule.scheduledOperations)
    certificate.finalState.contents
  have erasure := certificate.eraseIdentities_scheduledOperations
  change
    MSQueue.HW.eraseIdentities schedule.scheduledOperations =
      completedHistory certificate.commits at erasure
  rw [erasure]
  exact schedule.canonicalFIFO

/-- Once per-thread schedule equivalence is known, same-thread real time is
derived from source control flow; only the cross-thread boundary remains. -/
theorem linearizable_of_equivalent
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (equivalent :
      MSQueue.HW.Equivalent
        (Source.sourceCompletedOperations trace)
        schedule.scheduledOperations)
    (crossThread : CrossThreadRealTimeCompatible schedule) :
    MSQueue.HW.Linearizable [] (Source.sourceHistory trace) :=
  schedule.linearizable_of_equivalent_and_thread_cases equivalent
    (sameThreadRealTimeCompatible_of_equivalent schedule equivalent)
    crossThread

/-- Final finite bridge: an admitted atom schedule linearizes its exact source
history once the explicitly external cross-thread real-time edges are
compatible with that schedule. -/
theorem linearizable
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (crossThread : CrossThreadRealTimeCompatible schedule) :
    MSQueue.HW.Linearizable [] (Source.sourceHistory trace) :=
  schedule.linearizable_of_equivalent_and_thread_cases
    schedule.scheduleEquivalent
    schedule.sameThreadRealTimeCompatible
    crossThread

end AtomSchedule

/-- A packaged client-compatible schedule carries exactly the remaining
cross-thread premise needed by the finite bridge. -/
theorem ClientCompatibleSchedule.linearizable
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (compatible : ClientCompatibleSchedule execution) :
    MSQueue.HW.Linearizable [] (Source.sourceHistory trace) :=
  compatible.schedule.linearizable compatible.crossThreadRealTime

/-- Existential client-compatible scheduling is sufficient for finite
Herlihy--Wing linearizability. -/
theorem linearizable_of_hasClientCompatibleSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (available : HasClientCompatibleSchedule execution) :
    MSQueue.HW.Linearizable [] (Source.sourceHistory trace) := by
  rcases available with ⟨compatible⟩
  exact compatible.linearizable

end WeakMemory.MSQueue.Source.Structural
