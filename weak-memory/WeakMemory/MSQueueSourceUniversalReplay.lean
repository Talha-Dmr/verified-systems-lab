import WeakMemory.MSQueueSourceReplay
import WeakMemory.MSQueueSourceEmptyPrefixReadiness
import WeakMemory.MSQueueSourceTailPrefixReadiness
import WeakMemory.MSQueueSourceHeadTailGap

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Universal source-backed queue replay

The four source action shapes now have exact-prefix readiness proofs.  This
module closes the dispatcher consumed by atom-prefix induction and exposes
the resulting canonical replay, certificate, and FIFO history theorem without
an independently supplied structural replay.
-/

namespace AtomSchedule

/-- Every extracted structural record is ready at its exact atom-schedule
prefix.  Replay evidence for that prefix is needed only by the successful
Head case, where it preserves the historical Head/Tail gap. -/
theorem recordReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    RecordReady schedule := by
  intro focus focusMember represented replayed
  rcases structuralRecord_shape focusMember with
      ⟨owner, child, payload, actionShape, _pointSite, _written⟩ |
      ⟨expected, desired, actionShape, _pointSite, _written⟩ |
      ⟨expected, desired, dequeued, actionShape, _pointSite, _written⟩ |
      ⟨head, actionShape, _pointSite, _written⟩
  · exact schedule.linkBeforeAppliesAndPreserves
      focusMember actionShape represented
  · exact schedule.advanceTailBeforeAppliesAndPreserves
      focusMember actionShape represented
  · exact schedule.advanceHeadBeforeAppliesAndPreservesExact
      focusMember actionShape represented replayed
  · exact schedule.emptyBeforeAppliesAndPreserves
      focusMember actionShape represented

/-- Every admitted atom schedule has the canonical structural replay induced
by its record anchors. -/
theorem canonicalReplay
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    Prefix.Rep dummy (recordsOn trace schedule.atoms) ∧
      Replay (Chain.State.initial dummy)
        (recordsOn trace schedule.atoms)
        (Prefix.stateOf dummy (recordsOn trace schedule.atoms)) :=
  schedule.replay_of_ready schedule.recordReady

/-- The schedule therefore determines an exact source certificate; no replay
or final state is supplied by an external oracle. -/
def canonicalCertificate
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) : Certificate execution :=
  schedule.certificateOfReady schedule.recordReady

/-- Completed commits of every admitted source-backed schedule are legal for
the abstract FIFO queue and end in the canonical final contents. -/
theorem canonicalFIFO
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    QueueSpec.Legal []
      (completedHistory schedule.canonicalCertificate.commits)
      schedule.canonicalCertificate.finalState.contents := by
  simpa [canonicalCertificate] using
    schedule.fifoLegal_of_ready schedule.recordReady

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
