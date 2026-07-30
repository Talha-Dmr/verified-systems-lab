import WeakMemory.TreiberScheduledHistory

namespace WeakMemory.TreiberRC11

/-!
# Replaying any respecting canonical source schedule

The existing end-to-end construction chooses one topological schedule.  The
Herlihy--Wing bridge must instead be able to choose a schedule that also
respects the client's admissible real-time edges.  This module proves that no
extra replay assumption is needed: every schedule that covers the canonical
graph and respects program order plus extended coherence is accepted by the
same typed Treiber invariant.
-/

namespace SourceAtomicExecution

/--
Any respecting schedule of a canonical source execution replays successfully
and produces the already proved legal anonymous stack history.
-/
theorem legal_on_respecting_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    ∃ final finalValues,
      replay? initial schedule = some final ∧
        TreiberRA.Represents
          final.heap final.head finalValues ∧
        StackSpec.Legal initialValues
          (Treiber.completedHistory
            (TreiberRA.commits
              (projectedActions schedule)))
          finalValues := by
  let final :=
    advanceUncheckedList initial schedule
  have replayAccepted :
      replay? initial schedule = some final :=
    replay?_eq_some_advanceUncheckedList
      execution.toCoreConsistent.toWellFormed
      respects
      execution.toGraphTyping.toReplayInvariant
  have contained :
      ∀ event,
        event ∈ schedule →
          event ∈ execution.relations.graph.events := by
    intro event member
    exact (respects.covers event).mpr member
  let certificate :
      CertifiedSchedule
        execution.relations.graph initial schedule final := {
    consistent :=
      execution.toCoreConsistent
    respectsGraph :=
      respects
    executes :=
      replay?_sound
        execution.relations.graph contained replayAccepted
  }
  obtain ⟨finalValues, finalRepresentation, legal⟩ :=
    certifiedSchedule_linearizable
      certificate initialRepresentation
  exact ⟨final, finalValues, replayAccepted,
    finalRepresentation, legal⟩

end SourceAtomicExecution

end WeakMemory.TreiberRC11
