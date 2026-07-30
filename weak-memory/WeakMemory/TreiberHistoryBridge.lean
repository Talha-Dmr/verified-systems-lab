import WeakMemory.TreiberArbitrarySchedule
import WeakMemory.TreiberClientCompatibilityCheck
import WeakMemory.TreiberRealTime
import WeakMemory.TreiberScheduleEquivalence
import WeakMemory.TreiberSameThreadRealTime
import WeakMemory.TreiberSourceCompletion
import WeakMemory.TreiberSourceHistoryWellFormed

namespace WeakMemory.TreiberRC11

/-!
# Source histories as Herlihy--Wing linearizations

This module joins the independently derived history obligations:

* the source client history is structurally well formed;
* source commits form its standard finite completion;
* every graph-respecting schedule is legal for the sequential stack;
* a respecting schedule preserves each client's commit order;
* client real time is preserved by splitting the derived same-thread case
  from the explicit cross-thread compatibility boundary.

The first theorem keeps the derived same-thread fact as a parameter so the
composition itself is independent of its proof.  The source-specific theorem
that supplies that fact is layered on top in `TreiberSameThreadRealTime`.
-/

namespace SourceAtomicExecution

/--
Construct the complete Herlihy--Wing witness on a fixed compatible graph
schedule.

The only client-side premise is cross-thread real-time compatibility, packaged
in `ClientCompatibleSchedule`.  Same-thread compatibility is a separate
argument here and is derived from source control flow by the next layer.
-/
theorem herlihyWingLinearizable_on_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (compatible :
      ClientCompatibleSchedule execution schedule)
    (sameThread :
      SameThreadRealTimeCompatible execution schedule)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    HerlihyWing.Linearizable initialValues
      (sourceHistory execution.source.skeleton) := by
  obtain ⟨final, finalValues, replayAccepted,
      finalRepresentation, legal⟩ :=
    execution.legal_on_respecting_schedule
      compatible.respectsGraph initialRepresentation
  refine ⟨{
    wellFormed :=
      execution.source.valid.historyWellFormed
    completionOperations :=
      sourceCommittedOperations execution.source.skeleton
    completion :=
      execution.source.valid.sourceCompletion
    sequentialOperations :=
      scheduledOperations execution schedule
    equivalent :=
      execution.scheduleEquivalent compatible.respectsGraph
    preservesRealTime :=
      (compatible.toFullyCompatible sameThread).preservesRealTime
    final :=
      finalValues
    legal := ?_
  }⟩
  change
    StackSpec.Legal initialValues
      (HerlihyWing.eraseIdentities
        (scheduledOperations execution schedule))
      finalValues
  rw [eraseIdentities_scheduledOperations
    execution compatible.respectsGraph]
  exact legal

/--
The same fixed-schedule bridge, paired with the independently derived safety
certificate for every modeled non-atomic `node->next` access.
-/
theorem herlihyWingLinearizable_and_nodeSafe_on_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (nextReadValues : NextReadValueCertificate execution)
    {schedule : List (Event α)}
    (compatible :
      ClientCompatibleSchedule execution schedule)
    (sameThread :
      SameThreadRealTimeCompatible execution schedule)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate execution.toControlledCandidate ∧
      HerlihyWing.Linearizable initialValues
        (sourceHistory execution.source.skeleton) :=
  ⟨execution.toNodeAccessCertificate nextReadValues,
    execution.herlihyWingLinearizable_on_schedule
      compatible sameThread initialRepresentation⟩

/--
Classical Herlihy--Wing linearizability on a fixed client-compatible schedule.
Same-thread real time is discharged from the source trace and graph program
order; only the cross-thread client condition remains in `compatible`.
-/
theorem herlihyWingLinearizable_on_client_compatible_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (compatible :
      ClientCompatibleSchedule execution schedule)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    HerlihyWing.Linearizable initialValues
      (sourceHistory execution.source.skeleton) :=
  execution.herlihyWingLinearizable_on_schedule
    compatible
    (execution.sameThreadRealTimeCompatible
      compatible.respectsGraph)
    initialRepresentation

/--
Existential client-compatible scheduling is the exact external condition
needed by the classical cross-thread real-time definition.
-/
theorem herlihyWingLinearizable
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (compatible :
      HasClientCompatibleSchedule execution)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    HerlihyWing.Linearizable initialValues
      (sourceHistory execution.source.skeleton) := by
  obtain ⟨schedule, scheduleCompatible⟩ := compatible
  exact
    execution.herlihyWingLinearizable_on_client_compatible_schedule
      scheduleCompatible initialRepresentation

/--
End-to-end classical linearizability and immutable-field access safety from
canonical source/relation data, finite client-compatible scheduling, and the
derived next-field value certificate.
-/
theorem herlihyWingLinearizable_and_nodeSafe
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (nextReadValues : NextReadValueCertificate execution)
    (compatible :
      HasClientCompatibleSchedule execution)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate execution.toControlledCandidate ∧
      HerlihyWing.Linearizable initialValues
        (sourceHistory execution.source.skeleton) :=
  ⟨execution.toNodeAccessCertificate nextReadValues,
    execution.herlihyWingLinearizable
      compatible initialRepresentation⟩

/--
Executable fixed-schedule entry point.  The finite Boolean client-order check
is sound for the only classical real-time condition not implied by RC11.
-/
theorem herlihyWingLinearizable_of_checked_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule)
    (clientOrderChecked :
      ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution schedule = true)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    HerlihyWing.Linearizable initialValues
      (sourceHistory execution.source.skeleton) :=
  execution.herlihyWingLinearizable_on_client_compatible_schedule
    {
      respectsGraph :=
        respects
      crossThreadRealTime :=
        ClientCompatibilityCheck.crossThreadRealTimeCompatible_sound
          clientOrderChecked
    }
    initialRepresentation

/--
Checked classical linearizability together with the derived non-atomic node
access certificate.
-/
theorem herlihyWingLinearizable_and_nodeSafe_of_checked_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (nextReadValues : NextReadValueCertificate execution)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule)
    (clientOrderChecked :
      ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution schedule = true)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate execution.toControlledCandidate ∧
      HerlihyWing.Linearizable initialValues
        (sourceHistory execution.source.skeleton) :=
  ⟨execution.toNodeAccessCertificate nextReadValues,
    execution.herlihyWingLinearizable_of_checked_schedule
      respects clientOrderChecked initialRepresentation⟩

end SourceAtomicExecution

end WeakMemory.TreiberRC11
