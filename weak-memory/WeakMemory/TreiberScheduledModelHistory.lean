import WeakMemory.TreiberHistoryBridge
import WeakMemory.TreiberOrderFromSchedule

namespace WeakMemory.TreiberRC11

/-!
# Checked history theorem for scheduled relation models

`ScheduledRelationModelExecution` keeps one finite schedule that orders the
canonical relation graph.  Its conversion derives the common RC11 rank from
schedule positions.  This module connects that model-scoped package directly
to the executable client-order check and the Herlihy--Wing theorem.

The name deliberately says *model*: no theorem here claims that an external C
frontend has translated `c/treiber.c` into this package.
-/

namespace ScheduledRelationModelExecution

/--
A scheduled relation-model execution whose finite client-order check passes
has a classical Herlihy--Wing linearization.
-/
theorem herlihyWingLinearizable_of_checked_client_order
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : ScheduledRelationModelExecution initial)
    (clientOrderChecked :
      ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution.toSourceAtomicExecution
        execution.relationSchedule = true)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    HerlihyWing.Linearizable initialValues
      (sourceHistory execution.source.skeleton) :=
  execution.toSourceAtomicExecution
    |>.herlihyWingLinearizable_of_checked_schedule
      execution.scheduleRespectsGraph
      clientOrderChecked
      initialRepresentation

/--
The checked model theorem paired with the publication-safety result for every
source `readNext`.
-/
theorem herlihyWingLinearizable_and_nodeSafe_of_checked_client_order
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : ScheduledRelationModelExecution initial)
    (nextReadValues :
      NextReadValueCertificate execution.toSourceAtomicExecution)
    (clientOrderChecked :
      ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution.toSourceAtomicExecution
        execution.relationSchedule = true)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate
        execution.toSourceAtomicExecution.toControlledCandidate ∧
      HerlihyWing.Linearizable initialValues
        (sourceHistory execution.source.skeleton) :=
  execution.toSourceAtomicExecution
    |>.herlihyWingLinearizable_and_nodeSafe_of_checked_schedule
      nextReadValues
      execution.scheduleRespectsGraph
      clientOrderChecked
      initialRepresentation

end ScheduledRelationModelExecution

end WeakMemory.TreiberRC11
