import WeakMemory.MSQueueSourceRealTime
import WeakMemory.MSQueueSourceCompletion
import WeakMemory.MSQueueSourceScheduleEquivalence

namespace WeakMemory.MSQueue.Source

/-!
# Derived same-thread real-time compatibility

Source completion orders one thread's selected commits by invocation order.
If one completed operation returns before another is invoked, source-history
well-formedness places the first invocation before that return, hence before
the second invocation.  Schedule equivalence then transports the resulting
commit order to the structural atom schedule.
-/

namespace SameThreadRealTime

/-- An inductive presentation of strict order in a list. -/
private inductive ListPrecedes
    (first second : β) :
    List β → Prop where
  | head {rest : List β} :
      second ∈ rest →
      ListPrecedes first second (first :: rest)
  | tail {item : β} {rest : List β} :
      ListPrecedes first second rest →
      ListPrecedes first second (item :: rest)

namespace ListPrecedes

private theorem second_mem
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    second ∈ items := by
  induction precedes with
  | head member =>
      exact List.mem_cons_of_mem _ member
  | tail _ inductionHypothesis =>
      exact List.mem_cons_of_mem _ inductionHypothesis

private theorem ofBefore
    {first second : β}
    {items : List β}
    (before : HerlihyWing.Before first second items) :
    ListPrecedes first second items := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  induction earlier with
  | nil =>
      apply ListPrecedes.head
      simp
  | cons item rest inductionHypothesis =>
      exact ListPrecedes.tail inductionHypothesis

private theorem toBefore
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    HerlihyWing.Before first second items := by
  induction precedes with
  | @head rest member =>
      obtain ⟨between, later, shape⟩ :=
        List.append_of_mem member
      exact ⟨[], between, later, by simp [shape]⟩
  | @tail item rest later inductionHypothesis =>
      obtain ⟨earlier, between, trailing, shape⟩ :=
        inductionHypothesis
      exact ⟨item :: earlier, between, trailing, by
        simp [shape]⟩

/-- Strict list order is transitive in a duplicate-free list. -/
private theorem trans
    {first middle last : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (firstBeforeMiddle :
      ListPrecedes first middle items)
    (middleBeforeLast :
      ListPrecedes middle last items) :
    ListPrecedes first last items := by
  induction firstBeforeMiddle with
  | @head rest middleMember =>
      cases middleBeforeLast with
      | head lastMember =>
          exact ListPrecedes.head lastMember
      | tail later =>
          exact ListPrecedes.head later.second_mem
  | @tail item rest earlier inductionHypothesis =>
      cases middleBeforeLast with
      | head lastMember =>
          exact
            ((List.nodup_cons.mp noDuplicates).1
              earlier.second_mem).elim
      | tail later =>
          exact ListPrecedes.tail
            (inductionHypothesis
              (List.nodup_cons.mp noDuplicates).2 later)

end ListPrecedes

/-- Decomposition-based strict order is transitive on a duplicate-free list. -/
private theorem before_trans
    {first middle last : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (firstBeforeMiddle :
      HerlihyWing.Before first middle items)
    (middleBeforeLast :
      HerlihyWing.Before middle last items) :
    HerlihyWing.Before first last items :=
  (ListPrecedes.ofBefore firstBeforeMiddle
    |>.trans noDuplicates
      (ListPrecedes.ofBefore middleBeforeLast)).toBefore

/--
Distinct invocation and return identifiers make the complete client-event
list duplicate-free.
-/
private theorem history_nodup_of_id_nodup
    {history : MSQueue.HW.History Value}
    (invocations :
      (MSQueue.HW.invocationIds history).Nodup)
    (returns :
      (MSQueue.HW.returnIds history).Nodup) :
    history.Nodup := by
  induction history with
  | nil =>
      exact List.nodup_nil
  | cons event rest inductionHypothesis =>
      cases event with
      | invoke invocation =>
          have invocationSplit :
              invocation.id ∉
                  MSQueue.HW.invocationIds rest ∧
                (MSQueue.HW.invocationIds rest).Nodup := by
            simpa [MSQueue.HW.invocationIds,
              MSQueue.HW.HistoryEvent.invocationId?] using
              invocations
          have returnTail :
              (MSQueue.HW.returnIds rest).Nodup := by
            simpa [MSQueue.HW.returnIds,
              MSQueue.HW.HistoryEvent.returnId?] using
              returns
          apply List.nodup_cons.mpr
          constructor
          · intro member
            apply invocationSplit.1
            exact List.mem_filterMap.mpr
              ⟨.invoke invocation, member, rfl⟩
          · exact inductionHypothesis
              invocationSplit.2 returnTail
      | respond returned =>
          have returnSplit :
              returned.id ∉ MSQueue.HW.returnIds rest ∧
                (MSQueue.HW.returnIds rest).Nodup := by
            simpa [MSQueue.HW.returnIds,
              MSQueue.HW.HistoryEvent.returnId?] using
              returns
          have invocationTail :
              (MSQueue.HW.invocationIds rest).Nodup := by
            simpa [MSQueue.HW.invocationIds,
              MSQueue.HW.HistoryEvent.invocationId?] using
              invocations
          apply List.nodup_cons.mpr
          constructor
          · intro member
            apply returnSplit.1
            exact List.mem_filterMap.mpr
              ⟨.respond returned, member, rfl⟩
          · exact inductionHypothesis
              invocationTail returnSplit.2

/-- Completed-operation thread projection distributes over concatenation. -/
private theorem operationsForThread_append
    (thread : ThreadId)
    (first second :
      List (MSQueue.HW.IdentifiedCompleted Value)) :
    MSQueue.HW.operationsForThread thread (first ++ second) =
      MSQueue.HW.operationsForThread thread first ++
        MSQueue.HW.operationsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.cons_append,
        MSQueue.HW.operationsForThread]
      split <;> simp [inductionHypothesis]

/-- Same-thread endpoints retain their order after thread projection. -/
private theorem before_operationsForThread
    {thread : ThreadId}
    {first second : MSQueue.HW.IdentifiedCompleted Value}
    {operations :
      List (MSQueue.HW.IdentifiedCompleted Value)}
    (before : HerlihyWing.Before first second operations)
    (firstThread : first.thread = thread)
    (secondThread : second.thread = thread) :
    HerlihyWing.Before first second
      (MSQueue.HW.operationsForThread thread operations) := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst operations
  refine ⟨
    MSQueue.HW.operationsForThread thread earlier,
    MSQueue.HW.operationsForThread thread between,
    MSQueue.HW.operationsForThread thread later,
    ?_⟩
  simp [operationsForThread_append,
    MSQueue.HW.operationsForThread,
    firstThread, secondThread]

/-- A completed-operation thread projection is a sublist of the source list. -/
private theorem operationsForThread_sublist
    (thread : ThreadId)
    (operations :
      List (MSQueue.HW.IdentifiedCompleted Value)) :
    List.Sublist
      (MSQueue.HW.operationsForThread thread operations)
      operations := by
  induction operations with
  | nil =>
      exact .slnil
  | cons entry rest inductionHypothesis =>
      by_cases sameThread : entry.thread = thread
      · simp only [MSQueue.HW.operationsForThread,
          sameThread, ↓reduceIte]
        exact inductionHypothesis.cons_cons entry
      · simp only [MSQueue.HW.operationsForThread,
          sameThread, ↓reduceIte]
        exact inductionHypothesis.cons entry

/-- Order in a completed-operation thread projection lifts to the full list. -/
private theorem before_of_operationsForThread
    {thread : ThreadId}
    {first second : MSQueue.HW.IdentifiedCompleted Value}
    {operations :
      List (MSQueue.HW.IdentifiedCompleted Value)}
    (before :
      HerlihyWing.Before first second
        (MSQueue.HW.operationsForThread thread operations)) :
    HerlihyWing.Before first second operations := by
  rw [HistoryWellFormed.before_iff_pair_sublist] at before ⊢
  exact before.trans
    (operationsForThread_sublist thread operations)

end SameThreadRealTime


namespace Structural

/--
Per-thread equivalence with the source commit list is sufficient to transport
every same-thread client real-time edge to an atom schedule.

This theorem isolates the history argument from the construction of schedule
equivalence.  In particular, it needs no RC11 assumption beyond the
`SupportedExecution` already indexed by the schedule.
-/
theorem sameThreadRealTimeCompatible_of_equivalent
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (equivalent :
      MSQueue.HW.Equivalent
        (Source.sourceCompletedOperations trace)
        schedule.scheduledOperations) :
    SameThreadRealTimeCompatible schedule := by
  intro first second firstScheduled secondScheduled
    sameThread realTime
  have firstSource :
      first ∈ Source.sourceCompletedOperations trace :=
    equivalent.1.mem_iff.mpr firstScheduled
  have secondSource :
      second ∈ Source.sourceCompletedOperations trace :=
    equivalent.1.mem_iff.mpr secondScheduled
  let completion :=
    execution.sourceWellFormed.sourceCompletion
  have firstPresent :
      first.Present (Source.sourceHistory trace) := by
    rcases (completion.selected firstSource).2 with
        present | pending
    · exact present
    · exfalso
      apply pending.no_matching_return
        (returned := first.returned)
        ⟨rfl, rfl⟩
      exact realTime.first_mem
  have sourceWellFormed :
      MSQueue.HW.WellFormed (Source.sourceHistory trace) :=
    execution.sourceWellFormed.historyWellFormed
  have historyNodup :
      (Source.sourceHistory trace).Nodup :=
    SameThreadRealTime.history_nodup_of_id_nodup
      sourceWellFormed.invocationIdsNodup
      sourceWellFormed.returnIdsNodup
  have invocationOrder :
      HerlihyWing.Before
        (.invoke first.invocation)
        (.invoke second.invocation)
        (Source.sourceHistory trace) :=
    SameThreadRealTime.before_trans
      historyNodup firstPresent realTime
  have sourceCommitOrder :
      HerlihyWing.Before first second
        (Source.sourceCompletedOperations trace) :=
    completion.threadOrder
      firstSource secondSource sameThread invocationOrder
  have sourceThreadOrder :
      HerlihyWing.Before first second
        (MSQueue.HW.operationsForThread first.thread
          (Source.sourceCompletedOperations trace)) :=
    SameThreadRealTime.before_operationsForThread
      sourceCommitOrder rfl sameThread.symm
  have scheduledThreadOrder :
      HerlihyWing.Before first second
        (MSQueue.HW.operationsForThread first.thread
          schedule.scheduledOperations) := by
    rw [← equivalent.2 first.thread]
    exact sourceThreadOrder
  exact
    SameThreadRealTime.before_of_operationsForThread
      scheduledThreadOrder

namespace AtomSchedule

/--
Every structural atom schedule automatically preserves client real-time order
between operations owned by the same source thread.
-/
theorem sameThreadRealTimeCompatible
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    SameThreadRealTimeCompatible schedule :=
  sameThreadRealTimeCompatible_of_equivalent
    schedule schedule.scheduleEquivalent

end AtomSchedule

end Structural

end WeakMemory.MSQueue.Source
