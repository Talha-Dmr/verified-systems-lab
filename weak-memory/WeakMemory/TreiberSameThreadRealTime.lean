import WeakMemory.TreiberRealTime
import WeakMemory.TreiberScheduleEquivalence
import WeakMemory.TreiberSourceCompletion
import WeakMemory.TreiberSourceHistoryWellFormed

namespace WeakMemory.TreiberRC11

/-!
# Derived same-thread real-time compatibility

Source completion orders one thread's selected commits by invocation order.
If one completed operation returns before another is invoked, source-history
well-formedness places the first invocation before that return, hence before
the second invocation.  Schedule equivalence then transports the resulting
commit order to every respecting graph schedule.
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
    {history : HerlihyWing.History α}
    (invocations :
      (HerlihyWing.invocationIds history).Nodup)
    (returns :
      (HerlihyWing.returnIds history).Nodup) :
    history.Nodup := by
  induction history with
  | nil =>
      exact List.nodup_nil
  | cons event rest inductionHypothesis =>
      cases event with
      | invoke invocation =>
          have invocationSplit :
              invocation.id ∉
                  HerlihyWing.invocationIds rest ∧
                (HerlihyWing.invocationIds rest).Nodup := by
            simpa [HerlihyWing.invocationIds,
              HerlihyWing.HistoryEvent.invocationId?] using
              invocations
          have returnTail :
              (HerlihyWing.returnIds rest).Nodup := by
            simpa [HerlihyWing.returnIds,
              HerlihyWing.HistoryEvent.returnId?] using
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
              returned.id ∉ HerlihyWing.returnIds rest ∧
                (HerlihyWing.returnIds rest).Nodup := by
            simpa [HerlihyWing.returnIds,
              HerlihyWing.HistoryEvent.returnId?] using
              returns
          have invocationTail :
              (HerlihyWing.invocationIds rest).Nodup := by
            simpa [HerlihyWing.invocationIds,
              HerlihyWing.HistoryEvent.invocationId?] using
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
    (thread : Nat)
    (first second :
      List (HerlihyWing.IdentifiedCompleted α)) :
    HerlihyWing.operationsForThread thread (first ++ second) =
      HerlihyWing.operationsForThread thread first ++
        HerlihyWing.operationsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.cons_append,
        HerlihyWing.operationsForThread]
      split <;> simp [inductionHypothesis]

/-- Same-thread endpoints retain their order after thread projection. -/
private theorem before_operationsForThread
    {thread : Nat}
    {first second : HerlihyWing.IdentifiedCompleted α}
    {operations :
      List (HerlihyWing.IdentifiedCompleted α)}
    (before : HerlihyWing.Before first second operations)
    (firstThread : first.thread = thread)
    (secondThread : second.thread = thread) :
    HerlihyWing.Before first second
      (HerlihyWing.operationsForThread thread operations) := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst operations
  refine ⟨
    HerlihyWing.operationsForThread thread earlier,
    HerlihyWing.operationsForThread thread between,
    HerlihyWing.operationsForThread thread later,
    ?_⟩
  simp [operationsForThread_append,
    HerlihyWing.operationsForThread,
    firstThread, secondThread]

/-- A completed-operation thread projection is a sublist of the source list. -/
private theorem operationsForThread_sublist
    (thread : Nat)
    (operations :
      List (HerlihyWing.IdentifiedCompleted α)) :
    List.Sublist
      (HerlihyWing.operationsForThread thread operations)
      operations := by
  induction operations with
  | nil =>
      exact .slnil
  | cons entry rest inductionHypothesis =>
      by_cases sameThread : entry.thread = thread
      · simp only [HerlihyWing.operationsForThread,
          sameThread, ↓reduceIte]
        exact inductionHypothesis.cons_cons entry
      · simp only [HerlihyWing.operationsForThread,
          sameThread, ↓reduceIte]
        exact inductionHypothesis.cons entry

/-- Order in a completed-operation thread projection lifts to the full list. -/
private theorem before_of_operationsForThread
    {thread : Nat}
    {first second : HerlihyWing.IdentifiedCompleted α}
    {operations :
      List (HerlihyWing.IdentifiedCompleted α)}
    (before :
      HerlihyWing.Before first second
        (HerlihyWing.operationsForThread thread operations)) :
    HerlihyWing.Before first second operations := by
  rw [HerlihyWing.Before.iff_pair_sublist] at before ⊢
  exact before.trans
    (operationsForThread_sublist thread operations)

end SameThreadRealTime

namespace SourceAtomicExecution

/--
Every respecting graph schedule automatically preserves real-time edges
between operations of the same client thread.
-/
theorem sameThreadRealTimeCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule) :
    SameThreadRealTimeCompatible execution schedule := by
  intro first second firstScheduled secondScheduled
    sameThread realTime
  let equivalent := execution.scheduleEquivalent respects
  have firstSource :
      first ∈
        sourceCommittedOperations execution.source.skeleton :=
    equivalent.1.mem_iff.mpr firstScheduled
  have secondSource :
      second ∈
        sourceCommittedOperations execution.source.skeleton :=
    equivalent.1.mem_iff.mpr secondScheduled
  let completion :=
    execution.source.valid.sourceCompletion
  have firstPresent :
      first.Present
        (sourceHistory execution.source.skeleton) := by
    rcases (completion.selected firstSource).2 with
        present | pending
    · exact present
    · exfalso
      apply pending.no_matching_return
        (returned := first.returned)
        ⟨rfl, rfl⟩
      exact realTime.first_mem
  have sourceWellFormed :
      HerlihyWing.WellFormed
        (sourceHistory execution.source.skeleton) :=
    execution.source.valid.historyWellFormed
  have historyNodup :
      (sourceHistory execution.source.skeleton).Nodup :=
    SameThreadRealTime.history_nodup_of_id_nodup
      sourceWellFormed.invocationIdsNodup
      sourceWellFormed.returnIdsNodup
  have invocationOrder :
      HerlihyWing.Before
        (.invoke first.invocation)
        (.invoke second.invocation)
        (sourceHistory execution.source.skeleton) :=
    SameThreadRealTime.before_trans
      historyNodup firstPresent realTime
  have sourceCommitOrder :
      HerlihyWing.Before first second
        (sourceCommittedOperations
          execution.source.skeleton) :=
    completion.threadOrder
      firstSource secondSource sameThread invocationOrder
  have sourceThreadOrder :
      HerlihyWing.Before first second
        (HerlihyWing.operationsForThread first.thread
          (sourceCommittedOperations
            execution.source.skeleton)) :=
    SameThreadRealTime.before_operationsForThread
      sourceCommitOrder rfl sameThread.symm
  have scheduledThreadOrder :
      HerlihyWing.Before first second
        (HerlihyWing.operationsForThread first.thread
          (scheduledOperations execution schedule)) := by
    rw [← equivalent.2 first.thread]
    exact sourceThreadOrder
  exact
    SameThreadRealTime.before_of_operationsForThread
      scheduledThreadOrder

end SourceAtomicExecution

end WeakMemory.TreiberRC11
