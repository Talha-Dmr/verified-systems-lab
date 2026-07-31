import WeakMemory.MSQueueInfiniteControlProgress
import WeakMemory.MSQueueInfiniteSafety

namespace WeakMemory.MSQueue.Source

/-!
# Structural stabilization on response-free queue suffixes

This module separates the structural schedule needed by the queue invariant
from the stronger client-compatible schedule used by Herlihy--Wing safety.
It then records the two finite facts needed by the later stabilization proof:

* weak thread fairness excludes every abstract operation commit on a globally
  response-free suffix; and
* exact canonical replay bounds the number of successful Tail advances by the
  number of successful links in every finite prefix.

The remaining step from this finite budget to a modification-free suffix also
has to account for the one-time dynamic `next` initializer of each pending
enqueue.  That source-accounting lemma is intentionally not assumed here.
-/

namespace InfiniteRC11Execution

/-- Every finite prefix admits the RC11 atom schedule needed by canonical
structural replay.  Unlike `PrefixSchedules`, this premise contains no
cross-thread client-real-time condition. -/
def PrefixAtomSchedules
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  ∀ length,
    Nonempty
      (Structural.AtomSchedule
        (execution.supportedPrefix length))

/-- The schedule already packaged for finite Herlihy--Wing safety supplies
the weaker structural schedule required by liveness. -/
theorem PrefixSchedules.toPrefixAtomSchedules
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixSchedules) :
    execution.PrefixAtomSchedules := by
  intro length
  obtain ⟨compatible⟩ := schedules length
  exact ⟨compatible.schedule⟩

/-- Number of successful queue-link records in one chronological source
prefix. -/
def linkCount
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat) : Nat :=
  (Structural.Prefix.links
    (Structural.structuralRecords
      (execution.source.tracePrefix length))).length

/-- Number of successful Tail-advance records in one chronological source
prefix. -/
def tailMoveCount
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat) : Nat :=
  (Structural.Prefix.tailMoves
    (Structural.structuralRecords
      (execution.source.tracePrefix length))).length

/-- A source event that is not an operation commit contributes no successful
queue link. -/
private theorem links_singleton_eq_nil_of_notOperationCommit
    (event : TraceEvent Value)
    (notCommit : ¬ event.IsOperationCommit) :
    Structural.Prefix.links
        (Structural.structuralRecords [event]) = [] := by
  cases event with
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | initializeNext | enqueueTailLoad | enqueueNextLoad |
          enqueueTailValidate | dequeueHeadLoad | dequeueTailLoad |
          dequeueNextLoad | dequeueHeadValidate =>
          simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links]
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded <;> simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links]
      | enqueueHelpTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded <;> simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links,
            Structural.Prefix.Record.edge?]
      | enqueueFinishTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded <;> simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links,
            Structural.Prefix.Record.edge?]
      | dequeueHeadValidateEmpty =>
          simp_all [TraceEvent.IsOperationCommit]
      | dequeueHelpTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded <;> simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links,
            Structural.Prefix.Record.edge?]
      | dequeueHeadCAS thread operation expected desired value observed
          succeeded =>
          cases succeeded <;> simp_all [TraceEvent.IsOperationCommit,
            Structural.structuralRecords,
            Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.links]
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      simp [Structural.structuralRecords,
        Structural.structuralRecordOfEvent?,
        Structural.Prefix.links]

/-- Exact schedule coverage transfers the canonical replay's Tail bound back
to the chronological source-record multiset. -/
theorem tailMoveCount_le_linkCount_of_atomSchedule
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (schedule :
      Structural.AtomSchedule
        (execution.supportedPrefix length)) :
    execution.tailMoveCount length ≤
      execution.linkCount length := by
  have represented := schedule.canonicalReplay.1
  have coverage := schedule.recordsOn_perm
  have tailCoverage :=
    coverage.filterMap Structural.Prefix.Record.tailMove?
  have linkCoverage :=
    coverage.filterMap Structural.Prefix.Record.edge?
  have tailLength := tailCoverage.length_eq
  have linkLength := linkCoverage.length_eq
  unfold tailMoveCount linkCount
  change
    (List.filterMap Structural.Prefix.Record.tailMove?
      (Structural.structuralRecords
        (execution.source.tracePrefix length))).length ≤
    (List.filterMap Structural.Prefix.Record.edge?
      (Structural.structuralRecords
        (execution.source.tracePrefix length))).length
  rw [← tailLength, ← linkLength]
  simpa [Structural.Prefix.tailMoves,
    Structural.Prefix.links] using represented.tailBound

/-- Every admitted structural prefix satisfies the finite Tail/link budget. -/
theorem PrefixAtomSchedules.tailMoveCount_le_linkCount
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (length : Nat) :
    execution.tailMoveCount length ≤
      execution.linkCount length := by
  obtain ⟨schedule⟩ := schedules length
  exact execution.tailMoveCount_le_linkCount_of_atomSchedule
    length schedule

/-- Extending a source prefix by a noncommitting event cannot create a new
successful queue link. -/
theorem linkCount_succ_eq_of_notOperationCommit
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (notCommit :
      ¬ (execution.source.event length).IsOperationCommit) :
    execution.linkCount (length + 1) =
      execution.linkCount length := by
  rw [linkCount, linkCount, execution.source.tracePrefix_succ]
  simp only [Structural.structuralRecords, List.filterMap_append,
    Structural.Prefix.links, List.filterMap_append, List.length_append]
  have noLinks :=
    links_singleton_eq_nil_of_notOperationCommit
      (execution.source.event length) notCommit
  change
    List.filterMap Structural.Prefix.Record.edge?
        (List.filterMap Structural.structuralRecordOfEvent?
          [execution.source.event length]) = [] at noLinks
  rw [noLinks]
  simp

/-- If no event commits after `start`, then the successful-link count has
already reached its final value at `start`. -/
theorem linkCount_eq_of_noOperationCommit
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start : Nat)
    (noCommit :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsOperationCommit) :
    ∀ length,
      start ≤ length →
      execution.linkCount length = execution.linkCount start := by
  intro length afterStart
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst length
  clear afterStart
  induction offset with
  | zero => rfl
  | succ offset inductionHypothesis =>
      rw [← Nat.add_assoc]
      rw [execution.linkCount_succ_eq_of_notOperationCommit
        (start + offset)
        (noCommit (start + offset)
          (Nat.le_add_right start offset))]
      exact inductionHypothesis

/-- Queue-level restatement of the source-control result: a fair globally
response-free suffix contains no enqueue link, dequeue Head, or empty-dequeue
commit. -/
theorem noOperationCommit_on_responseFreeSuffix
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (threadFair : execution.source.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse) :
    ∀ time,
      start ≤ time →
      ¬ (execution.source.event time).IsOperationCommit :=
  execution.source.no_operationCommit_on_response_free_suffix
    threadFair start noResponse

/-- On a fair response-free suffix, all later successful Tail advances fit
inside the finite link budget already accumulated at the suffix boundary.
This is the structural stabilization result available without yet assuming
the separate source lemma that bounds dynamic `next` initialization. -/
theorem tailMoveCount_le_at_responseFreeStart
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse) :
    ∀ length,
      start ≤ length →
      execution.tailMoveCount length ≤
        execution.linkCount start := by
  have noCommit :=
    execution.noOperationCommit_on_responseFreeSuffix
      threadFair start noResponse
  intro length afterStart
  calc
    execution.tailMoveCount length ≤ execution.linkCount length :=
      PrefixAtomSchedules.tailMoveCount_le_linkCount
        execution schedules length
    _ = execution.linkCount start :=
      execution.linkCount_eq_of_noOperationCommit
        start noCommit length afterStart

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
