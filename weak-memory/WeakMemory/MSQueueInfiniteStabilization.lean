import WeakMemory.MSQueueInfiniteStructure

namespace WeakMemory.MSQueue.Source

/-!
# Eventual queue-wide modification stabilization

On a fair response-free suffix, abstract commits disappear.  Canonical FIFO
replay gives a finite budget for the remaining successful Tail-help moves,
and the source machine permits at most one fresh `next` initializer per
thread.  Since the thread family is finite, every queue site is therefore
modification-free after one common cutoff.
-/

namespace TraceEvent

/-- One dynamic initialization of a freshly reserved node's `next` field. -/
def IsNextInitializationBy
    (event : TraceEvent Value)
    (thread : ThreadId) : Prop :=
  ∃ id operation node,
    event = .atomic ⟨id, .initializeNext thread operation node⟩

/-- One successful CAS that advances the shared Tail pointer. -/
def IsTailMove : TraceEvent Value → Prop
  | .atomic ⟨_, .enqueueHelpTailCAS _ _ _ _ _ true⟩
  | .atomic ⟨_, .enqueueFinishTailCAS _ _ _ _ _ true⟩
  | .atomic ⟨_, .dequeueHelpTailCAS _ _ _ _ _ true⟩ => True
  | _ => False

/-- Every source-level modification is a commit, Tail move, or fresh init. -/
theorem operationCommit_or_tailMove_or_nextInitialization_of_modifiedAt
    {event : TraceEvent Value}
    {site : Site}
    (modified : event.ModifiedAt site) :
    event.IsOperationCommit ∨ event.IsTailMove ∨
      ∃ thread, event.IsNextInitializationBy thread := by
  cases event with
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      rcases modified with ⟨atSite, write⟩
      cases action with
      | initializeNext thread operation node =>
          exact Or.inr (Or.inr ⟨thread, id, operation, node, rfl⟩)
      | enqueueTailLoad | enqueueNextLoad | enqueueTailValidate |
          dequeueHeadLoad | dequeueTailLoad | dequeueNextLoad |
          dequeueHeadValidate | dequeueHeadValidateEmpty =>
          simp [AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at write
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded with
          | false =>
              simp [AtomicAction.access,
                MultiLocationRC11.Access.IsWrite] at write
          | true =>
              exact Or.inl (by simp [TraceEvent.IsOperationCommit])
      | enqueueHelpTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded with
          | false =>
              simp [AtomicAction.access,
                MultiLocationRC11.Access.IsWrite] at write
          | true => exact Or.inr (Or.inl (by simp [IsTailMove]))
      | enqueueFinishTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded with
          | false =>
              simp [AtomicAction.access,
                MultiLocationRC11.Access.IsWrite] at write
          | true => exact Or.inr (Or.inl (by simp [IsTailMove]))
      | dequeueHelpTailCAS thread operation expected desired observed
          succeeded =>
          cases succeeded with
          | false =>
              simp [AtomicAction.access,
                MultiLocationRC11.Access.IsWrite] at write
          | true => exact Or.inr (Or.inl (by simp [IsTailMove]))
      | dequeueHeadCAS thread operation expected desired value observed
          succeeded =>
          cases succeeded with
          | false =>
              simp [AtomicAction.access,
                MultiLocationRC11.Access.IsWrite] at write
          | true =>
              exact Or.inl (by simp [TraceEvent.IsOperationCommit])
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim modified

end TraceEvent

namespace LocalState

/-- An enqueue has emitted its unique fresh-node initializer. -/
def EnqueuePostInitialized : LocalState Value → Prop
  | .enqueueLoadingTail ..
  | .enqueueLoadingNext ..
  | .enqueueValidatingTail ..
  | .enqueueLinking ..
  | .enqueueHelpingTail ..
  | .enqueueFinishingTail ..
  | .enqueueReturning .. => True
  | _ => False

end LocalState

namespace LocalStep

/-- Emitting `initializeNext` enters the post-initialization region. -/
theorem enqueuePostInitialized_after_of_nextInitialization
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (initialization : event.IsNextInitializationBy thread) :
    after.EnqueuePostInitialized := by
  rcases initialization with ⟨id, operation, node, eventEq⟩
  subst event
  cases step <;>
    simp [LocalState.EnqueuePostInitialized] at *

/-- Until its response, an initialized enqueue remains in that region. -/
theorem enqueuePostInitialized_after_of_notResponse
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (post : before.EnqueuePostInitialized)
    (notResponse : ¬ event.IsResponse) :
    after.EnqueuePostInitialized := by
  cases step <;>
    simp [LocalState.EnqueuePostInitialized,
      TraceEvent.IsResponse] at post notResponse ⊢

/-- A post-initialization state cannot emit another `initializeNext`. -/
theorem not_nextInitialization_of_enqueuePostInitialized
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (post : before.EnqueuePostInitialized) :
    ¬ event.IsNextInitializationBy thread := by
  intro initialization
  rcases initialization with ⟨id, operation, node, eventEq⟩
  subst event
  cases step <;>
    simp [LocalState.EnqueuePostInitialized] at post

end LocalStep

namespace InfiniteExecution

/-- Post-initialization control persists on an owner-response-free suffix. -/
theorem enqueuePostInitialized_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      (execution.state start query).EnqueuePostInitialized)
    (noResponse :
      ∀ position,
        start ≤ position →
        ¬ (execution.event position).IsResponse) :
    (execution.state time query).EnqueuePostInitialized := by
  obtain ⟨offset, equation⟩ := Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero => exact initial
  | succ offset inductionHypothesis =>
      by_cases owner : (execution.event (start + offset)).thread = query
      · have localStep :
            LocalStep query
              (execution.state (start + offset) query)
              (execution.event (start + offset))
              (execution.state (start + offset + 1) query) := by
          simpa [owner] using (execution.valid (start + offset)).owner
        exact localStep.enqueuePostInitialized_after_of_notResponse
          inductionHypothesis
          (noResponse (start + offset)
            (Nat.le_add_right start offset))
      · have unchanged :=
          (execution.valid (start + offset)).frame query (Ne.symm owner)
        have targetEq :
            execution.state (start + (offset + 1)) query =
              execution.state (start + offset) query := by
          simpa [Nat.add_assoc] using unchanged
        rw [targetEq]
        exact inductionHypothesis

/-- One thread cannot initialize two fresh nodes on a response-free suffix. -/
theorem nextInitialization_time_unique_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse)
    (thread : ThreadId)
    {first second : Nat}
    (firstAfter : start ≤ first)
    (secondAfter : start ≤ second)
    (firstInit :
      (execution.event first).IsNextInitializationBy thread)
    (secondInit :
      (execution.event second).IsNextInitializationBy thread) :
    first = second := by
  rcases Nat.lt_trichotomy first second with before | same | after
  · have owner : (execution.event first).thread = thread := by
      rcases firstInit with ⟨id, operation, node, eventEq⟩
      simp [eventEq, TraceEvent.thread, AtomicAction.thread]
    have localStep :
        LocalStep thread
          (execution.state first thread)
          (execution.event first)
          (execution.state (first + 1) thread) := by
      simpa [owner] using (execution.valid first).owner
    have postAfter :
        (execution.state (first + 1) thread).EnqueuePostInitialized :=
      localStep.enqueuePostInitialized_after_of_nextInitialization firstInit
    have postAtSecond :
        (execution.state second thread).EnqueuePostInitialized :=
      execution.enqueuePostInitialized_on_response_free_suffix
        thread (start := first + 1) (time := second)
        (by omega) postAfter
        (fun position afterFirst => noResponse position (by omega))
    have secondOwner : (execution.event second).thread = thread := by
      rcases secondInit with ⟨id, operation, node, eventEq⟩
      simp [eventEq, TraceEvent.thread, AtomicAction.thread]
    have secondStep :
        LocalStep thread
          (execution.state second thread)
          (execution.event second)
          (execution.state (second + 1) thread) := by
      simpa [secondOwner] using (execution.valid second).owner
    exact False.elim
      (secondStep.not_nextInitialization_of_enqueuePostInitialized
        postAtSecond secondInit)
  · exact same
  · exact (execution.nextInitialization_time_unique_on_response_free_suffix
      start noResponse thread secondAfter firstAfter secondInit firstInit).symm

/-- Every bounded thread eventually emits no further `next` initializer. -/
theorem eventually_no_nextInitializationBy
    (execution : InfiniteExecution Value threadCount)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse)
    (thread : ThreadId) :
    ∃ cutoff,
      start ≤ cutoff ∧
        ∀ time,
          cutoff ≤ time →
          ¬ (execution.event time).IsNextInitializationBy thread := by
  classical
  by_cases existsInit :
      ∃ time,
        start ≤ time ∧
          (execution.event time).IsNextInitializationBy thread
  · obtain ⟨first, firstAfter, firstInit⟩ := existsInit
    refine ⟨first + 1, by omega, ?_⟩
    intro time afterCutoff laterInit
    have same :=
      execution.nextInitialization_time_unique_on_response_free_suffix
        start noResponse thread firstAfter (by omega) firstInit laterInit
    omega
  · refine ⟨start, Nat.le_refl _, ?_⟩
    intro time afterStart initialization
    exact existsInit ⟨time, afterStart, initialization⟩

private theorem uniform_nextInitialization_cutoff_aux
    (execution : InfiniteExecution Value threadCount)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    ∀ count,
      ∃ cutoff,
        start ≤ cutoff ∧
          ∀ thread,
            thread < count →
            ∀ time,
              cutoff ≤ time →
              ¬ (execution.event time).IsNextInitializationBy thread := by
  intro count
  induction count with
  | zero =>
      exact ⟨start, Nat.le_refl _, fun thread impossible =>
        False.elim (Nat.not_lt_zero thread impossible)⟩
  | succ count inductionHypothesis =>
      obtain ⟨earlierCutoff, earlierAfter, earlierStable⟩ :=
        inductionHypothesis
      obtain ⟨lastCutoff, lastAfter, lastStable⟩ :=
        execution.eventually_no_nextInitializationBy
          start noResponse count
      refine ⟨max earlierCutoff lastCutoff, by omega, ?_⟩
      intro thread threadBound time afterCutoff initialization
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ threadBound) with
        before | same
      · exact earlierStable thread before time
          (Nat.le_trans (Nat.le_max_left _ _) afterCutoff) initialization
      · subst thread
        exact lastStable time
          (Nat.le_trans (Nat.le_max_right _ _) afterCutoff) initialization

/-- Finite ownership gives one cutoff after all dynamic next initializers. -/
theorem eventually_no_nextInitialization
    (execution : InfiniteExecution Value threadCount)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    ∃ cutoff,
      start ≤ cutoff ∧
        ∀ time,
          cutoff ≤ time →
          ∀ thread,
            ¬ (execution.event time).IsNextInitializationBy thread := by
  obtain ⟨cutoff, afterStart, stable⟩ :=
    execution.uniform_nextInitialization_cutoff_aux
      start noResponse threadCount
  refine ⟨cutoff, afterStart, ?_⟩
  intro time afterCutoff thread initialization
  have owner : (execution.event time).thread = thread := by
    rcases initialization with ⟨id, operation, node, eventEq⟩
    simp [eventEq, TraceEvent.thread, AtomicAction.thread]
  have bounded : thread < threadCount := by
    rw [← owner]
    exact execution.ownerBound time
  exact stable thread bounded time afterCutoff initialization

end InfiniteExecution

namespace InfiniteRC11Execution

/-- Appending one event never decreases the chronological Tail-move count. -/
theorem tailMoveCount_le_succ
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat) :
    execution.tailMoveCount length ≤
      execution.tailMoveCount (length + 1) := by
  rw [tailMoveCount, tailMoveCount, execution.source.tracePrefix_succ]
  simp only [Structural.structuralRecords, List.filterMap_append,
    Structural.Prefix.tailMoves, List.filterMap_append, List.length_append]
  omega

/-- Tail-move count grows by one at every successful Tail advance. -/
theorem tailMoveCount_succ_eq_add_one_of_tailMove
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat)
    (tailMove : (execution.source.event length).IsTailMove) :
    execution.tailMoveCount (length + 1) =
      execution.tailMoveCount length + 1 := by
  rw [tailMoveCount, tailMoveCount, execution.source.tracePrefix_succ]
  simp only [Structural.structuralRecords, List.filterMap_append,
    Structural.Prefix.tailMoves, List.filterMap_append, List.length_append]
  cases eventEq : execution.source.event length with
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        simp_all [TraceEvent.IsTailMove]
      all_goals
        cases ‹Bool› <;>
          simp_all [Structural.structuralRecordOfEvent?,
            Structural.structuralRecordOfOccurrence?,
            Structural.Prefix.Record.tailMove?]
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      simp [TraceEvent.IsTailMove, eventEq] at tailMove

/-- Tail-move prefix counts are monotone in prefix length. -/
theorem tailMoveCount_mono
    (execution : InfiniteRC11Execution Value threadCount dummy)
    {first second : Nat}
    (ordered : first ≤ second) :
    execution.tailMoveCount first ≤ execution.tailMoveCount second := by
  obtain ⟨offset, equation⟩ := Nat.exists_eq_add_of_le ordered
  subst second
  clear ordered
  induction offset with
  | zero => exact Nat.le_refl _
  | succ offset inductionHypothesis =>
      exact Nat.le_trans inductionHypothesis
        (by simpa [Nat.add_assoc] using
          execution.tailMoveCount_le_succ (first + offset))

private theorem tailMoveCount_growth_of_recurring
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (recurring :
      ∀ cutoff,
        ∃ time,
          cutoff ≤ time ∧
            (execution.source.event time).IsTailMove)
    (steps cutoff : Nat) :
    ∃ length,
      cutoff ≤ length ∧
        execution.tailMoveCount cutoff + steps ≤
          execution.tailMoveCount length := by
  induction steps generalizing cutoff with
  | zero => exact ⟨cutoff, Nat.le_refl _, by omega⟩
  | succ steps inductionHypothesis =>
      obtain ⟨time, afterCutoff, tailMove⟩ := recurring cutoff
      obtain ⟨length, afterMove, growth⟩ :=
        inductionHypothesis (time + 1)
      refine ⟨length, Nat.le_trans afterCutoff
        (Nat.le_trans (Nat.le_add_right time 1) afterMove), ?_⟩
      have beforeMove := execution.tailMoveCount_mono afterCutoff
      have atMove :=
        execution.tailMoveCount_succ_eq_add_one_of_tailMove time tailMove
      omega

/-- The finite replay budget implies eventual absence of Tail-help writes. -/
theorem eventually_no_tailMove_on_responseFreeSuffix
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse) :
    ∃ cutoff,
      start ≤ cutoff ∧
        ∀ time,
          cutoff ≤ time →
          ¬ (execution.source.event time).IsTailMove := by
  classical
  by_cases stable :
      ∃ cutoff,
        start ≤ cutoff ∧
          ∀ time,
            cutoff ≤ time →
            ¬ (execution.source.event time).IsTailMove
  · exact stable
  · exfalso
    have recurring :
        ∀ cutoff,
          ∃ time,
            cutoff ≤ time ∧
              (execution.source.event time).IsTailMove := by
      intro cutoff
      by_cases existsMove :
          ∃ time,
            max start cutoff ≤ time ∧
              (execution.source.event time).IsTailMove
      · obtain ⟨time, afterMaximum, move⟩ := existsMove
        exact ⟨time,
          Nat.le_trans (Nat.le_max_right start cutoff) afterMaximum,
          move⟩
      · exact False.elim (stable ⟨max start cutoff,
          Nat.le_max_left _ _, fun time afterMaximum move =>
            existsMove ⟨time, afterMaximum, move⟩⟩)
    obtain ⟨length, afterStart, growth⟩ :=
      execution.tailMoveCount_growth_of_recurring
        recurring (execution.linkCount start + 1) start
    have bounded :=
      execution.tailMoveCount_le_at_responseFreeStart
        schedules threadFair start noResponse length afterStart
    omega

/-- A fair response-free suffix eventually modifies no logical queue site. -/
theorem eventually_noModification_on_responseFreeSuffix
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse) :
    ∃ cutoff,
      start ≤ cutoff ∧
        ∀ site,
          WeakCAS.SiteProgressRule.NoModificationAtFrom
            execution.progressInterface site cutoff := by
  obtain ⟨tailCutoff, tailAfter, noTailMove⟩ :=
    execution.eventually_no_tailMove_on_responseFreeSuffix
      schedules threadFair start noResponse
  obtain ⟨initCutoff, initAfter, noInitialization⟩ :=
    execution.source.eventually_no_nextInitialization start noResponse
  let cutoff := max tailCutoff initCutoff
  have cutoffAfter : start ≤ cutoff := by
    exact Nat.le_trans tailAfter (Nat.le_max_left _ _)
  refine ⟨cutoff, cutoffAfter, ?_⟩
  intro site time afterCutoff modified
  rcases
      TraceEvent.operationCommit_or_tailMove_or_nextInitialization_of_modifiedAt
        modified with commit | tailMove | ⟨thread, initialization⟩
  · exact
      (execution.noOperationCommit_on_responseFreeSuffix
        threadFair start noResponse time
        (Nat.le_trans cutoffAfter afterCutoff)) commit
  · exact noTailMove time
      (Nat.le_trans (Nat.le_max_left _ _) afterCutoff) tailMove
  · exact noInitialization time
      (Nat.le_trans (Nat.le_max_right _ _) afterCutoff)
      thread initialization

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
