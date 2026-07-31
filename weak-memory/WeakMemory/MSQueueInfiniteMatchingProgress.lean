import WeakMemory.MSQueueInfiniteRetryVisibility
import WeakMemory.MSQueueInfiniteStabilization

namespace WeakMemory.MSQueue.Source

/-!
# Stable queue control reaches compare-equal CAS attempts

This is the source-control half of the fairness derivation.  A stable pointer
assignment describes the value returned by every sufficiently late atomic
read at its exact logical site.  Cached Head/Tail/next values are then either
already aligned with that assignment or are flushed through a bounded retry.
Once aligned, every fair scheduled source path reaches a compare-equal CAS,
an abstract commit, a modification, or a response in bounded local work.
-/

namespace TraceEvent

/-- One source event is a compare-equal queue CAS, at an unspecified site. -/
def IsMatchingCAS : TraceEvent Value → Prop
  | .atomic occurrence => occurrence.action.IsMatchingCAS
  | _ => False

/-- A matching event supplies its exact owner and exact logical site. -/
theorem matchingCAS_matchingAttemptAt
    {event : TraceEvent Value}
    (matching : event.IsMatchingCAS) :
    event.MatchingAttemptAt event.thread
      (match event with
      | .atomic occurrence => occurrence.action.site
      | _ => .head) := by
  cases event with
  | atomic occurrence =>
      exact ⟨rfl, rfl, matching⟩
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim matching

end TraceEvent

namespace LocalState

/-- Cached source variables agree with the stable value at their read sites. -/
def Aligned
    (stableValue : Site → Ptr) : LocalState Value → Prop
  | .idle
  | .enqueueWritingPayload ..
  | .enqueueInitializingNext ..
  | .enqueueLoadingTail ..
  | .enqueueReturning ..
  | .dequeueLoadingHead ..
  | .dequeueReturning .. => True
  | .enqueueLoadingNext _ _ _ tail =>
      stableValue .tail = .node tail
  | .enqueueValidatingTail _ _ _ tail next =>
      stableValue .tail = .node tail ∧
        stableValue (.next tail) = next
  | .enqueueLinking _ _ _ tail =>
      stableValue .tail = .node tail ∧
        stableValue (.next tail) = .null
  | .enqueueHelpingTail _ _ _ expected _ =>
      stableValue .tail = .node expected
  | .enqueueFinishingTail _ _ _ expected =>
      stableValue .tail = .node expected
  | .dequeueLoadingTail _ head =>
      stableValue .head = .node head
  | .dequeueLoadingNext _ head tail =>
      stableValue .head = .node head ∧
        stableValue .tail = .node tail
  | .dequeueValidatingHead _ head tail _ next =>
      stableValue .head = .node head ∧
        stableValue .tail = .node tail ∧
        stableValue (.next head) = next
  | .dequeueHelpingTail _ expected _ =>
      stableValue .tail = .node expected
  | .dequeueReadingPayload _ head _
  | .dequeueSwingingHead _ head .. =>
      stableValue .head = .node head

/-- Bounded local work remaining before alignment or a progress event. -/
def stableRank : LocalState Value → Nat
  | .idle => 0
  | .enqueueWritingPayload .. => 2
  | .enqueueInitializingNext .. => 1
  | .enqueueLoadingTail .. => 4
  | .enqueueLoadingNext .. => 3
  | .enqueueValidatingTail .. => 2
  | .enqueueLinking ..
  | .enqueueHelpingTail ..
  | .enqueueFinishingTail ..
  | .enqueueReturning .. => 1
  | .dequeueLoadingHead .. => 6
  | .dequeueLoadingTail .. => 5
  | .dequeueLoadingNext .. => 4
  | .dequeueValidatingHead .. => 3
  | .dequeueHelpingTail .. => 1
  | .dequeueReadingPayload .. => 2
  | .dequeueSwingingHead ..
  | .dequeueReturning .. => 1

theorem stableRank_le_six
    (state : LocalState Value) :
    state.stableRank ≤ 6 := by
  cases state <;> simp [stableRank]

/-- One phase bit combines stale-cache flushing with aligned source progress. -/
noncomputable def fairRank
    (stableValue : Site → Ptr)
    (state : LocalState Value) : Nat := by
  classical
  exact if state.Aligned stableValue then
    state.stableRank
  else
    state.stableRank + 7

theorem fairRank_eq_stableRank
    (stableValue : Site → Ptr)
    (state : LocalState Value)
    (aligned : state.Aligned stableValue) :
    state.fairRank stableValue = state.stableRank := by
  classical
  simp [fairRank, aligned]

theorem fairRank_eq_stableRank_add_seven
    (stableValue : Site → Ptr)
    (state : LocalState Value)
    (notAligned : ¬ state.Aligned stableValue) :
    state.fairRank stableValue = state.stableRank + 7 := by
  classical
  simp [fairRank, notAligned]

theorem fairRank_le_thirteen
    (stableValue : Site → Ptr)
    (state : LocalState Value) :
    state.fairRank stableValue ≤ 13 := by
  classical
  by_cases aligned : state.Aligned stableValue
  · rw [state.fairRank_eq_stableRank stableValue aligned]
    exact Nat.le_trans state.stableRank_le_six (by omega)
  · rw [state.fairRank_eq_stableRank_add_seven stableValue aligned]
    have bound := state.stableRank_le_six
    omega

end LocalState

namespace LocalStep

/-!
The two local lemmas below are exhaustive checks of the source machine.  The
first flushes stale cached snapshots; the second shows strict bounded progress
once all caches are aligned.  Successful CAS and fresh initialization are
reported as modifications rather than silently treated as local work.
-/

/-- A stable observation either makes the next state aligned, decreases the
flush rank, or emits a response/commit/modification/matching CAS. -/
theorem alignment_or_progress
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (active : before.Active)
    (observes : event.ObservesStable stableValue) :
    event.IsResponse ∨
      event.IsOperationCommit ∨
      (∃ site, event.ModifiedAt site) ∨
      event.IsMatchingCAS ∨
      after.Aligned stableValue ∨
      after.stableRank < before.stableRank := by
  cases step <;>
    simp_all [LocalState.Active, LocalState.Aligned,
      LocalState.stableRank, TraceEvent.ObservesStable,
      TraceEvent.IsResponse, TraceEvent.IsOperationCommit,
      TraceEvent.ModifiedAt, TraceEvent.IsMatchingCAS,
      AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.IsRead,
      MultiLocationRC11.Atom.readValue, AtomicAction.access,
      AtomicAction.site, AtomicAction.IsMatchingCAS,
      AtomicAction.casView?, MultiLocationRC11.Access.IsRead,
      MultiLocationRC11.Access.IsWrite,
      MultiLocationRC11.Access.readValue]

/-- From an aligned active state, every non-progress scheduled step preserves
alignment and strictly decreases the stable-control rank. -/
theorem aligned_progress
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (active : before.Active)
    (aligned : before.Aligned stableValue)
    (observes : event.ObservesStable stableValue) :
    event.IsResponse ∨
      event.IsOperationCommit ∨
      (∃ site, event.ModifiedAt site) ∨
      event.IsMatchingCAS ∨
      (after.Aligned stableValue ∧
        after.stableRank < before.stableRank) := by
  cases step <;>
    simp_all [LocalState.Active, LocalState.Aligned,
      LocalState.stableRank, TraceEvent.ObservesStable,
      TraceEvent.IsResponse, TraceEvent.IsOperationCommit,
      TraceEvent.ModifiedAt, TraceEvent.IsMatchingCAS,
      AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.IsRead,
      MultiLocationRC11.Atom.readValue, AtomicAction.access,
      AtomicAction.site, AtomicAction.IsMatchingCAS,
      AtomicAction.casView?, MultiLocationRC11.Access.IsRead,
      MultiLocationRC11.Access.IsWrite,
      MultiLocationRC11.Access.readValue]

/-- Outside a visible progress event, every scheduled active step strictly
decreases the combined stale/aligned rank. -/
theorem fairRank_decreases_or_progress
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (active : before.Active)
    (observes : event.ObservesStable stableValue) :
    event.IsResponse ∨
      event.IsOperationCommit ∨
      (∃ site, event.ModifiedAt site) ∨
      event.IsMatchingCAS ∨
      after.fairRank stableValue < before.fairRank stableValue := by
  classical
  by_cases aligned : before.Aligned stableValue
  · rcases step.aligned_progress active aligned observes with
      response | commit | modification | matching | ⟨afterAligned, decrease⟩
    · exact Or.inl response
    · exact Or.inr (Or.inl commit)
    · exact Or.inr (Or.inr (Or.inl modification))
    · exact Or.inr (Or.inr (Or.inr (Or.inl matching)))
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      rw [after.fairRank_eq_stableRank stableValue afterAligned]
      rw [before.fairRank_eq_stableRank stableValue aligned]
      exact decrease
  · rcases step.alignment_or_progress active observes with
      response | commit | modification | matching | afterAligned | decrease
    · exact Or.inl response
    · exact Or.inr (Or.inl commit)
    · exact Or.inr (Or.inr (Or.inl modification))
    · exact Or.inr (Or.inr (Or.inr (Or.inl matching)))
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      rw [after.fairRank_eq_stableRank stableValue afterAligned]
      rw [before.fairRank_eq_stableRank_add_seven stableValue aligned]
      have bound := after.stableRank_le_six
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      by_cases afterAligned : after.Aligned stableValue
      · rw [after.fairRank_eq_stableRank stableValue afterAligned]
        rw [before.fairRank_eq_stableRank_add_seven stableValue aligned]
        have bound := after.stableRank_le_six
        omega
      · rw [after.fairRank_eq_stableRank_add_seven stableValue afterAligned]
        rw [before.fairRank_eq_stableRank_add_seven stableValue aligned]
        exact Nat.add_lt_add_right decrease 7

end LocalStep

namespace InfiniteRC11Execution

/-!
A fair active owner cannot decrease a natural rank at every scheduled step.
Consequently a response-free, modification-free suffix with stable reads has
compare-equal CAS attempts by that owner arbitrarily late.
-/
theorem infinitelyOften_matchingCAS_of_stableObservations
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (threadFair : execution.source.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (activeAtStart :
      (execution.source.state start query).Active)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse)
    (noModification :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site start)
    (stableValue : Site → Ptr)
    (observes :
      ∀ time,
        start ≤ time →
        (execution.source.event time).ObservesStable stableValue) :
    Liveness.InfinitelyOften (fun time =>
      (execution.source.event time).thread = query ∧
        (execution.source.event time).IsMatchingCAS) := by
  classical
  have continuouslyActive :
      ∀ time,
        start ≤ time →
        (execution.source.state time query).Active := by
    intro time afterStart
    exact execution.source.active_on_response_free_suffix
      query afterStart activeAtStart noResponse
  have noCommit :=
    execution.source.no_operationCommit_on_response_free_suffix
      threadFair start noResponse
  intro bound
  let base := max start bound
  have baseAfterStart : start ≤ base := Nat.le_max_left _ _
  have baseAfterBound : bound ≤ base := Nat.le_max_right _ _
  apply Classical.byContradiction
  intro noWitness
  have noMatching :
      ∀ time,
        base ≤ time →
        ¬ ((execution.source.event time).thread = query ∧
          (execution.source.event time).IsMatchingCAS) := by
    intro time afterBase matching
    exact noWitness ⟨time,
      Nat.le_trans baseAfterBound afterBase, matching⟩
  have enabledEventually :
      Liveness.EventuallyAlways (fun time =>
        InfiniteExecution.Enabled
          (execution.source.state time) query) := by
    refine ⟨base, ?_⟩
    intro time afterBase
    exact continuouslyActive time
      (Nat.le_trans baseAfterStart afterBase)
  have scheduledOften :
      Liveness.InfinitelyOften (fun time =>
        some (execution.source.event time).thread = some query) :=
    threadFair query enabledEventually
  have oneStepLe :
      ∀ time,
        base ≤ time →
        (execution.source.state (time + 1) query).fairRank stableValue ≤
          (execution.source.state time query).fairRank stableValue := by
    intro time afterBase
    by_cases owner : (execution.source.event time).thread = query
    · have localStep :
          LocalStep query
            (execution.source.state time query)
            (execution.source.event time)
            (execution.source.state (time + 1) query) := by
        simpa [owner] using (execution.source.valid time).owner
      rcases localStep.fairRank_decreases_or_progress
          (continuouslyActive time
            (Nat.le_trans baseAfterStart afterBase))
          (observes time
            (Nat.le_trans baseAfterStart afterBase)) with
        response | commit | modification | matching | decrease
      · exact False.elim
          (noResponse time
            (Nat.le_trans baseAfterStart afterBase) response)
      · exact False.elim
          (noCommit time
            (Nat.le_trans baseAfterStart afterBase) commit)
      · obtain ⟨site, modified⟩ := modification
        exact False.elim
          (noModification site time
            (Nat.le_trans baseAfterStart afterBase) modified)
      · exact False.elim (noMatching time afterBase ⟨owner, matching⟩)
      · exact Nat.le_of_lt decrease
    · have unchanged :=
        (execution.source.valid time).frame query (Ne.symm owner)
      rw [unchanged]
      exact Nat.le_refl _
  have scheduledStepLt :
      ∀ time,
        base ≤ time →
        (execution.source.event time).thread = query →
        (execution.source.state (time + 1) query).fairRank stableValue <
          (execution.source.state time query).fairRank stableValue := by
    intro time afterBase owner
    have localStep :
        LocalStep query
          (execution.source.state time query)
          (execution.source.event time)
          (execution.source.state (time + 1) query) := by
      simpa [owner] using (execution.source.valid time).owner
    rcases localStep.fairRank_decreases_or_progress
        (continuouslyActive time
          (Nat.le_trans baseAfterStart afterBase))
        (observes time
          (Nat.le_trans baseAfterStart afterBase)) with
      response | commit | modification | matching | decrease
    · exact False.elim
        (noResponse time
          (Nat.le_trans baseAfterStart afterBase) response)
    · exact False.elim
        (noCommit time
          (Nat.le_trans baseAfterStart afterBase) commit)
    · obtain ⟨site, modified⟩ := modification
      exact False.elim
        (noModification site time
          (Nat.le_trans baseAfterStart afterBase) modified)
    · exact False.elim (noMatching time afterBase ⟨owner, matching⟩)
    · exact decrease
  have rankLeOn :
      ∀ {first second : Nat},
        base ≤ first →
        first ≤ second →
        (execution.source.state second query).fairRank stableValue ≤
          (execution.source.state first query).fairRank stableValue := by
    intro first second firstAfter ordered
    obtain ⟨offset, equation⟩ := Nat.exists_eq_add_of_le ordered
    subst second
    clear ordered
    induction offset with
    | zero => exact Nat.le_refl _
    | succ offset inductionHypothesis =>
        have lastStep := oneStepLe (first + offset) (by omega)
        exact Nat.le_trans
          (by simpa [Nat.add_assoc] using lastStep)
          inductionHypothesis
  have rankDescent :
      ∀ steps current,
        base ≤ current →
        ∃ later,
          current ≤ later ∧
            (execution.source.state later query).fairRank stableValue + steps ≤
              (execution.source.state current query).fairRank stableValue := by
    intro steps
    induction steps with
    | zero =>
        intro current currentAfter
        exact ⟨current, Nat.le_refl _, by omega⟩
    | succ steps inductionHypothesis =>
        intro current currentAfter
        obtain ⟨middle, afterCurrent, descent⟩ :=
          inductionHypothesis current currentAfter
        obtain ⟨time, afterMiddle, scheduledSome⟩ :=
          scheduledOften middle
        have owner : (execution.source.event time).thread = query :=
          Option.some.inj scheduledSome
        have beforeScheduled := rankLeOn (Nat.le_trans currentAfter afterCurrent)
          afterMiddle
        have atScheduled := scheduledStepLt time (by omega) owner
        refine ⟨time + 1,
          Nat.le_trans afterCurrent
            (Nat.le_trans afterMiddle (Nat.le_add_right time 1)), ?_⟩
        omega
  obtain ⟨later, _, impossibleDescent⟩ :=
    rankDescent 14 base (Nat.le_refl _)
  have initialBound :=
    (execution.source.state base query).fairRank_le_thirteen stableValue
  omega

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
