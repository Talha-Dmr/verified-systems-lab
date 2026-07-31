import WeakMemory.MSQueueInfinite

namespace WeakMemory.MSQueue.Source

/-!
# Scheduling fairness reaches Michael--Scott retry boundaries

This source-only layer isolates the scheduling facts needed by the later
memory-visibility argument.  A fair active thread must repeatedly reach either
a weak-CAS attempt or a snapshot validation.  Source semantics alone cannot
remove the snapshot alternative: Head or Tail may be observed to change at
every validation until a memory-fairness theorem supplies stable visibility.

Successful enqueue-link and dequeue-Head CASes, together with an empty
dequeue validation, are operation commits.  Enqueue commits retain one
best-effort Tail swing before returning, so post-commit response progress is
proved through a separate rank rather than by identifying commit states with
returning states.
-/

namespace AtomicAction

/-- A source-level weak compare-and-exchange attempt at any queue site. -/
def IsCASAttempt : AtomicAction Value → Prop
  | .enqueueLinkCAS ..
  | .enqueueHelpTailCAS ..
  | .enqueueFinishTailCAS ..
  | .dequeueHelpTailCAS ..
  | .dequeueHeadCAS .. => True
  | _ => False

/-- A snapshot reload that may restart or advance a retry path. -/
def IsRetrySnapshot : AtomicAction Value → Prop
  | .enqueueTailValidate ..
  | .dequeueHeadValidate .. => True
  | _ => False

end AtomicAction

namespace TraceEvent

/-- A dynamic weak-CAS attempt, successful or failed. -/
def IsCASAttempt : TraceEvent Value → Prop
  | .atomic occurrence => occurrence.action.IsCASAttempt
  | _ => False

/-- A noncommitting Head or Tail snapshot validation. -/
def IsRetrySnapshot : TraceEvent Value → Prop
  | .atomic occurrence => occurrence.action.IsRetrySnapshot
  | _ => False

/-- An event that commits one abstract enqueue or dequeue operation. -/
def IsOperationCommit : TraceEvent Value → Prop
  | .atomic ⟨_, .enqueueLinkCAS _ _ _ _ _ _ true⟩
  | .atomic ⟨_, .dequeueHeadValidateEmpty ..⟩
  | .atomic ⟨_, .dequeueHeadCAS _ _ _ _ _ _ true⟩ => True
  | _ => False

/-- A retry-relevant boundary at one exact logical queue site. -/
def RetryBoundaryAt
    (event : TraceEvent Value)
    (site : Site) : Prop :=
  match event with
  | .atomic occurrence =>
      occurrence.action.site = site ∧
        (occurrence.action.IsCASAttempt ∨
          occurrence.action.IsRetrySnapshot)
  | _ => False

/--
The source-control boundaries relevant to liveness.

An empty-dequeue validation is an operation commit rather than a retry
snapshot.  Successful link/Head CASes satisfy both the retry-boundary and
operation-commit branches; retaining both classifications is useful to the
later response-free argument.
-/
def IsLivenessBoundary (event : TraceEvent Value) : Prop :=
  (∃ site, event.RetryBoundaryAt site) ∨
    event.IsOperationCommit ∨
    event.IsResponse

/-- Every exact retry boundary is either a CAS attempt or a retry snapshot. -/
theorem casAttempt_or_retrySnapshot_of_retryBoundaryAt
    {event : TraceEvent Value}
    {site : Site}
    (boundary : event.RetryBoundaryAt site) :
    event.IsCASAttempt ∨ event.IsRetrySnapshot := by
  cases event with
  | atomic occurrence =>
      exact boundary.2
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim boundary

end TraceEvent

namespace LocalState

/-- A committed method that still owes its client response. -/
def Committed : LocalState Value → Prop
  | .enqueueFinishingTail ..
  | .enqueueReturning ..
  | .dequeueReturning .. => True
  | _ => False

/-- Every committed state is still an active method invocation. -/
theorem Committed.active
    {state : LocalState Value}
    (committed : state.Committed) :
    state.Active := by
  cases state <;> simp [Committed, Active] at committed ⊢

/--
Scheduled non-boundary steps remaining before the next retry, commit, or
response boundary.
-/
def controlRank : LocalState Value → Nat
  | .idle => 0
  | .enqueueWritingPayload .. => 4
  | .enqueueInitializingNext .. => 3
  | .enqueueLoadingTail .. => 2
  | .enqueueLoadingNext .. => 1
  | .enqueueValidatingTail .. => 0
  | .enqueueLinking .. => 0
  | .enqueueHelpingTail .. => 0
  | .enqueueFinishingTail .. => 0
  | .enqueueReturning .. => 0
  | .dequeueLoadingHead .. => 3
  | .dequeueLoadingTail .. => 2
  | .dequeueLoadingNext .. => 1
  | .dequeueValidatingHead .. => 0
  | .dequeueHelpingTail .. => 0
  | .dequeueReadingPayload .. => 1
  | .dequeueSwingingHead .. => 0
  | .dequeueReturning .. => 0

/-- The local distance to a liveness boundary is uniformly bounded. -/
theorem controlRank_le_four
    (state : LocalState Value) :
    state.controlRank ≤ 4 := by
  cases state <;> simp [controlRank]

/-- Scheduled local steps remaining after an abstract operation commit. -/
def responseRank : LocalState Value → Nat
  | .enqueueFinishingTail .. => 1
  | _ => 0

/-- A committed source state needs at most two fair scheduling positions. -/
theorem responseRank_le_one
    (state : LocalState Value) :
    state.responseRank ≤ 1 := by
  cases state <;> simp [responseRank]

end LocalState

namespace LocalStep

/-- A non-response source step preserves an active method invocation. -/
theorem active_after_of_not_response
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (active : before.Active)
    (notResponse : ¬ event.IsResponse) :
    after.Active := by
  cases step <;>
    simp [LocalState.Active, TraceEvent.IsResponse] at active notResponse ⊢

/-- The only source step from a returning state emits its method response. -/
theorem response_of_returning
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (returning :
      (match before with
      | .enqueueReturning .. | .dequeueReturning .. => True
      | _ => False)) :
    event.IsResponse := by
  cases step <;>
    simp [TraceEvent.IsResponse] at returning ⊢

/-- Every abstract operation commit enters the finite post-commit region. -/
theorem committed_after_of_operationCommit
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (commit : event.IsOperationCommit) :
    after.Committed := by
  cases step <;>
    simp [TraceEvent.IsOperationCommit,
      LocalState.Committed] at commit ⊢

/-- A non-response step from the post-commit region stays post-commit. -/
theorem committed_after_of_not_response
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (committed : before.Committed)
    (notResponse : ¬ event.IsResponse) :
    after.Committed := by
  cases step <;>
    simp [LocalState.Committed,
      TraceEvent.IsResponse] at committed notResponse ⊢

/-- Every scheduled non-response post-commit step decreases response rank. -/
theorem responseRank_decreases
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (committed : before.Committed)
    (notResponse : ¬ event.IsResponse) :
    after.responseRank < before.responseRank := by
  cases step <;>
    simp [LocalState.Committed, LocalState.responseRank,
      TraceEvent.IsResponse] at committed notResponse ⊢

/--
Every scheduled active step either reaches a liveness boundary or strictly
decreases the uniformly bounded control rank.
-/
theorem livenessBoundary_or_controlRank_decreases
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    (active : before.Active) :
    event.IsLivenessBoundary ∨
      after.controlRank < before.controlRank := by
  cases step <;>
    simp [LocalState.Active, LocalState.controlRank,
      TraceEvent.IsLivenessBoundary, TraceEvent.RetryBoundaryAt,
      TraceEvent.IsOperationCommit, TraceEvent.IsResponse,
      AtomicAction.IsCASAttempt, AtomicAction.IsRetrySnapshot,
      AtomicAction.site] at active ⊢

end LocalStep

namespace InfiniteExecution

/-- The scheduler enables exactly threads with an active method invocation. -/
def Enabled
    (state : GlobalState Value)
    (thread : ThreadId) : Prop :=
  (state thread).Active

/-- Weak scheduling fairness specialized to the infinite queue source run. -/
def WeakThreadFair
    (execution : InfiniteExecution Value threadCount) : Prop :=
  Liveness.WeakThreadFair
    execution.toInfiniteRun
    Enabled
    (fun event => some event.thread)

/-- A non-response global step preserves activity of every active thread. -/
theorem active_preserved_of_not_response
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : (before query).Active)
    (notResponse : ¬ event.IsResponse) :
    (after query).Active := by
  by_cases owner : event.thread = query
  · subst query
    exact transition.owner.active_after_of_not_response
      active notResponse
  · have unchanged :
        after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact active

/-- Activity persists throughout a suffix containing no method response. -/
theorem active_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial : (execution.state start query).Active)
    (noResponse :
      ∀ position,
        start ≤ position →
        ¬ (execution.event position).IsResponse) :
    (execution.state time query).Active := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact initial
  | succ offset inductionHypothesis =>
      exact
        active_preserved_of_not_response
          (execution.valid (start + offset))
          query
          inductionHypothesis
          (noResponse (start + offset)
            (Nat.le_add_right start offset))

/-- A committed method is preserved unless its owner emits its response. -/
theorem committed_preserved_of_no_scheduled_response
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (committed : (before query).Committed)
    (noResponse :
      event.thread = query →
        ¬ event.IsResponse) :
    (after query).Committed := by
  by_cases owner : event.thread = query
  · subst query
    exact transition.owner.committed_after_of_not_response
      committed (noResponse rfl)
  · have unchanged :
        after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact committed

/-- A committed method persists until its own response is emitted. -/
theorem committed_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial : (execution.state start query).Committed)
    (noResponse :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        ¬ (execution.event position).IsResponse) :
    (execution.state time query).Committed := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact initial
  | succ offset inductionHypothesis =>
      exact
        committed_preserved_of_no_scheduled_response
          (execution.valid (start + offset))
          query
          inductionHypothesis
          (fun scheduled =>
            noResponse (start + offset)
              (Nat.le_add_right start offset)
              scheduled)

/-- One boundary-free global step cannot increase an active thread's rank. -/
theorem controlRank_le_of_no_scheduled_boundary
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : (before query).Active)
    (noBoundary :
      event.thread = query →
        ¬ event.IsLivenessBoundary) :
    (after query).controlRank ≤
      (before query).controlRank := by
  by_cases owner : event.thread = query
  · subst query
    rcases transition.owner
        |>.livenessBoundary_or_controlRank_decreases active with
      boundary | decreases
    · exact False.elim (noBoundary rfl boundary)
    · exact Nat.le_of_lt decreases
  · have unchanged : after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact Nat.le_refl _

/-- A scheduled non-boundary step strictly decreases an active thread's rank. -/
theorem controlRank_lt_of_scheduled_nonboundary
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : (before query).Active)
    (scheduled : event.thread = query)
    (notBoundary : ¬ event.IsLivenessBoundary) :
    (after query).controlRank <
      (before query).controlRank := by
  subst query
  rcases transition.owner
      |>.livenessBoundary_or_controlRank_decreases active with
    boundary | decreases
  · exact False.elim (notBoundary boundary)
  · exact decreases

/-- Boundary-free interference leaves one active thread's rank nonincreasing. -/
theorem controlRank_le_on_boundary_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (active :
      ∀ position,
        start ≤ position →
        (execution.state position query).Active)
    (noBoundary :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        ¬ (execution.event position).IsLivenessBoundary) :
    (execution.state time query).controlRank ≤
      (execution.state start query).controlRank := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact Nat.le_refl _
  | succ offset inductionHypothesis =>
      have oneStep :
          (execution.state (start + offset + 1) query).controlRank ≤
            (execution.state (start + offset) query).controlRank :=
        controlRank_le_of_no_scheduled_boundary
          (execution.valid (start + offset))
          query
          (active (start + offset)
            (Nat.le_add_right start offset))
          (fun scheduled =>
            noBoundary (start + offset)
              (Nat.le_add_right start offset)
              scheduled)
      exact Nat.le_trans oneStep inductionHypothesis

/-- A step cannot raise response rank unless the committed owner responds. -/
theorem responseRank_le_of_no_scheduled_response
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (committed : (before query).Committed)
    (noResponse :
      event.thread = query →
        ¬ event.IsResponse) :
    (after query).responseRank ≤
      (before query).responseRank := by
  by_cases owner : event.thread = query
  · subst query
    exact Nat.le_of_lt
      (transition.owner.responseRank_decreases
        committed (noResponse rfl))
  · have unchanged : after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact Nat.le_refl _

/-- Post-commit response rank is nonincreasing on a response-free suffix. -/
theorem responseRank_le_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (committed :
      ∀ position,
        start ≤ position →
        (execution.state position query).Committed)
    (noResponse :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        ¬ (execution.event position).IsResponse) :
    (execution.state time query).responseRank ≤
      (execution.state start query).responseRank := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact Nat.le_refl _
  | succ offset inductionHypothesis =>
      have oneStep :
          (execution.state (start + offset + 1) query).responseRank ≤
            (execution.state (start + offset) query).responseRank :=
        responseRank_le_of_no_scheduled_response
          (execution.valid (start + offset))
          query
          (committed (start + offset)
            (Nat.le_add_right start offset))
          (fun scheduled =>
            noResponse (start + offset)
              (Nat.le_add_right start offset)
              scheduled)
      exact Nat.le_trans oneStep inductionHypothesis

/-- A scheduled response-free post-commit step strictly decreases response rank. -/
theorem responseRank_lt_of_scheduled_nonresponse
    {before after : GlobalState Value}
    {event : TraceEvent Value}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (committed : (before query).Committed)
    (scheduled : event.thread = query)
    (notResponse : ¬ event.IsResponse) :
    (after query).responseRank <
      (before query).responseRank := by
  subst query
  exact transition.owner.responseRank_decreases
    committed notResponse

/-- Weak fairness completes the finite source path after an abstract commit. -/
theorem eventually_response_of_committed
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (committedAtStart :
      (execution.state start query).Committed) :
    ∃ time,
      start ≤ time ∧
        (execution.event time).thread = query ∧
        (execution.event time).IsResponse := by
  by_cases reaches :
      ∃ time,
        start ≤ time ∧
          (execution.event time).thread = query ∧
          (execution.event time).IsResponse
  · exact reaches
  · have noResponse :
        ∀ time,
          start ≤ time →
          (execution.event time).thread = query →
          ¬ (execution.event time).IsResponse := by
      intro time afterStart owner response
      exact reaches ⟨time, afterStart, owner, response⟩
    have committedAlways :
        ∀ time,
          start ≤ time →
          (execution.state time query).Committed := by
      intro time afterStart
      exact execution.committed_on_response_free_suffix
        query afterStart committedAtStart noResponse
    have enabledEventually :
        Liveness.EventuallyAlways (fun time =>
          Enabled (execution.state time) query) :=
      ⟨start, fun time afterStart =>
        (committedAlways time afterStart).active⟩
    have scheduledOften :
        Liveness.InfinitelyOften (fun time =>
          some (execution.event time).thread = some query) :=
      threadFair query enabledEventually
    obtain ⟨first, firstAfterStart, firstScheduledSome⟩ :=
      scheduledOften start
    have firstScheduled :
        (execution.event first).thread = query :=
      Option.some.inj firstScheduledSome
    obtain ⟨second, secondAfterFirst, secondScheduledSome⟩ :=
      scheduledOften (first + 1)
    have secondScheduled :
        (execution.event second).thread = query :=
      Option.some.inj secondScheduledSome
    have firstDecrease :
        (execution.state (first + 1) query).responseRank <
          (execution.state first query).responseRank :=
      responseRank_lt_of_scheduled_nonresponse
        (execution.valid first) query
        (committedAlways first firstAfterStart)
        firstScheduled
        (noResponse first firstAfterStart firstScheduled)
    have between :
        (execution.state second query).responseRank ≤
          (execution.state (first + 1) query).responseRank :=
      execution.responseRank_le_on_response_free_suffix
        query secondAfterFirst
        (fun time afterFirst =>
          committedAlways time (by omega))
        (fun time afterFirst scheduled =>
          noResponse time (by omega) scheduled)
    have secondDecrease :
        (execution.state (second + 1) query).responseRank <
          (execution.state second query).responseRank :=
      responseRank_lt_of_scheduled_nonresponse
        (execution.valid second) query
        (committedAlways second (by omega))
        secondScheduled
        (noResponse second (by omega) secondScheduled)
    have initialBound :
        (execution.state first query).responseRank ≤ 1 :=
      LocalState.responseRank_le_one _
    have impossible : False := by omega
    exact False.elim impossible

/-- Every abstract operation commit is eventually followed by its response. -/
theorem eventually_response_of_operationCommit
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (time : Nat)
    (commit :
      (execution.event time).IsOperationCommit) :
    ∃ responseTime,
      time ≤ responseTime ∧
        (execution.event responseTime).thread =
          (execution.event time).thread ∧
        (execution.event responseTime).IsResponse := by
  have committedAfter :
      (execution.state (time + 1)
        (execution.event time).thread).Committed :=
    (execution.valid time).owner
      |>.committed_after_of_operationCommit commit
  obtain ⟨responseTime, afterCommit, owner, response⟩ :=
    execution.eventually_response_of_committed
      threadFair
      (execution.event time).thread
      (time + 1)
      committedAfter
  exact ⟨responseTime,
    Nat.le_trans (Nat.le_add_right time 1) afterCommit,
    owner, response⟩

/-- A fair globally response-free suffix contains no operation commit. -/
theorem no_operationCommit_on_response_free_suffix
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    ∀ time,
      start ≤ time →
      ¬ (execution.event time).IsOperationCommit := by
  intro time afterStart commit
  obtain ⟨responseTime, afterCommit, _, response⟩ :=
    execution.eventually_response_of_operationCommit
      threadFair time commit
  exact noResponse responseTime
    (Nat.le_trans afterStart afterCommit) response

/--
A continuously active, weakly fairly scheduled thread eventually reaches a
liveness boundary.

Five scheduled non-boundary steps would strictly decrease a rank bounded by
four five times, which is impossible.
-/
theorem eventually_livenessBoundary_of_weakThreadFair
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (continuouslyActive :
      ∀ time,
        start ≤ time →
        (execution.state time query).Active) :
    ∃ time,
      start ≤ time ∧
        (execution.event time).thread = query ∧
        (execution.event time).IsLivenessBoundary := by
  by_cases reaches :
      ∃ time,
        start ≤ time ∧
          (execution.event time).thread = query ∧
          (execution.event time).IsLivenessBoundary
  · exact reaches
  · have noBoundary :
        ∀ time,
          start ≤ time →
          (execution.event time).thread = query →
          ¬ (execution.event time).IsLivenessBoundary := by
      intro time afterStart scheduled boundary
      exact reaches ⟨time, afterStart, scheduled, boundary⟩
    have enabledEventually :
        Liveness.EventuallyAlways (fun time =>
          Enabled (execution.state time) query) :=
      ⟨start, continuouslyActive⟩
    have scheduledOften :
        Liveness.InfinitelyOften (fun time =>
          some (execution.event time).thread = some query) :=
      threadFair query enabledEventually
    obtain ⟨first, firstAfterStart, firstScheduledSome⟩ :=
      scheduledOften start
    obtain ⟨second, secondAfterFirst, secondScheduledSome⟩ :=
      scheduledOften (first + 1)
    obtain ⟨third, thirdAfterSecond, thirdScheduledSome⟩ :=
      scheduledOften (second + 1)
    obtain ⟨fourth, fourthAfterThird, fourthScheduledSome⟩ :=
      scheduledOften (third + 1)
    obtain ⟨fifth, fifthAfterFourth, fifthScheduledSome⟩ :=
      scheduledOften (fourth + 1)
    have firstScheduled : (execution.event first).thread = query :=
      Option.some.inj firstScheduledSome
    have secondScheduled : (execution.event second).thread = query :=
      Option.some.inj secondScheduledSome
    have thirdScheduled : (execution.event third).thread = query :=
      Option.some.inj thirdScheduledSome
    have fourthScheduled : (execution.event fourth).thread = query :=
      Option.some.inj fourthScheduledSome
    have fifthScheduled : (execution.event fifth).thread = query :=
      Option.some.inj fifthScheduledSome
    have firstDecrease :
        (execution.state (first + 1) query).controlRank <
          (execution.state first query).controlRank :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid first) query
        (continuouslyActive first firstAfterStart)
        firstScheduled
        (noBoundary first firstAfterStart firstScheduled)
    have betweenFirstSecond :
        (execution.state second query).controlRank ≤
          (execution.state (first + 1) query).controlRank :=
      execution.controlRank_le_on_boundary_free_suffix
        query secondAfterFirst
        (fun time afterFirst =>
          continuouslyActive time (by omega))
        (fun time afterFirst scheduled =>
          noBoundary time (by omega) scheduled)
    have secondDecrease :
        (execution.state (second + 1) query).controlRank <
          (execution.state second query).controlRank :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid second) query
        (continuouslyActive second (by omega))
        secondScheduled
        (noBoundary second (by omega) secondScheduled)
    have betweenSecondThird :
        (execution.state third query).controlRank ≤
          (execution.state (second + 1) query).controlRank :=
      execution.controlRank_le_on_boundary_free_suffix
        query thirdAfterSecond
        (fun time afterSecond =>
          continuouslyActive time (by omega))
        (fun time afterSecond scheduled =>
          noBoundary time (by omega) scheduled)
    have thirdDecrease :
        (execution.state (third + 1) query).controlRank <
          (execution.state third query).controlRank :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid third) query
        (continuouslyActive third (by omega))
        thirdScheduled
        (noBoundary third (by omega) thirdScheduled)
    have betweenThirdFourth :
        (execution.state fourth query).controlRank ≤
          (execution.state (third + 1) query).controlRank :=
      execution.controlRank_le_on_boundary_free_suffix
        query fourthAfterThird
        (fun time afterThird =>
          continuouslyActive time (by omega))
        (fun time afterThird scheduled =>
          noBoundary time (by omega) scheduled)
    have fourthDecrease :
        (execution.state (fourth + 1) query).controlRank <
          (execution.state fourth query).controlRank :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid fourth) query
        (continuouslyActive fourth (by omega))
        fourthScheduled
        (noBoundary fourth (by omega) fourthScheduled)
    have betweenFourthFifth :
        (execution.state fifth query).controlRank ≤
          (execution.state (fourth + 1) query).controlRank :=
      execution.controlRank_le_on_boundary_free_suffix
        query fifthAfterFourth
        (fun time afterFourth =>
          continuouslyActive time (by omega))
        (fun time afterFourth scheduled =>
          noBoundary time (by omega) scheduled)
    have fifthDecrease :
        (execution.state (fifth + 1) query).controlRank <
          (execution.state fifth query).controlRank :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid fifth) query
        (continuouslyActive fifth (by omega))
        fifthScheduled
        (noBoundary fifth (by omega) fifthScheduled)
    have initialBound :
        (execution.state first query).controlRank ≤ 4 :=
      LocalState.controlRank_le_four _
    have impossible : False := by omega
    exact False.elim impossible

/-- A continuously active fair thread reaches liveness boundaries arbitrarily late. -/
theorem infinitelyOften_livenessBoundary_of_weakThreadFair
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (continuouslyActive :
      ∀ time,
        start ≤ time →
        (execution.state time query).Active) :
    Liveness.InfinitelyOften (fun time =>
      (execution.event time).thread = query ∧
        (execution.event time).IsLivenessBoundary) := by
  intro bound
  let suffixStart := max start bound
  obtain ⟨time, afterSuffix, scheduled, boundary⟩ :=
    execution.eventually_livenessBoundary_of_weakThreadFair
      threadFair query suffixStart
      (fun time afterSuffix =>
        continuouslyActive time
          (Nat.le_trans
            (Nat.le_max_left start bound)
            afterSuffix))
  exact ⟨time,
    Nat.le_trans
      (Nat.le_max_right start bound)
      afterSuffix,
    scheduled, boundary⟩

/-!
The following theorem is the strongest source-only retry statement used by
the later memory proof.  It retains the exact site at every boundary but does
not claim that the boundary is already a CAS attempt.
-/

/--
On a fair response-free suffix, an active thread reaches exact-site CAS or
retry-snapshot boundaries arbitrarily late.
-/
theorem infinitelyOften_retryBoundaryAt_of_active_responseFree
    (execution : InfiniteExecution Value threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (activeAtStart :
      (execution.state start query).Active)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    Liveness.InfinitelyOften (fun time =>
      (execution.event time).thread = query ∧
        ∃ site,
          (execution.event time).RetryBoundaryAt site) := by
  have continuouslyActive :
      ∀ time,
        start ≤ time →
        (execution.state time query).Active := by
    intro time afterStart
    exact execution.active_on_response_free_suffix
      query afterStart activeAtStart noResponse
  have noCommit :=
    execution.no_operationCommit_on_response_free_suffix
      threadFair start noResponse
  intro bound
  obtain ⟨time, afterMaximum, scheduled, boundary⟩ :=
    execution.infinitelyOften_livenessBoundary_of_weakThreadFair
      threadFair query start continuouslyActive (max bound start)
  have afterBound : bound ≤ time :=
    Nat.le_trans (Nat.le_max_left bound start) afterMaximum
  have afterStart : start ≤ time :=
    Nat.le_trans (Nat.le_max_right bound start) afterMaximum
  rcases boundary with retry | commit | response
  · exact ⟨time, afterBound, scheduled, retry⟩
  · exact False.elim (noCommit time afterStart commit)
  · exact False.elim (noResponse time afterStart response)

end InfiniteExecution

end WeakMemory.MSQueue.Source
