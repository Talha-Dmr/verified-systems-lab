import WeakMemory.TreiberC11V1Infinite
import WeakMemory.TreiberC11V1LivenessControl

namespace WeakMemory.TreiberC11V1

/-!
# Scheduling fairness reaches source liveness boundaries

The source control graph has a uniformly bounded amount of straight-line
local work between liveness-relevant events.  This module lifts that finite
fact to an infinite global execution: a continuously active, weakly fairly
scheduled thread must eventually emit a CAS attempt, a decisive load, or a
method response.
-/

namespace InfiniteExecution

/-- A source thread currently owns an invocation that has not returned. -/
def Enabled
    (state : GlobalState α)
    (thread : ThreadId) : Prop :=
  Active (state thread)

/-- Weak scheduling fairness specialized to the infinite source execution. -/
def WeakThreadFair
    (execution : InfiniteExecution α threadCount) : Prop :=
  Liveness.WeakThreadFair
    execution.toInfiniteRun
    Enabled
    (fun event => some event.thread)

/--
One global step cannot increase an active thread's control rank unless that
thread emits a liveness boundary.
-/
theorem controlRank_le_of_no_scheduled_boundary
    {before after : GlobalState α}
    {event : TraceEvent α}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : Active (before query))
    (noBoundary :
      event.thread = query →
        ¬ event.IsLivenessBoundary) :
    controlRank (after query) ≤
      controlRank (before query) := by
  by_cases owner : event.thread = query
  · subst query
    rcases
        transition.owner
          |>.livenessBoundary_or_controlRank_decreases
            active with boundary | decrease
    · exact False.elim ((noBoundary rfl) boundary)
    · exact Nat.le_of_lt decrease
  · have unchanged :
        after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact Nat.le_refl _

/-- A scheduled non-boundary step of an active thread strictly decreases rank. -/
theorem controlRank_lt_of_scheduled_nonboundary
    {before after : GlobalState α}
    {event : TraceEvent α}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : Active (before query))
    (scheduled : event.thread = query)
    (notBoundary : ¬ event.IsLivenessBoundary) :
    controlRank (after query) <
      controlRank (before query) := by
  subst query
  rcases
      transition.owner
        |>.livenessBoundary_or_controlRank_decreases
          active with boundary | decrease
  · exact False.elim (notBoundary boundary)
  · exact decrease

/--
A returning state is preserved until its owner emits the mandatory response.
-/
theorem returning_preserved_of_no_scheduled_response
    {before after : GlobalState α}
    {event : TraceEvent α}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (returning : Returning (before query))
    (noResponse :
      event.thread = query →
        ¬ event.IsResponse) :
    Returning (after query) := by
  by_cases owner : event.thread = query
  · subst query
    have response :
        event.IsResponse :=
      transition.owner.response_of_returning returning
    exact False.elim ((noResponse rfl) response)
  · have unchanged :
        after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact returning

/-- A non-response global step preserves activity of every active thread. -/
theorem active_preserved_of_not_response
    {before after : GlobalState α}
    {event : TraceEvent α}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (active : Active (before query))
    (notResponse : ¬ event.IsResponse) :
    Active (after query) := by
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
    (execution : InfiniteExecution α threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      Active (execution.state start query))
    (noResponse :
      ∀ position,
        start ≤ position →
        ¬ (execution.event position).IsResponse) :
    Active (execution.state time query) := by
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

/-- A returning state persists across a suffix with no response by its owner. -/
theorem returning_on_response_free_suffix
    (execution : InfiniteExecution α threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      Returning (execution.state start query))
    (noResponse :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        ¬ (execution.event position).IsResponse) :
    Returning (execution.state time query) := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact initial
  | succ offset inductionHypothesis =>
      exact
        returning_preserved_of_no_scheduled_response
          (execution.valid (start + offset))
          query
          inductionHypothesis
          (fun scheduled =>
            noResponse (start + offset)
              (Nat.le_add_right start offset)
              scheduled)

/--
On a suffix where one thread stays active and never emits a liveness boundary,
its control rank is nonincreasing across arbitrary global interference.
-/
theorem controlRank_le_on_boundary_free_suffix
    (execution : InfiniteExecution α threadCount)
    (query : ThreadId)
    {start time : Nat}
    (afterStart : start ≤ time)
    (active :
      ∀ position,
        start ≤ position →
        Active (execution.state position query))
    (noBoundary :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        ¬ (execution.event position).IsLivenessBoundary) :
    controlRank (execution.state time query) ≤
      controlRank (execution.state start query) := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact Nat.le_refl _
  | succ offset inductionHypothesis =>
      have oneStep :
          controlRank
              (execution.state (start + offset + 1) query) ≤
            controlRank
              (execution.state (start + offset) query) :=
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

/--
A continuously active, weakly fairly scheduled thread eventually reaches a
liveness boundary.

The proof uses three later scheduling positions.  If none were a boundary,
the thread's rank would strictly decrease three times even though every rank
is at most two.
-/
theorem eventually_livenessBoundary_of_weakThreadFair
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (continuouslyActive :
      ∀ time,
        start ≤ time →
        Active (execution.state time query)) :
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
      exact reaches
        ⟨time, afterStart, scheduled, boundary⟩
    have enabledEventually :
        Liveness.EventuallyAlways (fun time =>
          Enabled (execution.state time) query) :=
      ⟨start, continuouslyActive⟩
    have scheduledOften :
        Liveness.InfinitelyOften (fun time =>
          some (execution.event time).thread =
            some query) :=
      threadFair query enabledEventually
    obtain ⟨first, firstAfterStart, firstScheduledSome⟩ :=
      scheduledOften start
    have firstScheduled :
        (execution.event first).thread = query :=
      Option.some.inj firstScheduledSome
    obtain ⟨second, secondAfterFirst,
        secondScheduledSome⟩ :=
      scheduledOften (first + 1)
    have secondScheduled :
        (execution.event second).thread = query :=
      Option.some.inj secondScheduledSome
    obtain ⟨third, thirdAfterSecond,
        thirdScheduledSome⟩ :=
      scheduledOften (second + 1)
    have thirdScheduled :
        (execution.event third).thread = query :=
      Option.some.inj thirdScheduledSome
    have firstDecrease :
        controlRank
              (execution.state (first + 1) query) <
            controlRank
              (execution.state first query) :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid first)
        query
        (continuouslyActive first firstAfterStart)
        firstScheduled
        (noBoundary first firstAfterStart firstScheduled)
    have betweenFirstSecond :
        controlRank (execution.state second query) ≤
          controlRank
            (execution.state (first + 1) query) :=
      execution.controlRank_le_on_boundary_free_suffix
        query
        (start := first + 1)
        (time := second)
        secondAfterFirst
        (fun time afterFirst =>
          continuouslyActive time (by omega))
        (fun time afterFirst scheduled =>
          noBoundary time (by omega) scheduled)
    have secondDecrease :
        controlRank
              (execution.state (second + 1) query) <
            controlRank
              (execution.state second query) :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid second)
        query
        (continuouslyActive second (by omega))
        secondScheduled
        (noBoundary second (by omega) secondScheduled)
    have betweenSecondThird :
        controlRank (execution.state third query) ≤
          controlRank
            (execution.state (second + 1) query) :=
      execution.controlRank_le_on_boundary_free_suffix
        query
        (start := second + 1)
        (time := third)
        thirdAfterSecond
        (fun time afterSecond =>
          continuouslyActive time (by omega))
        (fun time afterSecond scheduled =>
          noBoundary time (by omega) scheduled)
    have thirdDecrease :
        controlRank
              (execution.state (third + 1) query) <
            controlRank
              (execution.state third query) :=
      controlRank_lt_of_scheduled_nonboundary
        (execution.valid third)
        query
        (continuouslyActive third (by omega))
        thirdScheduled
        (noBoundary third (by omega) thirdScheduled)
    have initialBound :
        controlRank (execution.state first query) ≤ 2 :=
      controlRank_le_two _
    have impossible : False := by
      omega
    exact False.elim impossible

/--
A thread that remains active forever emits liveness boundaries arbitrarily
late.
-/
theorem infinitelyOften_livenessBoundary_of_weakThreadFair
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (continuouslyActive :
      ∀ time,
        start ≤ time →
        Active (execution.state time query)) :
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
  exact
    ⟨time,
      Nat.le_trans
        (Nat.le_max_right start bound)
        afterSuffix,
      scheduled,
      boundary⟩

/--
Weak thread fairness discharges finite post-commit local progress: a returning
operation eventually emits its response.
-/
theorem eventually_response_of_returning
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (returning :
      Returning (execution.state start query)) :
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
      intro time afterStart scheduled response
      exact reaches
        ⟨time, afterStart, scheduled, response⟩
    have returningAlways :
        ∀ time,
          start ≤ time →
          Returning (execution.state time query) := by
      intro time afterStart
      exact execution.returning_on_response_free_suffix
        query afterStart returning noResponse
    have enabledEventually :
        Liveness.EventuallyAlways (fun time =>
          Enabled (execution.state time) query) := by
      refine ⟨start, ?_⟩
      intro time afterStart
      exact (returningAlways time afterStart).active
    have scheduledOften :
        Liveness.InfinitelyOften (fun time =>
          some (execution.event time).thread =
            some query) :=
      threadFair query enabledEventually
    obtain ⟨time, afterStart, scheduledSome⟩ :=
      scheduledOften start
    have scheduled :
        (execution.event time).thread = query :=
      Option.some.inj scheduledSome
    have ownerReturning :
        Returning
          (execution.state time
            (execution.event time).thread) := by
      simpa [scheduled] using
        returningAlways time afterStart
    have response :
        (execution.event time).IsResponse :=
      (execution.valid time).owner.response_of_returning
        ownerReturning
    exact ⟨time, afterStart, scheduled, response⟩

/--
Every abstract operation commit is followed by a response under weak thread
fairness.
-/
theorem eventually_response_of_operationCommit
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (time : Nat)
    (commit :
      (execution.event time).IsOperationCommit) :
    ∃ responseTime,
      time ≤ responseTime ∧
        (execution.event responseTime).thread =
          (execution.event time).thread ∧
        (execution.event responseTime).IsResponse := by
  have returningAfter :
      Returning
        (execution.state (time + 1)
          (execution.event time).thread) :=
    (execution.valid time).owner
      |>.returning_after_of_operationCommit commit
  obtain ⟨responseTime, afterCommit, owner, response⟩ :=
    execution.eventually_response_of_returning
      threadFair
      (execution.event time).thread
      (time + 1)
      returningAfter
  exact
    ⟨responseTime,
      Nat.le_trans (Nat.le_add_right time 1) afterCommit,
      owner,
      response⟩

/--
On a globally response-free suffix, weak thread fairness excludes every
abstract operation commit.
-/
theorem no_operationCommit_on_response_free_suffix
    (execution : InfiniteExecution α threadCount)
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
  exact
    noResponse responseTime
      (Nat.le_trans afterStart afterCommit)
      response

/-- A response-free suffix therefore contains no successful CAS. -/
theorem no_successfulCAS_on_response_free_suffix
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (start : Nat)
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    ∀ time,
      start ≤ time →
      ¬ (execution.event time).IsSuccessfulCAS := by
  intro time afterStart successful
  exact
    execution.no_operationCommit_on_response_free_suffix
      threadFair start noResponse time afterStart
      (TraceEvent.successfulCAS_is_commit successful)

/--
An active operation on a response-free fair suffix performs CAS attempts
arbitrarily late.

Decisive loads and successful/empty-result commits are impossible on such a
suffix because every commit would eventually produce a response.
-/
theorem infinitelyOften_CASAttempt_of_active_responseFree
    (execution : InfiniteExecution α threadCount)
    (threadFair : execution.WeakThreadFair)
    (query : ThreadId)
    (start : Nat)
    (activeAtStart :
      Active (execution.state start query))
    (noResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.event time).IsResponse) :
    Liveness.InfinitelyOften (fun time =>
      (execution.event time).thread = query ∧
        (execution.event time).IsCASAttempt) := by
  have continuouslyActive :
      ∀ time,
        start ≤ time →
        Active (execution.state time query) := by
    intro time afterStart
    exact execution.active_on_response_free_suffix
      query afterStart activeAtStart noResponse
  have noCommit :=
    execution.no_operationCommit_on_response_free_suffix
      threadFair start noResponse
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
  have afterStart : start ≤ time :=
    Nat.le_trans
      (Nat.le_max_left start bound)
      afterSuffix
  have afterBound : bound ≤ time :=
    Nat.le_trans
      (Nat.le_max_right start bound)
      afterSuffix
  rcases boundary with cas | decisive | response
  · exact ⟨time, afterBound, scheduled, cas⟩
  · exact False.elim
      (noCommit time afterStart
        (TraceEvent.decisiveLoad_is_commit decisive))
  · exact False.elim
      (noResponse time afterStart response)

end InfiniteExecution

end WeakMemory.TreiberC11V1
