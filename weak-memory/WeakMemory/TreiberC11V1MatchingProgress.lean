import WeakMemory.TreiberC11V1CASJustice
import WeakMemory.TreiberC11V1Progress
import WeakMemory.TreiberC11V1RetrySeed

namespace WeakMemory.TreiberC11V1

/-!
# From a refreshed retry seed to compare-equal attempts

This module lifts the finite retry-seed facts through a globally interleaved
source execution.  It remains parametric in the memory fact that all relevant
late CAS attempts observe one fixed pointer.
-/

namespace InfiniteExecution

/--
One global step preserves a retry seed when the step does not commit and every
CAS by the seeded thread observes the seeded pointer.
-/
theorem retrySeed_preserved
    {before after : GlobalState α}
    {event : TraceEvent α}
    (transition : GlobalStep before event after)
    (query : ThreadId)
    (value : Ptr)
    (seeded : RetrySeed value (before query))
    (notCommit : ¬ event.IsOperationCommit)
    (casObserves :
      event.thread = query →
      event.IsCASAttempt →
        event.casObserved? = some value) :
    RetrySeed value (after query) := by
  by_cases owner : event.thread = query
  · subst query
    rcases
        transition.owner.expectedCAS_or_retrySeed_after
          seeded with expectedCAS | seedAfter
    · obtain ⟨refreshed, observed, refreshedSeed⟩ :=
        transition.owner
          |>.retrySeed_after_of_noncommittingCAS
            expectedCAS.2 notCommit
      have observedValue :=
        casObserves rfl expectedCAS.2
      have sameValue :
          refreshed = value :=
        Option.some.inj
          (observed.symm.trans observedValue)
      subst refreshed
      exact refreshedSeed
    · exact seedAfter
  · have unchanged :
        after query = before query :=
      transition.frame query (Ne.symm owner)
    rw [unchanged]
    exact seeded

/-- A retry seed persists throughout a suitable global suffix. -/
theorem retrySeed_on_suffix
    (execution : InfiniteExecution α threadCount)
    (query : ThreadId)
    (value : Ptr)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      RetrySeed value (execution.state start query))
    (noCommit :
      ∀ position,
        start ≤ position →
        ¬ (execution.event position).IsOperationCommit)
    (casObserves :
      ∀ position,
        start ≤ position →
        (execution.event position).thread = query →
        (execution.event position).IsCASAttempt →
        (execution.event position).casObserved? =
          some value) :
    RetrySeed value (execution.state time query) := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      exact initial
  | succ offset inductionHypothesis =>
      exact
        retrySeed_preserved
          (execution.valid (start + offset))
          query value inductionHypothesis
          (noCommit (start + offset)
            (Nat.le_add_right start offset))
          (fun scheduled attempt =>
            casObserves (start + offset)
              (Nat.le_add_right start offset)
              scheduled attempt)

end InfiniteExecution

namespace InfiniteRC11Execution

/--
Memory/source progress needed by the retry proof: on every response-free
active suffix, one global write eventually supplies all CAS attempts of the
chosen thread.
-/
def StableSourceProgress
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  ∀ thread start,
    Active (execution.source.state start thread) →
    (∀ time,
      start ≤ time →
        ¬ (execution.source.event time).IsResponse) →
    ∃ stableWrite,
      Liveness.EventuallyAlways (fun time =>
        ((execution.source.event time).thread = thread ∧
          (execution.source.event time).IsCASAttempt) →
        execution.observedWrite time = stableWrite)

/--
Once a thread has a retry seed and all of its later CAS attempts observe the
seeded pointer, arbitrarily late CAS attempts are compare-equal.
-/
theorem infinitelyOften_matchingCAS_of_retrySeed
    (execution : InfiniteRC11Execution α threadCount)
    (query : ThreadId)
    (value : Ptr)
    (start : Nat)
    (initial :
      RetrySeed value
        (execution.source.state start query))
    (noCommit :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsOperationCommit)
    (casObserves :
      ∀ time,
        start ≤ time →
        (execution.source.event time).thread = query →
        (execution.source.event time).IsCASAttempt →
        (execution.source.event time).casObserved? =
          some value)
    (casOften :
      Liveness.InfinitelyOften (fun time =>
        (execution.source.event time).thread = query ∧
          (execution.source.event time).IsCASAttempt)) :
    Liveness.InfinitelyOften
      (execution.MatchingCASAttemptBy query) := by
  intro bound
  obtain ⟨time, afterMaximum, scheduled, attempt⟩ :=
    casOften (max bound start)
  have afterBound : bound ≤ time :=
    Nat.le_trans
      (Nat.le_max_left bound start)
      afterMaximum
  have afterStart : start ≤ time :=
    Nat.le_trans
      (Nat.le_max_right bound start)
      afterMaximum
  have seededAtTime :
      RetrySeed value
        (execution.source.state time query) :=
    execution.source.retrySeed_on_suffix
      query value afterStart initial noCommit casObserves
  have ownerSeeded :
      RetrySeed value
        (execution.source.state time
          (execution.source.event time).thread) := by
    simpa [scheduled] using seededAtTime
  have observed :=
    casObserves time afterStart scheduled attempt
  have matching :
      (execution.source.event time).CASComparesEqual :=
    (execution.source.valid time).owner
      |>.seededCAS_comparesEqual
        ownerSeeded attempt observed
  exact
    ⟨time, afterBound, scheduled, matching⟩

/--
Stable RF-source visibility plus finite retry control yields the
`MatchingAttemptProgress` obligation consumed by primitive justice.
-/
theorem matchingAttemptProgress_of_stableSourceProgress
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (stableSources : execution.StableSourceProgress) :
    execution.MatchingAttemptProgress := by
  intro query start activeAtStart noResponse
  have noCommit :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsOperationCommit :=
    execution.source
      |>.no_operationCommit_on_response_free_suffix
        threadFair start noResponse
  have casOften :
      Liveness.InfinitelyOften (fun time =>
        (execution.source.event time).thread = query ∧
          (execution.source.event time).IsCASAttempt) :=
    execution.source
      |>.infinitelyOften_CASAttempt_of_active_responseFree
        threadFair query start activeAtStart noResponse
  obtain ⟨stableWrite, visibleStart, observesStable⟩ :=
    stableSources query start activeAtStart noResponse
  obtain ⟨first, firstAfterMaximum,
      firstScheduled, firstAttempt⟩ :=
    casOften (max start visibleStart)
  have firstAfterStart : start ≤ first :=
    Nat.le_trans
      (Nat.le_max_left start visibleStart)
      firstAfterMaximum
  have firstAfterVisible : visibleStart ≤ first :=
    Nat.le_trans
      (Nat.le_max_right start visibleStart)
      firstAfterMaximum
  have firstStableSource :
      execution.observedWrite first = stableWrite :=
    observesStable first firstAfterVisible
      ⟨firstScheduled, firstAttempt⟩
  obtain ⟨value, firstObserved, seedAfterFirst⟩ :=
    (execution.source.valid first).owner
      |>.retrySeed_after_of_noncommittingCAS
        firstAttempt
        (noCommit first firstAfterStart)
  have seedForQuery :
      RetrySeed value
        (execution.source.state (first + 1) query) := by
    simpa [firstScheduled] using seedAfterFirst
  obtain ⟨firstOccurrence, firstShape⟩ :=
    TraceEvent.exists_atomic_of_CASAttempt
      firstAttempt
  have firstReadSource :
      execution.readSource firstOccurrence.id =
        some stableWrite := by
    have source :=
      execution.readSource_eq_observedWrite_of_atomic
        first firstOccurrence firstShape
    simpa [firstStableSource] using source
  have firstObservedReadValue :
      (execution.source.event first).casObserved? =
        some firstOccurrence.action.readValue :=
    TraceEvent.casObserved?_eq_readValue_of_atomic
      firstShape firstAttempt
  have firstReadValue :
      firstOccurrence.action.readValue = value :=
    Option.some.inj
      (firstObservedReadValue.symm.trans firstObserved)
  have laterCASObservesValue :
      ∀ time,
        first + 1 ≤ time →
        (execution.source.event time).thread = query →
        (execution.source.event time).IsCASAttempt →
        (execution.source.event time).casObserved? =
          some value := by
    intro time afterFirst scheduled attempt
    have afterVisible : visibleStart ≤ time := by
      omega
    have currentStableSource :
        execution.observedWrite time = stableWrite :=
      observesStable time afterVisible
        ⟨scheduled, attempt⟩
    obtain ⟨occurrence, shape⟩ :=
      TraceEvent.exists_atomic_of_CASAttempt attempt
    have currentReadSource :
        execution.readSource occurrence.id =
          some stableWrite := by
      have source :=
        execution.readSource_eq_observedWrite_of_atomic
          time occurrence shape
      simpa [currentStableSource] using source
    have sameReadValue :
        firstOccurrence.action.readValue =
          occurrence.action.readValue :=
      execution.readValue_eq_of_same_readSource
        first time firstOccurrence occurrence
        firstShape shape stableWrite
        firstReadSource currentReadSource
    have currentObservedReadValue :
        (execution.source.event time).casObserved? =
          some occurrence.action.readValue :=
      TraceEvent.casObserved?_eq_readValue_of_atomic
        shape attempt
    exact
      currentObservedReadValue.trans
        (congrArg some
          (sameReadValue.symm.trans firstReadValue))
  exact
    execution.infinitelyOften_matchingCAS_of_retrySeed
      query value (first + 1) seedForQuery
      (fun time afterFirst =>
        noCommit time (by omega))
      laterCASObservesValue
      casOften

/--
End-to-end source progress once stable-source visibility has been established.
-/
theorem systemResponseProgress_of_stableSourceProgress
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (stableSources : execution.StableSourceProgress)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_matchingAttemptProgress
    threadFair
    (execution.matchingAttemptProgress_of_stableSourceProgress
      threadFair stableSources)
    justice

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
