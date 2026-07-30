import WeakMemory.TreiberC11V1CASJustice
import WeakMemory.WeakCASProgress

namespace WeakMemory.TreiberC11V1

/-!
# Response progress from matching CAS attempts

This module isolates the final primitive-progress argument from the
memory-visibility proof.  The remaining Treiber-specific obligation is stated
as `MatchingAttemptProgress`: on a response-free suffix, an active operation
must generate compare-equal CAS attempts arbitrarily late.

That obligation is where scheduler fairness, prefix-finite `fr`, RC11 value
agreement, and the finite push/pop retry control flow meet.  Primitive justice
then turns one of those attempts into a success, and finite post-commit local
progress turns the success into a method response.
-/

namespace InfiniteRC11Execution

/-- The Treiber execution viewed through the reusable weak-CAS progress rule. -/
def progressRuleInterface
    (execution : InfiniteRC11Execution α threadCount) :
    WeakCAS.ProgressRule.Interface ThreadId where
  active time thread :=
    Active (execution.source.state time thread)
  response time :=
    (execution.source.event time).IsResponse
  succeeded time :=
    (execution.source.event time).IsSuccessfulCAS
  matchingAttempt thread time :=
    execution.MatchingCASAttemptBy thread time

/-- From every state containing an active call, some later method responds. -/
def SystemResponseProgress
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  ∀ start,
    (∃ thread,
      Active (execution.source.state start thread)) →
    ∃ time,
      start ≤ time ∧
        (execution.source.event time).IsResponse

/--
The algorithmic/memory obligation consumed by primitive weak-CAS justice.
-/
def MatchingAttemptProgress
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  ∀ thread start,
    Active (execution.source.state start thread) →
    (∀ time,
      start ≤ time →
        ¬ (execution.source.event time).IsResponse) →
    Liveness.InfinitelyOften
      (execution.MatchingCASAttemptBy thread)

/--
Once response-free active suffixes contain arbitrarily late compare-equal
attempts, weak scheduling fairness and primitive justice imply system-wide
method progress.
-/
theorem systemResponseProgress_of_matchingAttemptProgress
    (execution : InfiniteRC11Execution α threadCount)
    (threadFair : execution.source.WeakThreadFair)
    (matchingProgress :
      execution.MatchingAttemptProgress)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress := by
  change
    WeakCAS.ProgressRule.SystemResponseProgress
      execution.progressRuleInterface
  apply
    WeakCAS.ProgressRule.systemResponseProgress_of_primitiveJustice
      execution.progressRuleInterface
  · constructor
    · intro start noResponse
      change execution.NoSuccessfulCASFrom start
      exact
        execution.source
          |>.no_successfulCAS_on_response_free_suffix
            threadFair start noResponse
    · intro thread start activeAtStart noResponse
      exact
        matchingProgress thread start
          activeAtStart noResponse
  · intro thread start noSuccessfulCAS matching
    obtain ⟨time, afterStart, _, successful⟩ :=
      justice thread start noSuccessfulCAS matching
    exact ⟨time, afterStart, successful⟩

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
