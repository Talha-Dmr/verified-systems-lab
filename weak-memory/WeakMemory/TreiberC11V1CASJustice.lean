import WeakMemory.TreiberC11V1InfiniteMemory
import WeakMemory.TreiberC11V1InfiniteControlProgress

namespace WeakMemory.TreiberC11V1

/-!
# Primitive weak-CAS justice for the Treiber source

ISO C permits weak compare-and-exchange to fail spuriously.  Scheduler
fairness and memory fairness therefore do not by themselves exclude a stable
suffix containing infinitely many compare-equal failures.

The contract below talks only about primitive CAS attempts, their comparison,
and their primitive outcome.  It does not mention abstract commits, method
responses, or lock-freedom.
-/

namespace InfiniteRC11Execution

/-- No successful weak CAS occurs at or after one source position. -/
def NoSuccessfulCASFrom
    (execution : InfiniteRC11Execution α threadCount)
    (start : Nat) : Prop :=
  ∀ time,
    start ≤ time →
      ¬ (execution.source.event time).IsSuccessfulCAS

/-- One thread performs a compare-equal weak-CAS attempt. -/
def MatchingCASAttemptBy
    (execution : InfiniteRC11Execution α threadCount)
    (thread : ThreadId)
    (time : Nat) : Prop :=
  (execution.source.event time).thread = thread ∧
    (execution.source.event time).CASComparesEqual

/--
Primitive weak-CAS justice for the single Treiber `head` site.

If the site has no successful modification on a suffix and one thread makes
compare-equal attempts arbitrarily late, one later primitive attempt succeeds.
The conclusion contradicts the stable-suffix premise; equivalently, the
contract excludes precisely such an infinite pure-spurious suffix.
-/
def WeakCASJustice
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  ∀ thread start,
    execution.NoSuccessfulCASFrom start →
    Liveness.InfinitelyOften
      (execution.MatchingCASAttemptBy thread) →
    ∃ time,
      start ≤ time ∧
        (execution.source.event time).thread = thread ∧
        (execution.source.event time).IsSuccessfulCAS

/-- Direct bad-suffix exclusion form of primitive justice. -/
def NoStablePureSpuriousSuffix
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  ∀ thread start,
    execution.NoSuccessfulCASFrom start →
      ¬ Liveness.InfinitelyOften
        (execution.MatchingCASAttemptBy thread)

/-- The justice and bad-suffix-exclusion formulations are equivalent. -/
theorem weakCASJustice_iff_noStablePureSpuriousSuffix
    (execution : InfiniteRC11Execution α threadCount) :
    execution.WeakCASJustice ↔
      execution.NoStablePureSpuriousSuffix := by
  constructor
  · intro justice thread start stable matching
    obtain ⟨time, afterStart, _, successful⟩ :=
      justice thread start stable matching
    exact stable time afterStart successful
  · intro excludes thread start stable matching
    exact
      False.elim
        (excludes thread start stable matching)

/-- Every source-valid successful CAS is a compare-equal attempt by its owner. -/
theorem successfulCAS_is_matchingAttempt
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat)
    (successful :
      (execution.source.event time).IsSuccessfulCAS) :
    execution.MatchingCASAttemptBy
      (execution.source.event time).thread
      time := by
  refine ⟨rfl, ?_⟩
  exact
    (execution.source.valid time).owner
      |>.successfulCAS_comparesEqual successful

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
