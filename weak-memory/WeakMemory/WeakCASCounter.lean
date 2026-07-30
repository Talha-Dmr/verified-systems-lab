import WeakMemory.WeakCASProgress

namespace WeakMemory.WeakCASCounter

/-!
# A second client of the generic weak-CAS progress rule

This file instantiates `WeakMemory.WeakCAS.ProgressRule` for a one-location
increment operation.  It deliberately does not import or mention the Treiber
model.

An invocation records the current counter value as its expected value.  A
mismatching weak-CAS attempt refreshes that expectation, a spurious failure
leaves it unchanged, and a successful attempt increments the counter and
returns from the operation.  Because this is a single-thread minimal model,
an active operation takes one primitive step at every position; scheduling
fairness is therefore built into the choice of trace positions.

For this deliberately small client, the successful CAS transition is also the
method response.  Thus the rule's response-free-implies-no-success obligation
is definitional; the nontrivial client proof is the derivation of arbitrarily
late matching attempts.  This is a reuse and independence case study, not a
second RC11 development or a model of post-CAS return scheduling.
-/

inductive Action where
  | invoke
  | mismatch
  | spurious
  | success
  deriving Repr, DecidableEq

namespace Action

/-- The primitive weak CAS succeeded. -/
def Succeeded : Action → Prop
  | .success => True
  | _ => False

/-- The weak CAS compared equal, whether it succeeded or failed spuriously. -/
def MatchingAttempt : Action → Prop
  | .spurious
  | .success => True
  | _ => False

@[simp] theorem invoke_not_succeeded :
    ¬ Succeeded .invoke := by
  simp [Succeeded]

@[simp] theorem mismatch_not_succeeded :
    ¬ Succeeded .mismatch := by
  simp [Succeeded]

@[simp] theorem spurious_not_succeeded :
    ¬ Succeeded .spurious := by
  simp [Succeeded]

@[simp] theorem success_succeeded :
    Succeeded .success :=
  trivial

@[simp] theorem invoke_not_matching :
    ¬ MatchingAttempt .invoke := by
  simp [MatchingAttempt]

@[simp] theorem mismatch_not_matching :
    ¬ MatchingAttempt .mismatch := by
  simp [MatchingAttempt]

@[simp] theorem spurious_matching :
    MatchingAttempt .spurious :=
  trivial

@[simp] theorem success_matching :
    MatchingAttempt .success :=
  trivial

end Action

/--
The state of a single pending-or-idle increment operation.

The model intentionally has no allocation, pointer reuse, ABA, or
multi-location memory behavior.  It isolates the primitive weak-CAS fairness
dimension in a client that is structurally different from a stack.
-/
structure State where
  value : Nat
  expected : Nat
  pending : Bool
  deriving Repr, DecidableEq

/-- One transition of the weak-CAS increment loop. -/
inductive Step : State → Action → State → Prop where
  | invoke
      (state : State)
      (idle : state.pending = false) :
      Step state .invoke
        { state with
          expected := state.value
          pending := true }
  | mismatch
      (state : State)
      (active : state.pending = true)
      (different : state.expected ≠ state.value) :
      Step state .mismatch
        { state with expected := state.value }
  | spurious
      (state : State)
      (active : state.pending = true)
      (matching : state.expected = state.value) :
      Step state .spurious state
  | success
      (state : State)
      (active : state.pending = true)
      (matching : state.expected = state.value) :
      Step state .success
        { value := state.value + 1
          expected := state.value + 1
          pending := false }

/-- An infinite trace of the increment machine, starting with no pending call. -/
structure Run extends
    Liveness.InfiniteRun (Step : State → Action → State → Prop) where
  initialIdle :
    (state 0).pending = false

namespace Step

/-- The local retry invariant: the operation is pending and compares equal. -/
def RetryInvariant (state : State) : Prop :=
  state.pending = true ∧
    state.expected = state.value

/--
After an active operation takes any non-successful primitive step, the retry
invariant holds.  A mismatch refreshes `expected`; a spurious failure already
compares equal.
-/
theorem retryInvariant_after_failed_active
    {before after : State}
    {action : Action}
    (transition : Step before action after)
    (active : before.pending = true)
    (notSucceeded : ¬ action.Succeeded) :
    RetryInvariant after := by
  cases transition with
  | invoke idle =>
      simp_all
  | mismatch active different =>
      exact ⟨active, rfl⟩
  | spurious active matching =>
      exact ⟨active, matching⟩
  | success active matching =>
      exact False.elim (notSucceeded trivial)

/-- A failed retry step preserves the local retry invariant. -/
theorem retryInvariant_preserved
    {before after : State}
    {action : Action}
    (transition : Step before action after)
    (notSucceeded : ¬ action.Succeeded)
    (invariant : RetryInvariant before) :
    RetryInvariant after :=
  retryInvariant_after_failed_active
    transition invariant.1 notSucceeded

/--
From a state satisfying the retry invariant, a non-successful transition is a
genuine compare-equal weak-CAS attempt.
-/
theorem action_matching_of_retryInvariant
    {before after : State}
    {action : Action}
    (transition : Step before action after)
    (invariant : RetryInvariant before)
    (notSucceeded : ¬ action.Succeeded) :
    action.MatchingAttempt := by
  cases transition with
  | invoke idle =>
      exact False.elim (by
        have := invariant.1
        simp_all)
  | mismatch active different =>
      exact False.elim (different invariant.2)
  | spurious =>
      trivial
  | success =>
      exact False.elim (notSucceeded trivial)

end Step

namespace Run

/--
Once the first failed step of an active response-free suffix has established
the retry invariant, every later state on that suffix retains it.
-/
theorem retryInvariant_on_responseFreeSuffix
    (run : Run)
    {start time : Nat}
    (afterFirst : start + 1 ≤ time)
    (activeAtStart : (run.state start).pending = true)
    (noSuccess :
      ∀ position,
        start ≤ position →
          ¬ (run.action position).Succeeded) :
    Step.RetryInvariant (run.state time) := by
  have firstInvariant :
      Step.RetryInvariant (run.state (start + 1)) :=
    Step.retryInvariant_after_failed_active
      (run.valid start)
      activeAtStart
      (noSuccess start (Nat.le_refl start))
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterFirst
  subst time
  clear afterFirst
  induction offset with
  | zero =>
      simpa using firstInvariant
  | succ offset inductionHypothesis =>
      have failed :
          ¬ (run.action (start + 1 + offset)).Succeeded :=
        noSuccess (start + 1 + offset) (by omega)
      have next :=
        Step.retryInvariant_preserved
          (run.valid (start + 1 + offset))
          failed
          inductionHypothesis
      simpa [Nat.add_assoc] using next

end Run

/-- The generic progress-rule interface exposed by an increment run. -/
def interface
    (run : Run) :
    WeakCAS.ProgressRule.Interface Unit where
  active time _ :=
    (run.state time).pending = true
  response time :=
    (run.action time).Succeeded
  succeeded time :=
    (run.action time).Succeeded
  matchingAttempt _ time :=
    (run.action time).MatchingAttempt

/--
The increment loop discharges both algorithm-specific obligations of the
generic rule.

The first is immediate because the successful CAS is also the method response.
For the second, the first failed step refreshes `expected`; without a success,
the counter cannot leave the retry loop, so every sufficiently late step is a
compare-equal attempt.
-/
theorem progressRuleObligations
    (run : Run) :
    WeakCAS.ProgressRule.Obligations (interface run) := by
  constructor
  · intro start noResponse time afterStart succeeded
    exact noResponse time afterStart succeeded
  · intro thread start activeAtStart noResponse
    have active :
        (run.state start).pending = true :=
      activeAtStart
    have noSuccess :
        ∀ time,
          start ≤ time →
            ¬ (run.action time).Succeeded := by
      intro time afterStart succeeded
      exact noResponse time afterStart succeeded
    intro bound
    let time := max bound (start + 1)
    have afterBound : bound ≤ time :=
      Nat.le_max_left _ _
    have afterFirst : start + 1 ≤ time :=
      Nat.le_max_right _ _
    have invariant :
        Step.RetryInvariant (run.state time) :=
      run.retryInvariant_on_responseFreeSuffix
        afterFirst active noSuccess
    have matching :
        (run.action time).MatchingAttempt :=
      Step.action_matching_of_retryInvariant
        (run.valid time)
        invariant
        (noSuccess time (by omega))
    exact ⟨time, afterBound, matching⟩

/--
Counter-level response progress obtained solely by instantiating the generic
weak-CAS progress theorem.
-/
theorem responseProgress_of_primitiveJustice
    (run : Run)
    (justice :
      WeakCAS.ProgressRule.PrimitiveJustice (interface run)) :
    WeakCAS.ProgressRule.SystemResponseProgress (interface run) :=
  WeakCAS.ProgressRule.systemResponseProgress_of_primitiveJustice
    (interface run)
    (progressRuleObligations run)
    justice

namespace SuccessRich

def initial : State where
  value := 0
  expected := 0
  pending := false

/-- Invoke when idle; otherwise let the compare-equal weak CAS succeed. -/
def scheduled : State → Action
  | ⟨_, _, false⟩ => .invoke
  | ⟨_, _, true⟩ => .success

def advance : State → State
  | ⟨value, _, false⟩ =>
      { value := value
        expected := value
        pending := true }
  | ⟨value, _, true⟩ =>
      { value := value + 1
        expected := value + 1
        pending := false }

def state : Nat → State
  | 0 => initial
  | time + 1 => advance (state time)

def action (time : Nat) : Action :=
  scheduled (state time)

theorem state_aligned (time : Nat) :
    (state time).expected = (state time).value := by
  cases time with
  | zero =>
      rfl
  | succ time =>
      change
        (advance (state time)).expected =
          (advance (state time)).value
      cases state time with
      | mk value expected pending =>
          cases pending <;> rfl

theorem scheduled_step
    (current : State)
    (aligned : current.expected = current.value) :
    Step current (scheduled current) (advance current) := by
  cases current with
  | mk value expected pending =>
      cases pending with
      | false =>
          exact Step.invoke _ rfl
      | true =>
          exact Step.success _ rfl aligned

/-- A concrete infinite trace alternating invocation and successful return. -/
def run : Run where
  state := state
  action := action
  initialIdle := rfl
  valid := by
    intro time
    simpa [state, action] using
      scheduled_step (state time) (state_aligned time)

/-- Every position is a success or is immediately followed by one. -/
theorem success_now_or_next (time : Nat) :
    (run.action time).Succeeded ∨
      (run.action (time + 1)).Succeeded := by
  change
    (scheduled (state time)).Succeeded ∨
      (scheduled (state (time + 1))).Succeeded
  cases equation : state time with
  | mk value expected pending =>
      cases pending with
      | false =>
          right
          simp [state, advance, scheduled, equation, Action.Succeeded]
      | true =>
          left
          simp [scheduled, Action.Succeeded]

/-- Successful increments occur arbitrarily late. -/
theorem successes_infinitelyOften :
    Liveness.InfinitelyOften (fun time =>
      (run.action time).Succeeded) := by
  intro bound
  rcases success_now_or_next bound with success | success
  · exact ⟨bound, Nat.le_refl bound, success⟩
  · exact ⟨bound + 1, by omega, success⟩

/--
The success-rich trace satisfies primitive justice.  In fact, it has no
success-free suffix, which is stronger than what this particular justice
premise requires.
-/
theorem primitiveJustice :
    WeakCAS.ProgressRule.PrimitiveJustice (interface run) := by
  intro thread start noSuccess matchingAttempts
  obtain ⟨time, afterStart, succeeded⟩ :=
    successes_infinitelyOften start
  exact False.elim
    (noSuccess time afterStart succeeded)

/-- The generic theorem applies to the concrete success-rich trace. -/
theorem responseProgress :
    WeakCAS.ProgressRule.SystemResponseProgress (interface run) :=
  responseProgress_of_primitiveJustice run primitiveJustice

@[simp] theorem active_at_one :
    (interface run).active 1 () :=
  rfl

/-- The first concrete increment invocation has a later response. -/
theorem firstInvocationResponds :
    ∃ time,
      1 ≤ time ∧
        (interface run).response time :=
  responseProgress 1 ⟨(), active_at_one⟩

end SuccessRich

namespace AllSpurious

def idle : State where
  value := 0
  expected := 0
  pending := false

def pending : State where
  value := 0
  expected := 0
  pending := true

def state : Nat → State
  | 0 => idle
  | _ + 1 => pending

def action : Nat → Action
  | 0 => .invoke
  | _ + 1 => .spurious

def run : Run where
  state := state
  action := action
  initialIdle := rfl
  valid := by
    intro time
    cases time with
    | zero =>
        exact Step.invoke idle rfl
    | succ time =>
        exact Step.spurious pending rfl rfl

@[simp] theorem active (time : Nat) :
    (interface run).active (time + 1) () :=
  rfl

@[simp] theorem noResponse (time : Nat) :
    ¬ (interface run).response time := by
  cases time <;>
    simp [interface, run, action, Action.Succeeded]

@[simp] theorem noSuccess (time : Nat) :
    ¬ (interface run).succeeded time := by
  cases time <;>
    simp [interface, run, action, Action.Succeeded]

@[simp] theorem matchingAttempt (time : Nat) :
    (interface run).matchingAttempt () (time + 1) := by
  simp [interface, run, action, Action.MatchingAttempt]

theorem matchingAttempts :
    Liveness.InfinitelyOften
      ((interface run).matchingAttempt ()) :=
  fun bound =>
    ⟨bound + 1,
      Nat.le_add_right bound 1,
      matchingAttempt bound⟩

/-- The all-spurious counter trace violates exactly primitive justice. -/
theorem notPrimitiveJustice :
    ¬ WeakCAS.ProgressRule.PrimitiveJustice
        (interface run) := by
  intro justice
  have noSuccessFrom :
      WeakCAS.ProgressRule.NoSuccessFrom
        (interface run) 1 := by
    intro time afterStart
    exact noSuccess time
  obtain ⟨time, _, succeeded⟩ :=
    justice () 1 noSuccessFrom matchingAttempts
  exact noSuccess time succeeded

/-- An active increment never responds on the all-spurious trace. -/
theorem notResponseProgress :
    ¬ WeakCAS.ProgressRule.SystemResponseProgress
        (interface run) := by
  intro progress
  obtain ⟨time, _, response⟩ :=
    progress 1 ⟨(), active 0⟩
  exact noResponse time response

/--
Counter-specific independence result: the algorithmic obligations of the
generic rule are consistent with an infinite all-spurious execution, but
primitive justice and response progress both fail.
-/
theorem obligations_do_not_imply_primitiveJustice_or_progress :
    ∃ candidate : Run,
      WeakCAS.ProgressRule.Obligations (interface candidate) ∧
        ¬ WeakCAS.ProgressRule.PrimitiveJustice
            (interface candidate) ∧
        ¬ WeakCAS.ProgressRule.SystemResponseProgress
            (interface candidate) :=
  ⟨run, progressRuleObligations run,
    notPrimitiveJustice, notResponseProgress⟩

end AllSpurious

end WeakMemory.WeakCASCounter
