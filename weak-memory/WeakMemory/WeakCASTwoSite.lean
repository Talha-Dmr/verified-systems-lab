import WeakMemory.WeakCASProgress

namespace WeakMemory.WeakCASTwoSite

/-!
# A two-site client of the site-indexed weak-CAS progress rule

This small transition system is deliberately independent of Treiber and RC11.
It validates the location-sensitive logical boundary before a larger
multi-location algorithm is added.

Each logical site owns one retrying method.  A `complete` action is both a
successful weak CAS and a method response.  A `backgroundSuccess` is a
successful CAS at an idle site but is not a response of either modeled method.
Consequently, an active method may retry forever at one site while unrelated
successes continue at the other.  Erasing site identities hides precisely that
failure mode.
-/

inductive Site where
  | left
  | right
  deriving Repr, DecidableEq

inductive LocalState where
  | idle
  | retry
  deriving Repr, DecidableEq

structure State where
  status : Site → LocalState

namespace State

def set
    (state : State)
    (site : Site)
    (value : LocalState) : State where
  status query :=
    if query = site then value else state.status query

@[simp] theorem set_same
    (state : State)
    (site : Site)
    (value : LocalState) :
    (state.set site value).status site = value := by
  simp [set]

@[simp] theorem set_other
    (state : State)
    {site query : Site}
    (different : query ≠ site)
    (value : LocalState) :
    (state.set site value).status query = state.status query := by
  simp [set, different]

end State

inductive Action where
  | invoke (site : Site)
  | spurious (site : Site)
  | complete (site : Site)
  | backgroundSuccess (site : Site)
  | stutter
  deriving Repr, DecidableEq

namespace Action

/-- The modeled method responds exactly on its own completing CAS. -/
def IsResponse : Action → Prop
  | .complete _ => True
  | _ => False

/-- A primitive CAS succeeds at the queried logical site. -/
def SucceededAt (query : Site) : Action → Prop
  | .complete site
  | .backgroundSuccess site => site = query
  | _ => False

/-- A retrying owner makes a compare-equal attempt at the queried site. -/
def MatchingAt (query : Site) : Action → Prop
  | .spurious site
  | .complete site => site = query
  | _ => False

/-- Every successful CAS is a modification, including a background one. -/
def ModifiedAt := SucceededAt

/-- Only owner retry attempts count as scheduler service. -/
def actor? : Action → Option Site
  | .spurious site
  | .complete site => some site
  | .invoke _
  | .backgroundSuccess _
  | .stutter => none

theorem actor_eq_some_iff_matchingAt
    (action : Action)
    (site : Site) :
    actor? action = some site ↔
      action.MatchingAt site := by
  cases action <;> simp [actor?, MatchingAt]

end Action

/-- Operational semantics of two independent retry sites. -/
inductive Step : State → Action → State → Prop where
  | invoke
      (state : State)
      (site : Site)
      (idle : state.status site = .idle) :
      Step state (.invoke site) (state.set site .retry)
  | spurious
      (state : State)
      (site : Site)
      (retrying : state.status site = .retry) :
      Step state (.spurious site) state
  | complete
      (state : State)
      (site : Site)
      (retrying : state.status site = .retry) :
      Step state (.complete site) (state.set site .idle)
  | backgroundSuccess
      (state : State)
      (site : Site)
      (idle : state.status site = .idle) :
      Step state (.backgroundSuccess site) state
  | stutter (state : State) :
      Step state .stutter state

namespace Step

/-- A retrying method remains active across every non-response transition. -/
theorem retry_preserved_of_not_response
    {before after : State}
    {action : Action}
    {site : Site}
    (transition : Step before action after)
    (retrying : before.status site = .retry)
    (noResponse : ¬ action.IsResponse) :
    after.status site = .retry := by
  cases transition with
  | invoke actor idle =>
      by_cases same : site = actor
      · subst actor
        simp
      · simpa [State.set, same] using retrying
  | spurious =>
      exact retrying
  | complete =>
      exact False.elim (noResponse trivial)
  | backgroundSuccess =>
      exact retrying
  | stutter =>
      exact retrying

/--
On a non-response step, the primitive cannot succeed at a site whose modeled
owner is retrying.  Background successes remain possible at the other site.
-/
theorem no_modificationAt_of_retrying_not_response
    {before after : State}
    {action : Action}
    {site : Site}
    (transition : Step before action after)
    (retrying : before.status site = .retry)
    (noResponse : ¬ action.IsResponse) :
    ¬ action.ModifiedAt site := by
  cases transition with
  | invoke =>
      simp [Action.ModifiedAt, Action.SucceededAt]
  | spurious =>
      simp [Action.ModifiedAt, Action.SucceededAt]
  | complete =>
      exact False.elim (noResponse trivial)
  | backgroundSuccess actor idle =>
      intro succeeded
      have same : actor = site :=
        succeeded
      subst actor
      rw [retrying] at idle
      cases idle
  | stutter =>
      simp [Action.ModifiedAt, Action.SucceededAt]

end Step

abbrev Run := Liveness.InfiniteRun Step

/-- The scheduler regards a retrying owner as enabled. -/
def enabled (state : State) (site : Site) : Prop :=
  state.status site = .retry

/-- Weak fairness independently schedules both enabled site owners. -/
def WeakThreadFair (run : Run) : Prop :=
  Liveness.WeakThreadFair run enabled Action.actor?

/-- The two-site observations consumed by the generic progress theorem. -/
def interface
    (run : Run) :
    WeakCAS.SiteProgressRule.Interface Site Site where
  active time thread :=
    (run.state time).status thread = .retry
  response time :=
    (run.action time).IsResponse
  succeededAt site time :=
    (run.action time).SucceededAt site
  modifiedAt site time :=
    (run.action time).ModifiedAt site
  success_is_modification _ _ succeeded :=
    succeeded
  matchingAttemptAt thread site time :=
    thread = site ∧
      (run.action time).MatchingAt site

namespace Run

/-- Activity persists throughout a suffix containing no method response. -/
theorem retry_on_responseFreeSuffix
    (run : Run)
    {site : Site}
    {start time : Nat}
    (afterStart : start ≤ time)
    (retrying : (run.state start).status site = .retry)
    (noResponse :
      ∀ position,
        start ≤ position →
          ¬ (run.action position).IsResponse) :
    (run.state time).status site = .retry := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      simpa using retrying
  | succ offset inductionHypothesis =>
      exact
        Step.retry_preserved_of_not_response
          (run.valid (start + offset))
          inductionHypothesis
          (noResponse (start + offset) (by omega))

/--
Weak thread fairness supplies matching attempts at the active owner's own
site, even if unrelated background successes occur at the other site.
-/
theorem matchingAttempts_on_responseFreeSuffix
    (run : Run)
    (threadFair : WeakThreadFair run)
    (thread : Site)
    (start : Nat)
    (activeAtStart :
      (run.state start).status thread = .retry)
    (noResponse :
      ∀ time,
        start ≤ time →
          ¬ (run.action time).IsResponse) :
    Liveness.InfinitelyOften
      ((interface run).matchingAttemptAt thread thread) := by
  have continuouslyEnabled :
      Liveness.EventuallyAlways
        (fun time => enabled (run.state time) thread) := by
    refine ⟨start, ?_⟩
    intro time afterStart
    exact
      run.retry_on_responseFreeSuffix
        afterStart activeAtStart noResponse
  have scheduled :=
    threadFair thread continuouslyEnabled
  exact
    Liveness.InfinitelyOften.mono scheduled (by
      intro time actor
      exact
        ⟨rfl,
          (Action.actor_eq_some_iff_matchingAt
            (run.action time) thread).mp actor⟩)

end Run

/-- The two-site loop discharges the coupled, site-indexed suffix obligation. -/
theorem progressRuleObligations
    (run : Run)
    (threadFair : WeakThreadFair run) :
    WeakCAS.SiteProgressRule.Obligations (interface run) := by
  constructor
  intro start active noResponse
  obtain ⟨thread, activeAtStart⟩ := active
  refine ⟨thread, start, Nat.le_refl start, thread, ?_, ?_⟩
  · intro time afterStart succeeded
    have retrying :
        (run.state time).status thread = .retry :=
      run.retry_on_responseFreeSuffix
        afterStart activeAtStart noResponse
    exact
      Step.no_modificationAt_of_retrying_not_response
        (run.valid time)
        retrying
        (noResponse time afterStart)
        succeeded
  · exact
      run.matchingAttempts_on_responseFreeSuffix
        threadFair thread start activeAtStart noResponse

/-- Conditional system progress for a genuine two-site weak-CAS client. -/
theorem systemResponseProgress_of_siteJustice
    (run : Run)
    (threadFair : WeakThreadFair run)
    (justice :
      WeakCAS.SiteProgressRule.PrimitiveJustice
        (interface run)) :
    WeakCAS.SiteProgressRule.SystemResponseProgress
      (interface run) :=
  WeakCAS.SiteProgressRule.systemResponseProgress_of_siteJustice
    (interface run)
    (progressRuleObligations run threadFair)
    justice

/-! ## A success-rich two-site execution -/

namespace SuccessRich

inductive Phase where
  | bothRetry
  | leftIdle
  | bothIdle
  | rightIdle
  deriving Repr, DecidableEq

def Phase.next : Phase → Phase
  | .bothRetry => .leftIdle
  | .leftIdle => .bothIdle
  | .bothIdle => .rightIdle
  | .rightIdle => .bothRetry

def stateOf : Phase → State
  | .bothRetry =>
      { status := fun _ => .retry }
  | .leftIdle =>
      { status
          | .left => .idle
          | .right => .retry }
  | .bothIdle =>
      { status := fun _ => .idle }
  | .rightIdle =>
      { status
          | .left => .retry
          | .right => .idle }

def actionOf : Phase → Action
  | .bothRetry => .complete .left
  | .leftIdle => .complete .right
  | .bothIdle => .invoke .left
  | .rightIdle => .invoke .right

theorem scheduled_step (phase : Phase) :
    Step (stateOf phase) (actionOf phase)
      (stateOf phase.next) := by
  cases phase with
  | bothRetry =>
      have after :
          (stateOf .bothRetry).set .left .idle =
            stateOf .leftIdle := by
        apply congrArg State.mk
        funext query
        cases query <;> rfl
      have transition :=
        Step.complete (stateOf .bothRetry) .left (by rfl)
      rw [after] at transition
      exact transition
  | leftIdle =>
      have after :
          (stateOf .leftIdle).set .right .idle =
            stateOf .bothIdle := by
        apply congrArg State.mk
        funext query
        cases query <;> rfl
      have transition :=
        Step.complete (stateOf .leftIdle) .right (by rfl)
      rw [after] at transition
      exact transition
  | bothIdle =>
      have after :
          (stateOf .bothIdle).set .left .retry =
            stateOf .rightIdle := by
        apply congrArg State.mk
        funext query
        cases query <;> rfl
      have transition :=
        Step.invoke (stateOf .bothIdle) .left (by rfl)
      rw [after] at transition
      exact transition
  | rightIdle =>
      have after :
          (stateOf .rightIdle).set .right .retry =
            stateOf .bothRetry := by
        apply congrArg State.mk
        funext query
        cases query <;> rfl
      have transition :=
        Step.invoke (stateOf .rightIdle) .right (by rfl)
      rw [after] at transition
      exact transition

def phase : Nat → Phase
  | 0 => .bothRetry
  | time + 1 => (phase time).next

def run : Run where
  state time := stateOf (phase time)
  action time := actionOf (phase time)
  valid time := by
    simpa [phase] using scheduled_step (phase time)

theorem phase_add_four (time : Nat) :
    phase (time + 4) = phase time := by
  change
    ((((phase time).next).next).next).next =
      phase time
  cases phase time <;> rfl

theorem phase_four_mul (index : Nat) :
    phase (4 * index) = .bothRetry := by
  induction index with
  | zero =>
      rfl
  | succ index inductionHypothesis =>
      rw [Nat.mul_succ]
      rw [phase_add_four]
      exact inductionHypothesis

theorem phase_four_mul_add_one (index : Nat) :
    phase (4 * index + 1) = .leftIdle := by
  change (phase (4 * index)).next = .leftIdle
  rw [phase_four_mul]
  rfl

theorem leftSuccesses :
    Liveness.InfinitelyOften
      ((interface run).succeededAt .left) := by
  intro bound
  refine ⟨4 * bound, by omega, ?_⟩
  simp [interface, run, phase_four_mul,
    actionOf, Action.SucceededAt]

theorem rightSuccesses :
    Liveness.InfinitelyOften
      ((interface run).succeededAt .right) := by
  intro bound
  refine ⟨4 * bound + 1, by omega, ?_⟩
  simp [interface, run, phase_four_mul_add_one,
    actionOf, Action.SucceededAt]

theorem primitiveJustice :
    WeakCAS.SiteProgressRule.PrimitiveJustice
      (interface run) := by
  intro site _thread start _noModification _matching
  cases site with
  | left =>
      exact leftSuccesses start
  | right =>
      exact rightSuccesses start

theorem actor_of_succeeded
    (phase : Phase)
    (site : Site)
    (succeeded : (actionOf phase).SucceededAt site) :
    Action.actor? (actionOf phase) = some site := by
  cases phase <;> cases site <;>
    simp [actionOf, Action.SucceededAt, Action.actor?] at succeeded ⊢

theorem threadFair : WeakThreadFair run := by
  intro site _continuouslyEnabled
  cases site with
  | left =>
      exact Liveness.InfinitelyOften.mono
        leftSuccesses (by
          intro time succeeded
          change
            (actionOf (phase time)).SucceededAt .left
              at succeeded
          change
            Action.actor? (actionOf (phase time)) =
              some .left
          exact
            actor_of_succeeded (phase time) .left succeeded)
  | right =>
      exact Liveness.InfinitelyOften.mono
        rightSuccesses (by
          intro time succeeded
          change
            (actionOf (phase time)).SucceededAt .right
              at succeeded
          change
            Action.actor? (actionOf (phase time)) =
              some .right
          exact
            actor_of_succeeded (phase time) .right succeeded)

theorem responseProgress :
    WeakCAS.SiteProgressRule.SystemResponseProgress
      (interface run) :=
  systemResponseProgress_of_siteJustice
    run threadFair primitiveJustice

end SuccessRich

/-! ## Shared alternating schedule for the negative witnesses -/

def alternatingSite (time : Nat) : Site :=
  if time % 2 = 0 then .left else .right

@[simp] theorem alternatingSite_two_mul (index : Nat) :
    alternatingSite (2 * index) = .left := by
  simp [alternatingSite]

@[simp] theorem alternatingSite_two_mul_add_one (index : Nat) :
    alternatingSite (2 * index + 1) = .right := by
  simp [alternatingSite, Nat.add_mod]

namespace AllSpurious

def state : State where
  status _ := .retry

def run : Run where
  state _ := state
  action time := .spurious (alternatingSite time)
  valid time :=
    Step.spurious state (alternatingSite time) rfl

theorem threadFair : WeakThreadFair run := by
  intro site _
  intro bound
  cases site with
  | left =>
      refine ⟨2 * bound, by omega, ?_⟩
      simp [run, Action.actor?]
  | right =>
      refine ⟨2 * bound + 1, by omega, ?_⟩
      simp [run, Action.actor?]

theorem obligations :
    WeakCAS.SiteProgressRule.Obligations (interface run) :=
  progressRuleObligations run threadFair

theorem noModificationAt (site : Site) :
    WeakCAS.SiteProgressRule.NoModificationAtFrom
      (interface run) site 0 := by
  intro time _
  simp [interface, run, Action.ModifiedAt, Action.SucceededAt]

theorem noResponseFromZero :
    WeakCAS.SiteProgressRule.NoResponseFrom
      (interface run) 0 := by
  intro time _
  simp [interface, run, Action.IsResponse]

theorem matchingAt (site : Site) :
    Liveness.InfinitelyOften
      ((interface run).matchingAttemptAt site site) :=
  run.matchingAttempts_on_responseFreeSuffix
    threadFair site 0 rfl noResponseFromZero

/-- Every site has its own stable all-spurious suffix. -/
theorem notPrimitiveJusticeAt (site : Site) :
    ¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
      (interface run) site := by
  intro justice
  obtain ⟨time, afterStart, succeeded⟩ :=
    justice site 0 (noModificationAt site) (matchingAt site)
  exact
    noModificationAt site time afterStart succeeded

theorem notPrimitiveJustice :
    ¬ WeakCAS.SiteProgressRule.PrimitiveJustice
      (interface run) := by
  intro justice
  exact notPrimitiveJusticeAt .left (justice .left)

theorem neitherSiteIsJust :
    (¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
        (interface run) .left) ∧
      (¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
        (interface run) .right) :=
  ⟨notPrimitiveJusticeAt .left,
    notPrimitiveJusticeAt .right⟩

theorem notSystemResponseProgress :
    ¬ WeakCAS.SiteProgressRule.SystemResponseProgress
      (interface run) := by
  intro progress
  obtain ⟨time, _, response⟩ :=
    progress 0 ⟨.left, rfl⟩
  simp [interface, run, Action.IsResponse] at response

/-- Site-wise primitive justice is independent of scheduler obligations. -/
theorem obligations_do_not_imply_justice_or_progress :
    ∃ candidate : Run,
      WeakThreadFair candidate ∧
        WeakCAS.SiteProgressRule.Obligations
          (interface candidate) ∧
        ¬ WeakCAS.SiteProgressRule.PrimitiveJustice
          (interface candidate) ∧
        ¬ WeakCAS.SiteProgressRule.SystemResponseProgress
          (interface candidate) :=
  ⟨run, threadFair, obligations,
    notPrimitiveJustice, notSystemResponseProgress⟩

end AllSpurious

namespace WrongSite

def state : State where
  status
    | .left => .retry
    | .right => .idle

def action (time : Nat) : Action :=
  match alternatingSite time with
  | .left => .spurious .left
  | .right => .backgroundSuccess .right

def run : Run where
  state _ := state
  action := action
  valid time := by
    unfold action
    split
    · exact Step.spurious state .left rfl
    · exact Step.backgroundSuccess state .right rfl

theorem threadFair : WeakThreadFair run := by
  intro site continuouslyEnabled
  cases site with
  | left =>
      intro bound
      refine ⟨2 * bound, by omega, ?_⟩
      simp [run, action, Action.actor?]
  | right =>
      obtain ⟨start, enabledFrom⟩ := continuouslyEnabled
      have enabledAtStart := enabledFrom start (Nat.le_refl start)
      simp [enabled, run, state] at enabledAtStart

theorem obligations :
    WeakCAS.SiteProgressRule.Obligations (interface run) :=
  progressRuleObligations run threadFair

theorem noLeftModification :
    WeakCAS.SiteProgressRule.NoModificationAtFrom
      (interface run) .left 0 := by
  intro time _
  change ¬ (action time).ModifiedAt .left
  unfold action
  split <;> simp [Action.ModifiedAt, Action.SucceededAt]

theorem noResponseFromZero :
    WeakCAS.SiteProgressRule.NoResponseFrom
      (interface run) 0 := by
  intro time _
  simp [interface, run, action]
  split <;> simp [Action.IsResponse]

theorem matchingLeft :
    Liveness.InfinitelyOften
      ((interface run).matchingAttemptAt .left .left) :=
  run.matchingAttempts_on_responseFreeSuffix
    threadFair .left 0 rfl noResponseFromZero

/-- The active left site is stable and purely spurious forever. -/
theorem notPrimitiveJusticeAt_left :
    ¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
      (interface run) .left := by
  intro justice
  obtain ⟨time, afterStart, succeeded⟩ :=
    justice .left 0 noLeftModification matchingLeft
  exact noLeftModification time afterStart succeeded

/-- Recurring background successes make justice true at the right site. -/
theorem primitiveJusticeAt_right :
    WeakCAS.SiteProgressRule.PrimitiveJusticeAt
      (interface run) .right := by
  intro thread start noModification matching
  let time := 2 * start + 1
  refine ⟨time, ?_, ?_⟩
  · dsimp [time]
    omega
  · change (action time).SucceededAt .right
    simp [action, time, Action.SucceededAt]

/-- The active left site violates global justice despite right successes. -/
theorem notPrimitiveJustice :
    ¬ WeakCAS.SiteProgressRule.PrimitiveJustice
      (interface run) := by
  intro justice
  exact notPrimitiveJusticeAt_left (justice .left)

theorem notSystemResponseProgress :
    ¬ WeakCAS.SiteProgressRule.SystemResponseProgress
      (interface run) := by
  intro progress
  obtain ⟨time, _, response⟩ :=
    progress 0 ⟨.left, rfl⟩
  simp [interface, run, action] at response
  split at response <;> simp [Action.IsResponse] at response

/-- Erase site identities in exactly the way the original rule observes. -/
def erasedInterface :
    WeakCAS.ProgressRule.Interface Site where
  active := (interface run).active
  response := (interface run).response
  succeeded time :=
    ∃ site, (interface run).succeededAt site time
  matchingAttempt thread time :=
    ∃ site,
      (interface run).matchingAttemptAt thread site time

/--
After erasing sites, recurring right-site successes make primitive justice
hold vacuously even though the active left loop is purely spurious forever.
-/
theorem erasedPrimitiveJustice :
    WeakCAS.ProgressRule.PrimitiveJustice erasedInterface := by
  intro thread start noSuccess _
  let time := 2 * start + 1
  have afterStart : start ≤ time := by
    dsimp [time]
    omega
  have rightSuccess : erasedInterface.succeeded time := by
    refine ⟨.right, ?_⟩
    simp [interface, run, action, time,
      Action.SucceededAt]
  exact False.elim
    (noSuccess time afterStart rightSuccess)

/--
The original single-site theorem remains sound: its global no-success suffix
obligation rejects this erased execution because right-site successes recur.
-/
theorem notErasedObligations :
    ¬ WeakCAS.ProgressRule.Obligations erasedInterface := by
  intro erasedObligations
  have noResponse :
      ∀ time,
        0 ≤ time →
          ¬ erasedInterface.response time := by
    intro time afterStart
    exact noResponseFromZero time afterStart
  have noSuccess :=
    erasedObligations.noSuccess_on_responseFreeSuffix
      0 noResponse
  have rightSuccess : erasedInterface.succeeded 1 := by
    refine ⟨.right, ?_⟩
    simp [interface, run, action, alternatingSite,
      Action.SucceededAt]
  exact noSuccess 1 (by omega) rightSuccess

theorem notErasedSystemResponseProgress :
    ¬ WeakCAS.ProgressRule.SystemResponseProgress
      erasedInterface := by
  intro progress
  obtain ⟨time, afterStart, response⟩ :=
    progress 0 ⟨.left, rfl⟩
  exact noResponseFromZero time afterStart response

/-- Site erasure therefore loses a progress-relevant distinction. -/
theorem erasure_hides_wrong_site_starvation :
    WeakCAS.ProgressRule.PrimitiveJustice erasedInterface ∧
      ¬ WeakCAS.SiteProgressRule.PrimitiveJustice
        (interface run) ∧
      ¬ WeakCAS.SiteProgressRule.SystemResponseProgress
        (interface run) :=
  ⟨erasedPrimitiveJustice,
    notPrimitiveJustice,
    notSystemResponseProgress⟩

end WrongSite

end WeakMemory.WeakCASTwoSite
