import WeakMemory.WeakCASSiteProgress

namespace WeakMemory.WeakCAS

/-!
# Reusable weak-CAS progress rule

The abstract rule below separates three algorithm-independent observations:

* an active operation is represented by an owner thread;
* a response-free suffix has no successful primitive CAS; and
* the active owner makes compare-equal attempts arbitrarily late.

Primitive justice rules out that suffix.  Concrete machines discharge the two
suffix obligations from their scheduler, memory, and control-flow semantics.

The interface is intentionally system-wide and single-site: it does not index
attempts or successes by a CAS location.  This is exact for the Treiber
`head` and the one-location counter client.  A multi-site application should
add a site index (or prove a reduction to one logical site) instead of
silently reading this theorem as per-site justice.
-/

namespace ProgressRule

/-- Observable predicates needed by the single-site system-progress argument. -/
structure Interface (Thread : Type) where
  active : Nat → Thread → Prop
  response : Nat → Prop
  succeeded : Nat → Prop
  matchingAttempt : Thread → Nat → Prop

/-- No primitive success occurs at or after `start`. -/
def NoSuccessFrom
    (system : Interface Thread)
    (start : Nat) : Prop :=
  ∀ time,
    start ≤ time →
      ¬ system.succeeded time

/--
Primitive weak-CAS justice for one logical site, stated without any
method-response or abstract progress predicate.

The conclusion is a system-wide success because that is all lock-freedom
needs.  It does not identify the successful attempt; multi-site clients need a
site-indexed refinement.
-/
def PrimitiveJustice
    (system : Interface Thread) : Prop :=
  ∀ thread start,
    NoSuccessFrom system start →
    Liveness.InfinitelyOften
      (system.matchingAttempt thread) →
    ∃ time,
      start ≤ time ∧
        system.succeeded time

/-- From every state with an active owner, some later method responds. -/
def SystemResponseProgress
    (system : Interface Thread) : Prop :=
  ∀ start,
    (∃ thread, system.active start thread) →
    ∃ time,
      start ≤ time ∧
        system.response time

/--
The scheduler-, memory-, and algorithm-specific obligations consumed by the
generic primitive-justice rule.
-/
structure Obligations
    (system : Interface Thread) : Prop where
  noSuccess_on_responseFreeSuffix :
    ∀ start,
      (∀ time,
        start ≤ time →
          ¬ system.response time) →
      NoSuccessFrom system start
  matchingAttempts_on_responseFreeSuffix :
    ∀ thread start,
      system.active start thread →
      (∀ time,
        start ≤ time →
          ¬ system.response time) →
      Liveness.InfinitelyOften
        (system.matchingAttempt thread)

/-!
## Conservative embedding into the site-indexed rule

The original interface remains available to existing clients.  Its single
logical location is represented by `Unit`, and the public theorem below is
derived from the site-indexed theorem.  Thus the multi-location rule is a
conservative generalization rather than a parallel proof path.
-/

namespace Interface

/-- Regard a single-site interface as a site-indexed interface over `Unit`. -/
def toSiteIndexed
    (system : Interface Thread) :
    SiteProgressRule.Interface Thread Unit where
  active := system.active
  response := system.response
  succeededAt _ := system.succeeded
  modifiedAt _ := system.succeeded
  success_is_modification _ _ succeeded := succeeded
  matchingAttemptAt thread _ := system.matchingAttempt thread

end Interface

namespace Obligations

/-- Single-site suffix obligations discharge the indexed obligation at `()`. -/
theorem toSiteIndexed
    {system : Interface Thread}
    (obligations : Obligations system) :
    SiteProgressRule.Obligations system.toSiteIndexed := by
  constructor
  intro start active noResponse
  obtain ⟨thread, activeAtStart⟩ := active
  exact
    ⟨thread, start, Nat.le_refl start, (),
      obligations.noSuccess_on_responseFreeSuffix
        start noResponse,
      obligations.matchingAttempts_on_responseFreeSuffix
        thread start activeAtStart noResponse⟩

end Obligations

/-- Single-site primitive justice gives justice at the unique indexed site. -/
theorem primitiveJustice_toSiteIndexed
    {system : Interface Thread}
    (justice : PrimitiveJustice system) :
    SiteProgressRule.PrimitiveJustice system.toSiteIndexed := by
  intro _ thread start noSuccess matching
  exact justice thread start noSuccess matching

/-- Justice at the unique indexed site recovers single-site justice. -/
theorem primitiveJustice_ofSiteIndexed
    {system : Interface Thread}
    (justice :
      SiteProgressRule.PrimitiveJustice system.toSiteIndexed) :
    PrimitiveJustice system := by
  intro thread start noSuccess matching
  exact justice () thread start noSuccess matching

/-- The justice contracts agree exactly under the `Unit` embedding. -/
theorem primitiveJustice_iff_siteIndexed
    (system : Interface Thread) :
    PrimitiveJustice system ↔
      SiteProgressRule.PrimitiveJustice system.toSiteIndexed :=
  ⟨primitiveJustice_toSiteIndexed,
    primitiveJustice_ofSiteIndexed⟩

/-- System response progress is unchanged by the `Unit` site embedding. -/
theorem systemResponseProgress_iff_siteIndexed
    (system : Interface Thread) :
    SystemResponseProgress system ↔
      SiteProgressRule.SystemResponseProgress system.toSiteIndexed := by
  rfl

/--
Generic weak-CAS loop system-progress theorem.

The proof is algorithm-independent: a hypothetical response-free active
suffix supplies both a no-success suffix and arbitrarily late compare-equal
attempts, contradicting primitive justice.
-/
theorem systemResponseProgress_of_primitiveJustice
    (system : Interface Thread)
    (obligations : Obligations system)
    (justice : PrimitiveJustice system) :
    SystemResponseProgress system :=
  (systemResponseProgress_iff_siteIndexed system).mpr
    (SiteProgressRule.systemResponseProgress_of_siteJustice
      system.toSiteIndexed
      obligations.toSiteIndexed
      (primitiveJustice_toSiteIndexed justice))

end ProgressRule

/-!
# A one-location progress core for weak compare-and-exchange

This module gives an infinite transition system for one weak-CAS location.
The identity of the write supplying the current value is tracked separately
from the value itself.  Consequently, fairness cannot mistake ABA or a
same-valued RMW for an unmodified location.

The all-spurious execution at the end is the first negative result of the
liveness development.  It is:

* a valid infinite execution;
* fair to its only enabled thread;
* memory-fair because its run-derived `mo` and `fr` are prefix-finite;
* supplied by the initializer through `rf` at every attempt; and
* devoid of every successful CAS.

Thus thread fairness plus memory fairness does not imply weak-CAS progress.
-/

inductive ProgramCounter where
  | retry
  | done
  deriving Repr, DecidableEq

structure Local (Value : Type) where
  pc : ProgramCounter
  expected : Value
  desired : Value
  deriving Repr, DecidableEq

/--
State of one weak-CAS location and a fixed finite family of client threads.

`headWrite = 0` denotes the implicit initializer.  A successful dynamic CAS
replaces it with that action's positive event identifier.
-/
structure State (Value : Type) (threadCount : Nat) where
  head : Value
  headWrite : Nat
  locals : Fin threadCount → Local Value

namespace State

def updateExpected
    (state : State Value threadCount)
    (thread : Fin threadCount)
    (observed : Value) :
    State Value threadCount :=
  { state with
    locals := fun query =>
      if query = thread then
        { state.locals thread with expected := observed }
      else
        state.locals query }

def commit
    (state : State Value threadCount)
    (thread : Fin threadCount)
    (eventId : Nat) :
    State Value threadCount :=
  { head := (state.locals thread).desired
    headWrite := eventId
    locals := fun query =>
      if query = thread then
        { state.locals thread with pc := .done }
      else
        state.locals query }

def reactivate
    (state : State Value threadCount)
    (thread : Fin threadCount)
    (expected desired : Value) :
    State Value threadCount :=
  { state with
    locals := fun query =>
      if query = thread then
        { pc := .retry
          expected := expected
          desired := desired }
      else
        state.locals query }

end State

inductive FailureKind where
  | mismatch
  | spurious
  deriving Repr, DecidableEq

inductive Outcome (Value : Type) (threadCount : Nat) where
  | casFailure
      (thread : Fin threadCount)
      (expected observed : Value)
      (kind : FailureKind)
  | casSuccess
      (thread : Fin threadCount)
      (expected desired : Value)
  | reactivate
      (thread : Fin threadCount)
      (expected desired : Value)
  deriving Repr, DecidableEq

/-- A dynamic primitive event with its execution-graph identifier. -/
structure Action (Value : Type) (threadCount : Nat) where
  id : Nat
  outcome : Outcome Value threadCount
  deriving Repr, DecidableEq

namespace Action

def thread : Action Value threadCount → Fin threadCount
  | ⟨_, .casFailure thread ..⟩
  | ⟨_, .casSuccess thread ..⟩
  | ⟨_, .reactivate thread ..⟩ => thread

def expected : Action Value threadCount → Value
  | ⟨_, .casFailure _ expected _ _⟩
  | ⟨_, .casSuccess _ expected _⟩
  | ⟨_, .reactivate _ expected _⟩ => expected

def observed : Action Value threadCount → Value
  | ⟨_, .casFailure _ _ observed _⟩ => observed
  | ⟨_, .casSuccess _ expected _⟩
  | ⟨_, .reactivate _ expected _⟩ => expected

def succeeded : Action Value threadCount → Prop
  | ⟨_, .casFailure ..⟩ => False
  | ⟨_, .casSuccess ..⟩ => True
  | ⟨_, .reactivate ..⟩ => False

def attempt? :
    Action Value threadCount →
      Option (Fin threadCount)
  | ⟨_, .casFailure thread ..⟩
  | ⟨_, .casSuccess thread ..⟩ => some thread
  | ⟨_, .reactivate ..⟩ => none

def isSpuriousFailure : Action Value threadCount → Prop
  | ⟨_, .casFailure _ expected observed .spurious⟩ =>
      expected = observed
  | _ => False

@[simp] theorem failure_not_succeeded
    (id : Nat)
    (thread : Fin threadCount)
    (expected observed : Value)
    (kind : FailureKind) :
    ¬ succeeded
      ⟨id, .casFailure thread expected observed kind⟩ := by
  simp [succeeded]

@[simp] theorem success_succeeded
    (id : Nat)
    (thread : Fin threadCount)
    (expected desired : Value) :
    succeeded
      ⟨id, .casSuccess thread expected desired⟩ :=
  trivial

@[simp] theorem reactivate_not_succeeded
    (id : Nat)
    (thread : Fin threadCount)
    (expected desired : Value) :
    ¬ succeeded
      ⟨id, .reactivate thread expected desired⟩ := by
  simp [succeeded]

end Action

/--
One primitive transition.

A mismatch refreshes the local expected value.  A spurious failure is admitted
only when comparison succeeds and leaves the state unchanged.  A successful
CAS records its event identity as the new supplying write.
-/
inductive Step :
    State Value threadCount →
    Action Value threadCount →
    State Value threadCount →
    Prop where
  | failMismatch
      (state : State Value threadCount)
      (thread : Fin threadCount)
      (eventId : Nat)
      (retrying : (state.locals thread).pc = .retry)
      (mismatch : (state.locals thread).expected ≠ state.head) :
      Step state
        ⟨eventId,
          .casFailure thread
            (state.locals thread).expected
            state.head
            .mismatch⟩
        (state.updateExpected thread state.head)
  | failSpurious
      (state : State Value threadCount)
      (thread : Fin threadCount)
      (eventId : Nat)
      (retrying : (state.locals thread).pc = .retry)
      (matching : (state.locals thread).expected = state.head) :
      Step state
        ⟨eventId,
          .casFailure thread
            (state.locals thread).expected
            state.head
            .spurious⟩
        state
  | succeed
      (state : State Value threadCount)
      (thread : Fin threadCount)
      (eventId : Nat)
      (retrying : (state.locals thread).pc = .retry)
      (matching : (state.locals thread).expected = state.head) :
      Step state
        ⟨eventId,
          .casSuccess thread
            (state.locals thread).expected
            (state.locals thread).desired⟩
        (state.commit thread eventId)
  | reactivate
      (state : State Value threadCount)
      (thread : Fin threadCount)
      (eventId : Nat)
      (desired : Value)
      (done : (state.locals thread).pc = .done) :
      Step state
        ⟨eventId,
          .reactivate thread state.head desired⟩
        (state.reactivate thread state.head desired)

namespace Step

/-- A failed primitive transition does not change the CAS value. -/
theorem head_eq_of_not_succeeded
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (notSucceeded : ¬ action.succeeded) :
    after.head = before.head := by
  cases transition with
  | failMismatch =>
      rfl
  | failSpurious =>
      rfl
  | succeed thread eventId retrying matching =>
      exact False.elim
        (notSucceeded
          (Action.success_succeeded eventId thread
            (before.locals thread).expected
            (before.locals thread).desired))
  | reactivate =>
      rfl

/-- A failed primitive transition does not change the supplying write. -/
theorem headWrite_eq_of_not_succeeded
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (notSucceeded : ¬ action.succeeded) :
    after.headWrite = before.headWrite := by
  cases transition with
  | failMismatch =>
      rfl
  | failSpurious =>
      rfl
  | succeed thread eventId retrying matching =>
      exact False.elim
        (notSucceeded
          (Action.success_succeeded eventId thread
            (before.locals thread).expected
            (before.locals thread).desired))
  | reactivate =>
      rfl

/-- A successful primitive transition installs its own event as generation. -/
theorem headWrite_eq_action_id_of_succeeded
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (succeeded : action.succeeded) :
    after.headWrite = action.id := by
  cases transition with
  | failMismatch =>
      exact False.elim succeeded
  | failSpurious =>
      exact False.elim succeeded
  | succeed =>
      rfl
  | reactivate =>
      exact False.elim succeeded

/-- A non-successful transition cannot disable a retrying thread. -/
theorem enabled_preserved_of_not_succeeded
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (notSucceeded : ¬ action.succeeded)
    (query : Fin threadCount)
    (enabled : (before.locals query).pc = .retry) :
    (after.locals query).pc = .retry := by
  cases transition with
  | failMismatch thread eventId retrying mismatch =>
      by_cases same : query = thread
      · subst query
        simpa [State.updateExpected] using enabled
      · simpa [State.updateExpected, same] using enabled
  | failSpurious =>
      exact enabled
  | succeed thread eventId retrying matching =>
      exact False.elim
        (notSucceeded
          (Action.success_succeeded eventId thread
            (before.locals thread).expected
            (before.locals thread).desired))
  | reactivate thread eventId desired done =>
      by_cases same : query = thread
      · subst query
        have impossible : ProgramCounter.done = .retry :=
          done.symm.trans enabled
        cases impossible
      · simpa [State.reactivate, same] using enabled

/--
After any failed attempt, its owner expects the then-current head value.
-/
theorem owner_expected_eq_head_after_failure
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (notSucceeded : ¬ action.succeeded) :
    (after.locals action.thread).expected = after.head := by
  cases transition with
  | failMismatch thread eventId retrying mismatch =>
      simp [Action.thread, State.updateExpected]
  | failSpurious thread eventId retrying matching =>
      exact matching
  | succeed thread eventId retrying matching =>
      exact False.elim
        (notSucceeded
          (Action.success_succeeded eventId thread
            (before.locals thread).expected
            (before.locals thread).desired))
  | reactivate thread eventId desired done =>
      simp [Action.thread, State.reactivate]

/--
Once a thread's expected value matches a stable head, any failed transition
preserves that equality for the thread.
-/
theorem expected_eq_head_preserved_of_not_succeeded
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (notSucceeded : ¬ action.succeeded)
    (query : Fin threadCount)
    (matching :
      (before.locals query).expected = before.head) :
    (after.locals query).expected = after.head := by
  cases transition with
  | failMismatch thread eventId retrying mismatch =>
      by_cases same : query = thread
      · subst query
        exact False.elim (mismatch matching)
      · simpa [State.updateExpected, same] using matching
  | failSpurious =>
      exact matching
  | succeed thread eventId retrying successMatching =>
      exact False.elim
        (notSucceeded
          (Action.success_succeeded eventId thread
            (before.locals thread).expected
            (before.locals thread).desired))
  | reactivate thread eventId desired done =>
      by_cases same : query = thread
      · subst query
        simp [State.reactivate]
      · simpa [State.reactivate, same] using matching

/--
If the scheduled owner's expected value matches `head`, the emitted attempt
is compare-equal, regardless of whether it succeeds or fails spuriously.
-/
theorem action_comparesEqual_of_owner_expected
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (matching :
      (before.locals action.thread).expected = before.head) :
    action.expected = action.observed := by
  cases transition with
  | failMismatch thread eventId retrying mismatch =>
      exact False.elim (mismatch matching)
  | failSpurious thread eventId retrying failureMatching =>
      exact failureMatching
  | succeed =>
      rfl
  | reactivate =>
      rfl

/-- A retry-enabled scheduled owner emits a genuine CAS attempt. -/
theorem action_is_attempt_of_owner_enabled
    {before after : State Value threadCount}
    {action : Action Value threadCount}
    (transition : Step before action after)
    (enabled :
      (before.locals action.thread).pc = .retry) :
    action.attempt? = some action.thread := by
  cases transition with
  | failMismatch =>
      rfl
  | failSpurious =>
      rfl
  | succeed =>
      rfl
  | reactivate thread eventId desired done =>
      have impossible : ProgramCounter.done = .retry :=
        done.symm.trans enabled
      cases impossible

end Step

/--
An infinite run whose dynamic event identifiers are exactly `time + 1`.
Identifier zero remains reserved for initialization.
-/
structure Run (Value : Type) (threadCount : Nat)
    extends Liveness.InfiniteRun
      (Step :
        State Value threadCount →
        Action Value threadCount →
        State Value threadCount →
        Prop) where
  numbered : ∀ time, (action time).id = time + 1
  initialized : (state 0).headWrite = 0

namespace Run

/--
An invariant preserved by every failed transition holds throughout a suffix
containing no successful CAS.
-/
theorem invariant_on_failure_suffix
    (run : Run Value threadCount)
    (invariant : State Value threadCount → Prop)
    (preserved :
      ∀ {before after action},
        Step before action after →
        ¬ action.succeeded →
        invariant before →
        invariant after)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial : invariant (run.state start))
    (noSuccess :
      ∀ position,
        start ≤ position →
        ¬ (run.action position).succeeded) :
    invariant (run.state time) := by
  obtain ⟨offset, equation⟩ :=
    Nat.exists_eq_add_of_le afterStart
  subst time
  clear afterStart
  induction offset with
  | zero =>
      simpa using initial
  | succ offset inductionHypothesis =>
      have failed :
          ¬ (run.action (start + offset)).succeeded :=
        noSuccess (start + offset) (by omega)
      have next :=
        preserved
          (run.valid (start + offset))
          failed
          inductionHypothesis
      change invariant (run.state (start + offset + 1))
      exact next

theorem head_eq_on_failure_suffix
    (run : Run Value threadCount)
    {start time : Nat}
    (afterStart : start ≤ time)
    (noSuccess :
      ∀ position,
        start ≤ position →
        ¬ (run.action position).succeeded) :
    (run.state time).head = (run.state start).head := by
  apply run.invariant_on_failure_suffix
      (fun state => state.head = (run.state start).head)
      (fun transition failed invariant => ?_)
      afterStart rfl noSuccess
  exact
    (Step.head_eq_of_not_succeeded transition failed).trans
      invariant

theorem headWrite_eq_on_failure_suffix
    (run : Run Value threadCount)
    {start time : Nat}
    (afterStart : start ≤ time)
    (noSuccess :
      ∀ position,
        start ≤ position →
        ¬ (run.action position).succeeded) :
    (run.state time).headWrite =
      (run.state start).headWrite := by
  apply run.invariant_on_failure_suffix
      (fun state =>
        state.headWrite = (run.state start).headWrite)
      (fun transition failed invariant => ?_)
      afterStart rfl noSuccess
  exact
    (Step.headWrite_eq_of_not_succeeded transition failed).trans
      invariant

theorem enabled_on_failure_suffix
    (run : Run Value threadCount)
    (query : Fin threadCount)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      ((run.state start).locals query).pc = .retry)
    (noSuccess :
      ∀ position,
        start ≤ position →
        ¬ (run.action position).succeeded) :
    ((run.state time).locals query).pc = .retry := by
  exact run.invariant_on_failure_suffix
    (fun state => (state.locals query).pc = .retry)
    (fun transition failed enabled =>
      Step.enabled_preserved_of_not_succeeded
        transition failed query enabled)
    afterStart initial noSuccess

theorem expected_eq_head_on_failure_suffix
    (run : Run Value threadCount)
    (query : Fin threadCount)
    {start time : Nat}
    (afterStart : start ≤ time)
    (initial :
      ((run.state start).locals query).expected =
        (run.state start).head)
    (noSuccess :
      ∀ position,
        start ≤ position →
        ¬ (run.action position).succeeded) :
    ((run.state time).locals query).expected =
      (run.state time).head := by
  exact run.invariant_on_failure_suffix
    (fun state =>
      (state.locals query).expected = state.head)
    (fun transition failed matching =>
      Step.expected_eq_head_preserved_of_not_succeeded
        transition failed query matching)
    afterStart initial noSuccess

end Run

def Enabled
    (state : State Value threadCount)
    (thread : Fin threadCount) : Prop :=
  (state.locals thread).pc = .retry

def WeakThreadFair (run : Run Value threadCount) : Prop :=
  Liveness.WeakThreadFair run.toInfiniteRun Enabled
    (fun action => some action.thread)

/-- Initializer or a dynamic successful CAS. -/
def IsWrite
    (run : Run Value threadCount)
    (event : Nat) : Prop :=
  event = 0 ∨
    ∃ time,
      event = (run.action time).id ∧
        (run.action time).succeeded

/--
Every primitive attempt reads from the write currently supplying `head`.
-/
def ReadsFrom
    (run : Run Value threadCount)
    (source target : Nat) : Prop :=
  ∃ time,
    target = (run.action time).id ∧
      source = (run.state time).headWrite

/-- Modification order is event-ID order restricted to writes. -/
def ModificationOrder
    (run : Run Value threadCount)
    (first second : Nat) : Prop :=
  IsWrite run first ∧
    IsWrite run second ∧
    first < second

/-- Standard from-read: `rf⁻¹ ; mo`, excluding an RMW self-edge. -/
def FromRead
    (run : Run Value threadCount)
    (read write : Nat) : Prop :=
  ∃ source,
    ReadsFrom run source read ∧
      ModificationOrder run source write ∧
      read ≠ write

namespace Run

/-- The current supplying-write identifier never exceeds elapsed time. -/
theorem headWrite_le_time
    (run : Run Value threadCount)
    (time : Nat) :
    (run.state time).headWrite ≤ time := by
  induction time with
  | zero =>
      simpa using run.initialized
  | succ time inductionHypothesis =>
      have numbered := run.numbered time
      have transition := run.valid time
      by_cases succeeded :
          (run.action time).succeeded
      · have installed :=
          Step.headWrite_eq_action_id_of_succeeded
            transition succeeded
        rw [installed, numbered]
        exact Nat.le_refl _
      · have unchanged :=
          Step.headWrite_eq_of_not_succeeded
            transition succeeded
        rw [unchanged]
        omega

/-- A read's supplying write strictly precedes its current dynamic event. -/
theorem headWrite_lt_action
    (run : Run Value threadCount)
    (time : Nat) :
    (run.state time).headWrite <
      (run.action time).id := by
  have bounded := run.headWrite_le_time time
  have numbered := run.numbered time
  omega

/-- Every generation stored in a reachable state identifies a real write. -/
theorem headWrite_is_write
    (run : Run Value threadCount)
    (time : Nat) :
    IsWrite run (run.state time).headWrite := by
  induction time with
  | zero =>
      exact Or.inl run.initialized
  | succ time inductionHypothesis =>
      have transition := run.valid time
      by_cases succeeded :
          (run.action time).succeeded
      · have installed :=
          Step.headWrite_eq_action_id_of_succeeded
            transition succeeded
        rw [installed]
        exact Or.inr ⟨time, rfl, succeeded⟩
      · have unchanged :=
          Step.headWrite_eq_of_not_succeeded
            transition succeeded
        rw [unchanged]
        exact inductionHypothesis

/-- A generation change can only be caused by a successful CAS. -/
theorem generation_changes_only_on_success
    (run : Run Value threadCount)
    (time : Nat)
    (changed :
      (run.state (time + 1)).headWrite ≠
        (run.state time).headWrite) :
    (run.action time).succeeded := by
  have transition := run.valid time
  by_cases succeeded :
      (run.action time).succeeded
  · exact succeeded
  · exact False.elim
      (changed
        (Step.headWrite_eq_of_not_succeeded
          transition succeeded))

/-- Every successful CAS changes the supplying-write generation. -/
theorem success_changes_generation
    (run : Run Value threadCount)
    (time : Nat)
    (succeeded : (run.action time).succeeded) :
    (run.state (time + 1)).headWrite ≠
      (run.state time).headWrite := by
  have transition := run.valid time
  have prior := run.headWrite_lt_action time
  have installed :=
    Step.headWrite_eq_action_id_of_succeeded
      transition succeeded
  intro unchanged
  have impossible :
      (run.action time).id =
        (run.state time).headWrite :=
    installed.symm.trans unchanged
  omega

end Run

/-- Every reads-from source in the projected graph is a write. -/
theorem readsFrom_source_is_write
    (edge : ReadsFrom run source target) :
    IsWrite run source := by
  obtain ⟨time, _, sourceEquation⟩ := edge
  rw [sourceEquation]
  exact run.headWrite_is_write time

/-- Projected reads-from edges always point from earlier event IDs. -/
theorem readsFrom_source_precedes_target
    (edge : ReadsFrom run source target) :
    source < target := by
  obtain ⟨time, targetEquation, sourceEquation⟩ := edge
  rw [targetEquation, sourceEquation]
  exact run.headWrite_lt_action time

/-- Each dynamic primitive event has exactly one reads-from source. -/
theorem readsFrom_functional
    (left : ReadsFrom run first target)
    (right : ReadsFrom run second target) :
    first = second := by
  obtain ⟨leftTime, leftTarget, leftSource⟩ := left
  obtain ⟨rightTime, rightTarget, rightSource⟩ := right
  have leftNumbered := run.numbered leftTime
  have rightNumbered := run.numbered rightTime
  have timesEqual : leftTime = rightTime := by
    omega
  subst rightTime
  exact leftSource.trans rightSource.symm

def executionGraph
    (run : Run Value threadCount) :
    Liveness.InfiniteExecutionGraph
      (Step :
        State Value threadCount →
        Action Value threadCount →
        State Value threadCount →
        Prop) where
  toInfiniteRun := run.toInfiniteRun
  modificationOrder := ModificationOrder run
  fromRead := FromRead run

def MemoryFair (run : Run Value threadCount) : Prop :=
  Liveness.MemoryFair (executionGraph run)

def weakCASView
    (Value : Type)
    (threadCount : Nat) :
    Liveness.WeakCASView
      (State Value threadCount)
      (Action Value threadCount)
      (Fin threadCount)
      Unit where
  attempt? action :=
    match action.attempt? with
    | none => none
    | some thread => some (thread, ())
  comparesEqual _ action :=
    action.expected = action.observed
  succeeded :=
    Action.succeeded
  generation state _ :=
    state.headWrite
  success_is_equal_attempt := by
    intro state action success
    cases action with
    | mk id outcome =>
        cases outcome with
        | casFailure thread expected observed kind =>
            exact False.elim success
        | casSuccess thread expected desired =>
            exact ⟨rfl, ⟨(thread, ()), rfl⟩⟩
        | reactivate thread expected desired =>
            exact False.elim success

def WeakCASJustice (run : Run Value threadCount) : Prop :=
  Liveness.WeakCASJustice
    (weakCASView Value threadCount)
    run.toInfiniteRun

def SystemProgress (run : Run Value threadCount) : Prop :=
  ∀ start,
    (∃ thread, Enabled (run.state start) thread) →
    ∃ time,
      start ≤ time ∧
        (run.action time).succeeded

/--
Reusable one-location CAS-loop progress theorem.

If a retrying thread exists on a suffix with no successes, weak thread
fairness schedules it forever.  Its first failed attempt refreshes `expected`;
the unchanged head then makes all later attempts matching, and primitive
weak-CAS justice forces the missing success.
-/
theorem systemProgress_of_weakThreadFair_weakCASJustice
    (run : Run Value threadCount)
    (threadFair : WeakThreadFair run)
    (justice : WeakCASJustice run) :
    SystemProgress run := by
  intro start active
  obtain ⟨thread, enabledAtStart⟩ := active
  by_cases progress :
      ∃ time,
        start ≤ time ∧
          (run.action time).succeeded
  · exact progress
  · have noSuccess :
        ∀ time,
          start ≤ time →
          ¬ (run.action time).succeeded := by
      intro time afterStart succeeded
      exact progress ⟨time, afterStart, succeeded⟩
    have continuouslyEnabled :
        Liveness.EventuallyAlways (fun time =>
          Enabled (run.state time) thread) := by
      refine ⟨start, ?_⟩
      intro time afterStart
      exact run.enabled_on_failure_suffix
        thread afterStart enabledAtStart noSuccess
    have scheduledOften :
        Liveness.InfinitelyOften (fun time =>
          some (run.action time).thread = some thread) :=
      threadFair thread continuouslyEnabled
    obtain ⟨firstTime, firstAfterStart, firstScheduled⟩ :=
      scheduledOften start
    have firstActor :
        (run.action firstTime).thread = thread :=
      Option.some.inj firstScheduled
    have firstFailed :
        ¬ (run.action firstTime).succeeded :=
      noSuccess firstTime firstAfterStart
    have expectedAfterFirst :
        ((run.state (firstTime + 1)).locals thread).expected =
          (run.state (firstTime + 1)).head := by
      have ownerExpected :=
        Step.owner_expected_eq_head_after_failure
          (run.valid firstTime) firstFailed
      simpa [firstActor] using ownerExpected
    have noSuccessAfterFirst :
        ∀ time,
          firstTime + 1 ≤ time →
          ¬ (run.action time).succeeded := by
      intro time afterFirst
      exact noSuccess time (by omega)
    have headUnmodified :
        Liveness.CASSiteUnmodifiedFrom
          (weakCASView Value threadCount)
          run.toInfiniteRun
          ()
          start := by
      intro time afterStart
      exact run.headWrite_eq_on_failure_suffix
        afterStart noSuccess
    have matchingAttempts :
        Liveness.InfinitelyOften (fun time =>
          (weakCASView Value threadCount).attempt?
                (run.action time) =
              some (thread, ()) ∧
            (weakCASView Value threadCount).comparesEqual
              (run.state time) (run.action time)) := by
      intro bound
      obtain ⟨time, afterMaximum, scheduled⟩ :=
        scheduledOften (max bound (firstTime + 1))
      have afterBound : bound ≤ time :=
        Nat.le_trans (Nat.le_max_left _ _) afterMaximum
      have afterFirst : firstTime + 1 ≤ time :=
        Nat.le_trans (Nat.le_max_right _ _) afterMaximum
      have actor :
          (run.action time).thread = thread :=
        Option.some.inj scheduled
      have enabledAtTime :
          Enabled (run.state time) thread :=
        run.enabled_on_failure_suffix
          thread (by omega) enabledAtStart noSuccess
      have ownerEnabled :
          ((run.state time).locals
            (run.action time).thread).pc = .retry := by
        simpa [Enabled, actor] using enabledAtTime
      have isAttempt :=
        Step.action_is_attempt_of_owner_enabled
          (run.valid time) ownerEnabled
      have expectedMatches :
          ((run.state time).locals thread).expected =
            (run.state time).head :=
        run.expected_eq_head_on_failure_suffix
          thread afterFirst expectedAfterFirst
          noSuccessAfterFirst
      have ownerExpectedMatches :
          ((run.state time).locals
            (run.action time).thread).expected =
              (run.state time).head := by
        simpa [actor] using expectedMatches
      have comparesEqual :=
        Step.action_comparesEqual_of_owner_expected
          (run.valid time) ownerExpectedMatches
      refine ⟨time, afterBound, ?_, ?_⟩
      · change
          (match (run.action time).attempt? with
            | none => none
            | some owner => some (owner, ())) =
            some (thread, ())
        rw [isAttempt, actor]
      · exact comparesEqual
    obtain ⟨successTime, successAfterStart, _,
        succeeded⟩ :=
      justice thread () start
        headUnmodified matchingAttempts
    exact False.elim
      (noSuccess successTime successAfterStart succeeded)

/--
Memory fairness remains a separate hypothesis in the full RC11 theorem.  The
minimal core always observes the current head, so its primitive progress proof
uses scheduling and weak-CAS justice directly.
-/
theorem systemProgress_of_all_three
    (run : Run Value threadCount)
    (threadFair : WeakThreadFair run)
    (_memoryFair : MemoryFair run)
    (justice : WeakCASJustice run) :
    SystemProgress run :=
  systemProgress_of_weakThreadFair_weakCASJustice
    run threadFair justice

namespace AllSpurious

abbrev Value := Nat

def onlyThread : Fin 1 :=
  ⟨0, Nat.zero_lt_succ 0⟩

def state : State Value 1 where
  head := 0
  headWrite := 0
  locals _ :=
    { pc := .retry
      expected := 0
      desired := 1 }

def action (time : Nat) : Action Value 1 :=
  ⟨time + 1,
    .casFailure onlyThread 0 0 .spurious⟩

/-- The sole thread repeatedly receives a spurious failure forever. -/
def run : Run Value 1 where
  state _ := state
  action := action
  valid := by
    intro time
    exact Step.failSpurious state onlyThread (time + 1) rfl rfl
  numbered _ := rfl
  initialized := rfl

@[simp] theorem action_thread (time : Nat) :
    (run.action time).thread = onlyThread :=
  rfl

@[simp] theorem action_id (time : Nat) :
    (run.action time).id = time + 1 :=
  rfl

@[simp] theorem action_expected (time : Nat) :
    (run.action time).expected = 0 :=
  rfl

@[simp] theorem action_observed (time : Nat) :
    (run.action time).observed = 0 :=
  rfl

@[simp] theorem action_not_succeeded (time : Nat) :
    ¬ (run.action time).succeeded :=
  Action.failure_not_succeeded
    (time + 1) onlyThread 0 0 .spurious

@[simp] theorem state_headWrite (time : Nat) :
    (run.state time).headWrite = 0 :=
  rfl

/-- Every failed attempt reads from the initializer. -/
theorem readsFrom_initial (time : Nat) :
    ReadsFrom run 0 (time + 1) := by
  exact ⟨time, rfl, rfl⟩

theorem isWrite_iff_initializer (event : Nat) :
    IsWrite run event ↔ event = 0 := by
  constructor
  · intro write
    rcases write with initializer | dynamic
    · exact initializer
    · obtain ⟨time, _, success⟩ := dynamic
      exact False.elim (action_not_succeeded time success)
  · exact Or.inl

theorem modificationOrder_empty (first second : Nat) :
    ¬ ModificationOrder run first second := by
  intro ordered
  have firstIsZero :
      first = 0 :=
    (isWrite_iff_initializer first).mp ordered.1
  have secondIsZero :
      second = 0 :=
    (isWrite_iff_initializer second).mp ordered.2.1
  subst first
  subst second
  exact Nat.lt_irrefl 0 ordered.2.2

theorem fromRead_empty (read write : Nat) :
    ¬ FromRead run read write := by
  intro edge
  obtain ⟨source, _, ordered, _⟩ := edge
  exact modificationOrder_empty source write ordered

/-- The only continuously enabled thread is scheduled at every position. -/
theorem threadFair :
    WeakThreadFair run := by
  intro thread _
  have threadIsOnly : thread = onlyThread :=
    Subsingleton.elim thread onlyThread
  subst thread
  exact Liveness.InfinitelyOften.of_forall
    (fun time => congrArg some (action_thread time))

/--
`mo` and `fr` are empty and therefore prefix-finite.  Infinite `rf` fan-out
from the initializer does not violate declarative memory fairness.
-/
theorem memoryFair :
    MemoryFair run := by
  constructor
  · intro target
    refine ⟨0, ?_⟩
    intro source edge
    exact False.elim
      (modificationOrder_empty source target edge)
  · intro target
    refine ⟨0, ?_⟩
    intro source edge
    exact False.elim (fromRead_empty source target edge)

/-- Compare-equal attempts occur arbitrarily late. -/
theorem matchingAttempts :
    Liveness.InfinitelyOften (fun time =>
      (weakCASView Value 1).attempt? (run.action time) =
          some (onlyThread, ()) ∧
        (weakCASView Value 1).comparesEqual
          (run.state time) (run.action time)) :=
  Liveness.InfinitelyOften.of_forall (fun _ => ⟨rfl, rfl⟩)

/-- The initializer remains the supplying head write forever. -/
theorem headUnmodified :
    Liveness.CASSiteUnmodifiedFrom
      (weakCASView Value 1)
      run.toInfiniteRun
      ()
      0 := by
  intro time _
  rfl

/-- Primitive weak-CAS justice is exactly the missing fairness dimension. -/
theorem notWeakCASJustice :
    ¬ WeakCASJustice run := by
  intro justice
  obtain ⟨time, _, _, success⟩ :=
    justice onlyThread () 0 headUnmodified matchingAttempts
  exact action_not_succeeded time success

/-- The fair scheduler and fair memory still produce no successful CAS. -/
theorem notSystemProgress :
    ¬ SystemProgress run := by
  intro progress
  obtain ⟨time, _, success⟩ :=
    progress 0 ⟨onlyThread, rfl⟩
  exact action_not_succeeded time success

/--
Headline independence theorem: thread fairness and memory fairness together
do not entail either primitive weak-CAS justice or system progress.
-/
theorem threadFair_memoryFair_do_not_imply_progress :
    ∃ candidate : Run Value 1,
      WeakThreadFair candidate ∧
        MemoryFair candidate ∧
        ¬ WeakCASJustice candidate ∧
        ¬ SystemProgress candidate :=
  ⟨run, threadFair, memoryFair,
    notWeakCASJustice, notSystemProgress⟩

end AllSpurious

end WeakMemory.WeakCAS
