import WeakMemory

namespace WeakMemory.Liveness

/-!
# Infinite executions and independent fairness dimensions

The existing Treiber development is intentionally finite.  This module adds a
small, algorithm-independent vocabulary for infinite executions without
changing any of the finite safety semantics.

Three concerns are kept separate:

* scheduling fairness, expressed over enabled threads;
* memory fairness, expressed as prefix-finiteness of `mo` and `fr`; and
* progress of weak compare-and-exchange as a primitive operation.

The separation is essential.  Prefix-finite memory relations constrain which
writes may remain hidden forever, but do not prevent a weak CAS from failing
spuriously forever after comparing equal.
-/

/-- A predicate holds from some finite point onward. -/
def EventuallyAlways (predicate : Nat → Prop) : Prop :=
  ∃ start, ∀ time, start ≤ time → predicate time

/-- A predicate holds at arbitrarily late finite positions. -/
def InfinitelyOften (predicate : Nat → Prop) : Prop :=
  ∀ start, ∃ time, start ≤ time ∧ predicate time

namespace EventuallyAlways

theorem of_forall {predicate : Nat → Prop}
    (holds : ∀ time, predicate time) :
    EventuallyAlways predicate :=
  ⟨0, fun time _ => holds time⟩

theorem mono {left right : Nat → Prop}
    (eventually : EventuallyAlways left)
    (implication : ∀ time, left time → right time) :
    EventuallyAlways right := by
  obtain ⟨start, holds⟩ := eventually
  exact ⟨start, fun time afterStart =>
    implication time (holds time afterStart)⟩

end EventuallyAlways

namespace InfinitelyOften

theorem of_forall {predicate : Nat → Prop}
    (holds : ∀ time, predicate time) :
    InfinitelyOften predicate :=
  fun start => ⟨start, Nat.le_refl start, holds start⟩

theorem mono {left right : Nat → Prop}
    (often : InfinitelyOften left)
    (implication : ∀ time, left time → right time) :
    InfinitelyOften right := by
  intro start
  obtain ⟨time, afterStart, holds⟩ := often start
  exact ⟨time, afterStart, implication time holds⟩

theorem not_of_forall_not {predicate : Nat → Prop}
    (never : ∀ time, ¬ predicate time) :
    ¬ InfinitelyOften predicate := by
  intro often
  obtain ⟨time, _, holds⟩ := often 0
  exact never time holds

end InfinitelyOften

/--
An infinite sequence of valid transitions.

Transition `time` starts in `state time`, emits `action time`, and ends in
`state (time + 1)`.
-/
structure InfiniteRun
    {State : Type} {Action : Type}
    (step : State → Action → State → Prop) where
  state : Nat → State
  action : Nat → Action
  valid :
    ∀ time,
      step (state time) (action time) (state (time + 1))

/--
Weak scheduling fairness: a thread that is continuously enabled from some
point is scheduled at arbitrarily late positions.
-/
def WeakThreadFair
    {State Action Thread : Type}
    {step : State → Action → State → Prop}
    (run : InfiniteRun step)
    (enabled : State → Thread → Prop)
    (actor? : Action → Option Thread) : Prop :=
  ∀ thread,
    EventuallyAlways (fun time => enabled (run.state time) thread) →
    InfinitelyOften (fun time =>
      actor? (run.action time) = some thread)

/--
Prefix-finiteness for relations on an infinite, naturally indexed event set.

Natural event indices below the supplied bound form an explicit finite
container for every predecessor.  Unlike enumeration by a `List`, this does
not require deciding an arbitrary proposition-valued relation.
-/
def PrefixFinite (relation : Nat → Nat → Prop) : Prop :=
  ∀ target,
    ∃ bound,
      ∀ source, relation source target → source < bound

/--
An infinite run together with the two relations used by declarative
weak-memory fairness.

`fromRead` is the conventional `fr` relation.  Other RC11 validity conditions
are deliberately not folded into this generic carrier.
-/
structure InfiniteExecutionGraph
    {State : Type} {Action : Type}
    (step : State → Action → State → Prop)
    extends InfiniteRun step where
  modificationOrder : Nat → Nat → Prop
  fromRead : Nat → Nat → Prop

/--
The memory-fairness condition of prefix-finite modification order and
from-read.  It is intentionally independent of thread and primitive fairness.
-/
def MemoryFair
    {State Action : Type}
    {step : State → Action → State → Prop}
    (execution : InfiniteExecutionGraph step) : Prop :=
  PrefixFinite execution.modificationOrder ∧
    PrefixFinite execution.fromRead

/--
The observable information needed to state progress of weak CAS independently
of any particular algorithm.

`comparesEqual` is about one primitive attempt, while `succeeded` is the
primitive outcome.  Neither field mentions method returns or abstract
operation completion.
-/
structure WeakCASView
    (State Action Thread Site : Type) where
  attempt? : Action → Option (Thread × Site)
  comparesEqual : State → Action → Prop
  succeeded : Action → Prop
  /--
  Identity of the write currently supplying a CAS location.

  This is deliberately stronger than the stored value: an ABA or same-valued
  RMW changes the generation even when pointer equality is restored.
  -/
  generation : State → Site → Nat
  success_is_equal_attempt :
    ∀ {state action},
      succeeded action →
      comparesEqual state action ∧
        ∃ ownerAndSite, attempt? action = some ownerAndSite

namespace WeakCASView

/-- One compare-equal weak-CAS attempt that nevertheless failed. -/
def SpuriousFailureAt
    {State Action Thread Site : Type}
    (view : WeakCASView State Action Thread Site)
    (thread : Thread)
    (site : Site)
    (state : State)
    (action : Action) : Prop :=
  view.attempt? action = some (thread, site) ∧
    view.comparesEqual state action ∧
    ¬ view.succeeded action

end WeakCASView

/--
One CAS site's supplying write is unchanged throughout a suffix.

Generation stability, rather than mere value stability, prevents the fairness
premise from silently spanning ABA or same-valued modifications.
-/
def CASSiteUnmodifiedFrom
    {State Action Thread Site : Type}
    {step : State → Action → State → Prop}
    (view : WeakCASView State Action Thread Site)
    (run : InfiniteRun step)
    (site : Site)
    (start : Nat) : Prop :=
  ∀ time, start ≤ time →
    view.generation (run.state time) site =
      view.generation (run.state start) site

/--
Primitive weak-CAS justice.

If one thread performs compare-equal attempts arbitrarily late while the
supplying write at that CAS site is unchanged, one such attempt eventually
succeeds.  It is non-circular: method responses and system progress do not
occur in the definition.
-/
def WeakCASJustice
    {State Action Thread Site : Type}
    {step : State → Action → State → Prop}
    (view : WeakCASView State Action Thread Site)
    (run : InfiniteRun step) : Prop :=
  ∀ thread site start,
    CASSiteUnmodifiedFrom view run site start →
    InfinitelyOften (fun time =>
      view.attempt? (run.action time) = some (thread, site) ∧
        view.comparesEqual (run.state time) (run.action time)) →
    ∃ time,
      start ≤ time ∧
        view.attempt? (run.action time) = some (thread, site) ∧
        view.succeeded (run.action time)

/-- System-wide primitive progress: successful CAS actions occur forever. -/
def CASSystemProgress
    {State Action Thread Site : Type}
    {step : State → Action → State → Prop}
    (view : WeakCASView State Action Thread Site)
    (run : InfiniteRun step) : Prop :=
  InfinitelyOften (fun time => view.succeeded (run.action time))

end WeakMemory.Liveness
