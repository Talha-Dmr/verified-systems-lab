import WeakMemory.TreiberC11V1LivenessControl

namespace WeakMemory.TreiberC11V1

/-!
# Expected-value refresh across Treiber retry control

A failed weak CAS copies its observed pointer into the local retry state.  The
small amount of intervening source control preserves that pointer until the
next CAS.  This module records that fact independently of scheduling and RC11
visibility.
-/

namespace TraceEvent

/-- Every CAS attempt is represented by one atomic occurrence. -/
theorem exists_atomic_of_CASAttempt
    {event : TraceEvent α}
    (attempt : event.IsCASAttempt) :
    ∃ occurrence : AtomicOccurrence α,
      event = .atomic occurrence := by
  cases event with
  | atomic occurrence =>
      exact ⟨occurrence, rfl⟩
  | _ =>
      simp [IsCASAttempt] at attempt

/-- A CAS event's observed pointer is its atomic read value. -/
theorem casObserved?_eq_readValue_of_atomic
    {event : TraceEvent α}
    {occurrence : AtomicOccurrence α}
    (eventShape : event = .atomic occurrence)
    (attempt : event.IsCASAttempt) :
    event.casObserved? =
      some occurrence.action.readValue := by
  subst event
  cases occurrence with
  | mk id action =>
      cases action <;>
        simp [IsCASAttempt, casObserved?,
          AtomicAction.readValue] at attempt ⊢

end TraceEvent

/--
The local retry path has been seeded with the pointer that its next CAS will
use as `expected`.
-/
def RetrySeed
    (value : Ptr) : LocalState α → Prop
  | .pushWriting _ _ _ expected
  | .pushing _ _ _ expected =>
      expected = value
  | .popReading _ expected =>
      Ptr.node expected = value
  | .popping _ expected _ _ =>
      Ptr.node expected = value
  | _ =>
      False

namespace LocalStep

/--
A noncommitting CAS attempt refreshes the retry path with exactly the pointer
observed by that attempt.
-/
theorem retrySeed_after_of_noncommittingCAS
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (attempt : event.IsCASAttempt)
    (notCommit : ¬ event.IsOperationCommit) :
    ∃ value,
      event.casObserved? = some value ∧
        RetrySeed value after := by
  cases step <;>
    simp [TraceEvent.IsCASAttempt,
      TraceEvent.IsOperationCommit,
      TraceEvent.casObserved?,
      RetrySeed] at attempt notCommit ⊢

/--
From a seeded retry state, one local step either emits the seeded CAS or
preserves the seed for the following local step.
-/
theorem expectedCAS_or_retrySeed_after
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    {value : Ptr}
    (step : LocalStep thread before event after)
    (seeded : RetrySeed value before) :
    (event.casExpected? = some value ∧
      event.IsCASAttempt) ∨
      RetrySeed value after := by
  cases step <;>
    simp [RetrySeed, TraceEvent.casExpected?,
      TraceEvent.IsCASAttempt] at seeded ⊢ <;>
    simp_all

/-- A seeded CAS that observes the same pointer compares equal. -/
theorem seededCAS_comparesEqual
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    {value : Ptr}
    (step : LocalStep thread before event after)
    (seeded : RetrySeed value before)
    (attempt : event.IsCASAttempt)
    (observed :
      event.casObserved? = some value) :
    event.CASComparesEqual := by
  cases step <;>
    simp [RetrySeed, TraceEvent.IsCASAttempt,
      TraceEvent.CASComparesEqual,
      TraceEvent.casExpected?,
      TraceEvent.casObserved?] at seeded attempt observed ⊢ <;>
    cases value <;>
    simp_all

end LocalStep

end WeakMemory.TreiberC11V1
