import WeakMemory.InfiniteExecution

namespace WeakMemory.Liveness

/-!
# Visibility consequence of prefix-finite `fr`

Memory fairness and weak-CAS justice solve different liveness problems.
Prefix-finiteness of `fr` rules out reading forever from a write that has a
fixed later successor.  It does not rule out infinitely many spurious
compare-and-exchange failures after the current write has become visible.

This module records the first implication as a small reusable theorem.  Event
zero is reserved for an initializer and transition `time` has event index
`time + 1`, matching the infinite weak-CAS and RC11 layers.
-/

/--
Only finitely many transition events can be `fr`-predecessors of one fixed
write.
-/
theorem eventually_not_fromRead_to
    {fromRead : Nat → Nat → Prop}
    (prefixFinite : PrefixFinite fromRead)
    (targetWrite : Nat) :
    EventuallyAlways (fun time =>
      ¬ fromRead (time + 1) targetWrite) := by
  obtain ⟨bound, belowBound⟩ := prefixFinite targetWrite
  refine ⟨bound, ?_⟩
  intro time afterBound related
  have eventAfterBound : bound ≤ time + 1 :=
    Nat.le_trans afterBound (Nat.le_add_right time 1)
  exact
    (Nat.not_lt_of_ge eventAfterBound)
      (belowBound (time + 1) related)

/--
The identifiers selected along an infinite run eventually escape every finite
bound.  Non-selected positions impose no identifier obligation.
-/
def SelectedIndicesEscape
    (selected : Nat → Prop)
    (eventIndex : Nat → Nat) : Prop :=
  ∀ bound,
    EventuallyAlways (fun time =>
      selected time →
        bound ≤ eventIndex time)

/--
General visibility theorem for event identifiers that need not coincide with
global transition positions.

This form is needed by source traces containing calls, field accesses, and
responses between numbered atomic occurrences.
-/
theorem eventually_observes_stable_write_at
    {fromRead : Nat → Nat → Prop}
    (prefixFinite : PrefixFinite fromRead)
    (attempt : Nat → Prop)
    (eventIndex : Nat → Nat)
    (indicesEscape :
      SelectedIndicesEscape attempt eventIndex)
    (observedWrite : Nat → Nat)
    (stableWrite : Nat)
    (fromReadTarget : Nat)
    (staleImpliesFromRead :
      ∀ time,
        attempt time →
        observedWrite time ≠ stableWrite →
        fromRead (eventIndex time) fromReadTarget) :
    EventuallyAlways (fun time =>
      attempt time →
        observedWrite time = stableWrite) := by
  obtain ⟨bound, belowBound⟩ :=
    prefixFinite fromReadTarget
  obtain ⟨start, lateIndex⟩ :=
    indicesEscape bound
  refine ⟨start, ?_⟩
  intro time afterStart isAttempt
  by_cases current :
      observedWrite time = stableWrite
  · exact current
  · have related :
        fromRead (eventIndex time) fromReadTarget :=
      staleImpliesFromRead time isAttempt current
    have afterBound :
        bound ≤ eventIndex time :=
      lateIndex time afterStart isAttempt
    exact
      False.elim
        ((Nat.not_lt_of_ge afterBound)
          (belowBound (eventIndex time) related))

/--
If every stale observation of a fixed current write creates an `fr` edge to
that write, prefix-finite `fr` implies that sufficiently late attempts observe
the current write.

The theorem is deliberately silent about CAS outcomes.  Once the current
write is observed, excluding an infinite suffix of spurious failures is the
separate job of primitive weak-CAS justice.
-/
theorem eventually_observes_stable_write
    {fromRead : Nat → Nat → Prop}
    (prefixFinite : PrefixFinite fromRead)
    (attempt : Nat → Prop)
    (observedWrite : Nat → Nat)
    (stableWrite : Nat)
    (staleImpliesFromRead :
      ∀ time,
        attempt time →
        observedWrite time ≠ stableWrite →
        fromRead (time + 1) stableWrite) :
    EventuallyAlways (fun time =>
      attempt time →
        observedWrite time = stableWrite) := by
  exact
    eventually_observes_stable_write_at
      (fromRead := fromRead)
      prefixFinite
      attempt
      (fun time => time + 1)
      (by
        intro bound
        refine ⟨bound, ?_⟩
        intro time afterBound _
        exact
          Nat.le_trans afterBound
            (Nat.le_add_right time 1))
      observedWrite
      stableWrite
      stableWrite
      staleImpliesFromRead

end WeakMemory.Liveness
