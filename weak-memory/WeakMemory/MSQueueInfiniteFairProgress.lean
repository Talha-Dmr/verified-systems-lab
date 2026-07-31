import WeakMemory.MSQueueInfiniteMatchingProgress

namespace WeakMemory

namespace Liveness.InfinitelyOften

/-!
The queue proof eventually obtains matching attempts whose sites range over a
finite prefix carrier.  This small temporal pigeonhole lemma turns that fact
into one fixed site occurring arbitrarily late.
-/

/-- If events drawn from a finite list occur arbitrarily late, then one fixed
member of that list occurs arbitrarily late. -/
theorem finite_pigeonhole
    {Index : Type}
    (indices : List Index)
    (predicate : Nat → Index → Prop)
    (often :
      Liveness.InfinitelyOften (fun time =>
        ∃ index,
          index ∈ indices ∧ predicate time index)) :
    ∃ index,
      index ∈ indices ∧
        Liveness.InfinitelyOften (fun time =>
          predicate time index) := by
  classical
  induction indices with
  | nil =>
      obtain ⟨time, _, index, member, _⟩ := often 0
      simp at member
  | cons head tail inductionHypothesis =>
      by_cases headOften :
          Liveness.InfinitelyOften (fun time =>
            predicate time head)
      · exact ⟨head, by simp, headOften⟩
      · have eventuallyNotHead :
            ∃ cutoff,
              ∀ time,
                cutoff ≤ time →
                ¬ predicate time head := by
          unfold Liveness.InfinitelyOften at headOften
          obtain ⟨cutoff, noWitness⟩ :=
            Classical.not_forall.mp headOften
          refine ⟨cutoff, ?_⟩
          intro time afterCutoff holds
          apply noWitness
          exact ⟨time, afterCutoff, holds⟩
        obtain ⟨cutoff, noHead⟩ := eventuallyNotHead
        have tailOften :
            Liveness.InfinitelyOften (fun time =>
              ∃ index,
                index ∈ tail ∧ predicate time index) := by
          intro bound
          obtain ⟨time, afterMaximum, index, member, holds⟩ :=
            often (max cutoff bound)
          have afterCutoff : cutoff ≤ time :=
            Nat.le_trans (Nat.le_max_left _ _) afterMaximum
          have afterBound : bound ≤ time :=
            Nat.le_trans (Nat.le_max_right _ _) afterMaximum
          simp only [List.mem_cons] at member
          rcases member with same | inTail
          · subst index
            exact False.elim (noHead time afterCutoff holds)
          · exact ⟨time, afterBound, index, inTail, holds⟩
        obtain ⟨index, inTail, indexOften⟩ :=
          inductionHypothesis tailOften
        exact ⟨index, by simp [inTail], indexOften⟩

end Liveness.InfinitelyOften

namespace MSQueue.Source

/-!
# Fair queue progress obligations

This module discharges the algorithm-facing progress package from three
concrete ingredients: exact finite-prefix structure, weak scheduling fairness,
and selected-site read visibility.  On a hypothetical response-free suffix,
queue-wide modifications first stabilize.  All later reads then observe one
stable assignment, so a continuously active fair thread performs matching
CAS attempts arbitrarily late.  Only finitely many sites are represented at
the stabilization prefix; temporal pigeonhole therefore selects one fixed
stable site.
-/

namespace AtomicAction

/-- Every compare-equal CAS label has an RC11 read component, regardless of
whether the weak CAS succeeds or fails spuriously. -/
theorem isRead_of_isMatchingCAS
    (action : AtomicAction Value)
    (matching : action.IsMatchingCAS) :
    action.access.IsRead := by
  cases action <;>
    simp_all [IsMatchingCAS, casView?, access,
      MultiLocationRC11.Access.IsRead]
  all_goals
    cases ‹Bool› <;> simp_all

end AtomicAction

namespace TraceEvent

/-- A matching queue event exposes its atomic occurrence and its RC11 read
component. -/
theorem atomicRead_of_isMatchingCAS
    {event : TraceEvent Value}
    (matching : event.IsMatchingCAS) :
    ∃ occurrence : AtomicOccurrence Value,
      event = .atomic occurrence ∧
        occurrence.toRC11Atom.IsRead := by
  cases event with
  | atomic occurrence =>
      refine ⟨occurrence, rfl, ?_⟩
      change occurrence.action.access.IsRead
      exact occurrence.action.isRead_of_isMatchingCAS matching
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim matching

end TraceEvent

namespace InfiniteRC11Execution

/-- After a queue-wide stabilization boundary, the site of every later
matching CAS belongs to the finite site list represented at that boundary. -/
theorem matchingCAS_has_representedSite
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start time : Nat)
    (afterStart : start ≤ time)
    (allStable :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site start)
    (matching :
      (execution.source.event time).IsMatchingCAS) :
    ∃ site,
      site ∈ execution.representedSites start ∧
        execution.progressInterface.matchingAttemptAt
          (execution.source.event time).thread site time := by
  obtain ⟨occurrence, event, read⟩ :=
    TraceEvent.atomicRead_of_isMatchingCAS matching
  have represented :=
    execution.site_represented_at_start_of_later_read
      start time afterStart allStable occurrence event read
  have member :=
    (execution.mem_representedSites_iff
      start occurrence.action.site).mpr represented
  refine ⟨occurrence.action.site, member, ?_⟩
  change
    (execution.source.event time).MatchingAttemptAt
      (execution.source.event time).thread
      occurrence.action.site
  rw [event]
  exact ⟨rfl, rfl, by
    simpa [TraceEvent.IsMatchingCAS, event] using matching⟩

/-- Exact structural prefixes, fair scheduling, and selected-site memory
visibility discharge the complete algorithm-specific progress obligation. -/
theorem progressObligations_of_selectedSiteVisibilityFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (visibility : execution.SelectedSiteVisibilityFair) :
    execution.ProgressObligations := by
  classical
  refine {
    progressSite_on_responseFreeSuffix := ?_
  }
  intro start active noResponse
  obtain ⟨owner, activeAtStart⟩ := active
  change (execution.source.state start owner).Active at activeAtStart
  have sourceNoResponse :
      ∀ time,
        start ≤ time →
        ¬ (execution.source.event time).IsResponse := by
    exact noResponse
  obtain ⟨stableCutoff, stableAfterStart, allStable⟩ :=
    execution.eventually_noModification_on_responseFreeSuffix
      schedules threadFair start sourceNoResponse
  obtain ⟨visibilityCutoff, visibleAfterStable, observes⟩ :=
    execution.eventually_allReads_observe_stableValueAt
      visibility stableCutoff allStable
  have visibleAfterStart : start ≤ visibilityCutoff :=
    Nat.le_trans stableAfterStart visibleAfterStable
  have noResponseAfterVisibility :
      ∀ time,
        visibilityCutoff ≤ time →
        ¬ (execution.source.event time).IsResponse := by
    intro time afterVisibility
    exact sourceNoResponse time
      (Nat.le_trans visibleAfterStart afterVisibility)
  have noModificationAfterVisibility :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site visibilityCutoff := by
    intro site time afterVisibility
    exact allStable site time
      (Nat.le_trans visibleAfterStable afterVisibility)
  have activeAtVisibility :
      (execution.source.state visibilityCutoff owner).Active :=
    execution.source.active_on_response_free_suffix
      owner visibleAfterStart activeAtStart sourceNoResponse
  have matchingOften :=
    execution.infinitelyOften_matchingCAS_of_stableObservations
      threadFair owner visibilityCutoff activeAtVisibility
      noResponseAfterVisibility noModificationAfterVisibility
      (execution.stableValueAt stableCutoff) observes
  have matchingAtSomeRepresentedSite :
      Liveness.InfinitelyOften (fun time =>
        ∃ site,
          site ∈ execution.representedSites stableCutoff ∧
            execution.progressInterface.matchingAttemptAt
              owner site time) := by
    intro bound
    obtain ⟨time, afterMaximum, ownerEvent, matching⟩ :=
      matchingOften (max bound stableCutoff)
    have afterBound : bound ≤ time :=
      Nat.le_trans (Nat.le_max_left _ _) afterMaximum
    have afterStable : stableCutoff ≤ time :=
      Nat.le_trans (Nat.le_max_right _ _) afterMaximum
    obtain ⟨site, member, matchingAtEventOwner⟩ :=
      execution.matchingCAS_has_representedSite
        stableCutoff time afterStable allStable matching
    refine ⟨time, afterBound, site, member, ?_⟩
    rw [← ownerEvent]
    exact matchingAtEventOwner
  obtain ⟨site, _, matchingAtSite⟩ :=
    Liveness.InfinitelyOften.finite_pigeonhole
      (execution.representedSites stableCutoff)
      (fun time site =>
        execution.progressInterface.matchingAttemptAt
          owner site time)
      matchingAtSomeRepresentedSite
  exact ⟨owner, visibilityCutoff, visibleAfterStart, site,
    noModificationAfterVisibility site, matchingAtSite⟩

/-- Prefix-finite per-site from-read fairness supplies the selected-site
visibility premise needed by queue progress. -/
theorem progressObligations_of_fromReadFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (fromReadFair : execution.FromReadFair) :
    execution.ProgressObligations :=
  execution.progressObligations_of_selectedSiteVisibilityFair
    schedules threadFair
    (execution.selectedSiteVisibilityFair_of_fromReadFair fromReadFair)

/-- Conventional per-site memory fairness supplies the complete queue
progress obligation. -/
theorem progressObligations_of_memoryFairness
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (schedules : execution.PrefixAtomSchedules)
    (threadFair : execution.source.WeakThreadFair)
    (memoryFair : execution.MemoryFair) :
    execution.ProgressObligations :=
  execution.progressObligations_of_selectedSiteVisibilityFair
    schedules threadFair
    (execution.selectedSiteVisibilityFair_of_memoryFair memoryFair)

end InfiniteRC11Execution

end MSQueue.Source

end WeakMemory
