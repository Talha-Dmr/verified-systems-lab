import WeakMemory.MSQueueInfiniteControlProgress
import WeakMemory.MSQueueInfiniteStableSite

namespace WeakMemory.MSQueue.Source

/-!
# Concrete selected-site visibility for queue retry control

`SelectedSiteVisibilityFair` is the algorithm-facing form of RC11 memory
fairness.  It contains no scheduling, response, success, or abstract-progress
clause: after one exact site stops being modified, all sufficiently late reads
at that site use the maximal supplying write selected from the cutoff prefix.
The property is derived below from per-site prefix-finite `fr`.
-/

namespace TraceEvent

/-- The read component of an atomic event observes one stable site value. -/
def ObservesStable
    (stableValue : Site → Ptr) : TraceEvent Value → Prop
  | .atomic occurrence =>
      occurrence.toRC11Atom.IsRead →
        occurrence.toRC11Atom.readValue =
          some (stableValue occurrence.action.site)
  | _ => True

/-- A weak-CAS attempt by one owner at one exact logical queue site. -/
def CASAttemptAt
    (event : TraceEvent Value)
    (thread : ThreadId)
    (site : Site) : Prop :=
  match event with
  | .atomic occurrence =>
      occurrence.action.thread = thread ∧
        occurrence.action.site = site ∧
        occurrence.action.IsCASAttempt
  | _ => False

/-- A retry-snapshot validation by one owner at one exact site. -/
def RetrySnapshotAt
    (event : TraceEvent Value)
    (thread : ThreadId)
    (site : Site) : Prop :=
  match event with
  | .atomic occurrence =>
      occurrence.action.thread = thread ∧
        occurrence.action.site = site ∧
        occurrence.action.IsRetrySnapshot
  | _ => False

/-- Exact retry boundaries split into CAS attempts and snapshot validations. -/
theorem retryBoundaryAt_iff_casAttemptAt_or_retrySnapshotAt
    (event : TraceEvent Value)
    (thread : ThreadId)
    (site : Site) :
    event.thread = thread ∧ event.RetryBoundaryAt site ↔
      event.CASAttemptAt thread site ∨
        event.RetrySnapshotAt thread site := by
  cases event with
  | atomic occurrence =>
      simp only [RetryBoundaryAt, CASAttemptAt, RetrySnapshotAt,
        TraceEvent.thread]
      constructor
      · rintro ⟨owner, atSite, cas | snapshot⟩
        · exact Or.inl ⟨owner, atSite, cas⟩
        · exact Or.inr ⟨owner, atSite, snapshot⟩
      · rintro (⟨owner, atSite, cas⟩ | ⟨owner, atSite, snapshot⟩)
        · exact ⟨owner, atSite, Or.inl cas⟩
        · exact ⟨owner, atSite, Or.inr snapshot⟩
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      simp [RetryBoundaryAt, CASAttemptAt, RetrySnapshotAt]

/-- Every queue CAS attempt is an atomic RC11 read. -/
theorem casAttemptAt_atomicRead
    {event : TraceEvent Value}
    {thread : ThreadId}
    {site : Site}
    (attempt : event.CASAttemptAt thread site) :
    ∃ occurrence : AtomicOccurrence Value,
      event = .atomic occurrence ∧
        occurrence.action.thread = thread ∧
        occurrence.action.site = site ∧
        occurrence.toRC11Atom.IsRead := by
  cases event with
  | atomic occurrence =>
      rcases attempt with ⟨owner, atSite, cas⟩
      refine ⟨occurrence, rfl, owner, atSite, ?_⟩
      rcases occurrence with ⟨id, action⟩
      cases action with
      | initializeNext | enqueueTailLoad | enqueueNextLoad |
          enqueueTailValidate | dequeueHeadLoad | dequeueTailLoad |
          dequeueNextLoad | dequeueHeadValidate |
          dequeueHeadValidateEmpty =>
          simp [AtomicAction.IsCASAttempt] at cas
      | enqueueLinkCAS _ _ _ _ _ _ succeeded =>
          cases succeeded <;>
            simp [AtomicOccurrence.toRC11Atom,
              MultiLocationRC11.Atom.IsRead, AtomicAction.access,
              MultiLocationRC11.Access.IsRead]
      | enqueueHelpTailCAS _ _ _ _ _ succeeded =>
          cases succeeded <;>
            simp [AtomicOccurrence.toRC11Atom,
              MultiLocationRC11.Atom.IsRead, AtomicAction.access,
              MultiLocationRC11.Access.IsRead]
      | enqueueFinishTailCAS _ _ _ _ _ succeeded =>
          cases succeeded <;>
            simp [AtomicOccurrence.toRC11Atom,
              MultiLocationRC11.Atom.IsRead, AtomicAction.access,
              MultiLocationRC11.Access.IsRead]
      | dequeueHelpTailCAS _ _ _ _ _ succeeded =>
          cases succeeded <;>
            simp [AtomicOccurrence.toRC11Atom,
              MultiLocationRC11.Atom.IsRead, AtomicAction.access,
              MultiLocationRC11.Access.IsRead]
      | dequeueHeadCAS _ _ _ _ _ _ succeeded =>
          cases succeeded <;>
            simp [AtomicOccurrence.toRC11Atom,
              MultiLocationRC11.Atom.IsRead, AtomicAction.access,
              MultiLocationRC11.Access.IsRead]
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim attempt

/-- Every queue retry snapshot is an atomic RC11 read. -/
theorem retrySnapshotAt_atomicRead
    {event : TraceEvent Value}
    {thread : ThreadId}
    {site : Site}
    (snapshot : event.RetrySnapshotAt thread site) :
    ∃ occurrence : AtomicOccurrence Value,
      event = .atomic occurrence ∧
        occurrence.action.thread = thread ∧
        occurrence.action.site = site ∧
        occurrence.toRC11Atom.IsRead := by
  cases event with
  | atomic occurrence =>
      rcases snapshot with ⟨owner, atSite, validation⟩
      refine ⟨occurrence, rfl, owner, atSite, ?_⟩
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        simp_all [AtomicAction.IsRetrySnapshot,
          AtomicOccurrence.toRC11Atom,
          MultiLocationRC11.Atom.IsRead,
          AtomicAction.access,
          MultiLocationRC11.Access.IsRead]
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim snapshot

end TraceEvent

namespace InfiniteRC11Execution

private theorem writtenValue_exists_of_isWrite
    (atom : MultiLocationRC11.Atom Site Ptr)
    (write : atom.IsWrite) :
    ∃ value, atom.writtenValue = some value := by
  change atom.access.IsWrite at write
  change ∃ value, atom.access.writtenValue = some value
  generalize atom.access = access at write ⊢
  cases access <;>
    simp_all [MultiLocationRC11.Access.IsWrite,
      MultiLocationRC11.Access.writtenValue]

/-!
The selected-site property deliberately quantifies over a proof that the site
is already represented at the cutoff prefix.  Later structural stabilization
will choose cutoffs after all pending `next` initializers, making this premise
available for every subsequent retry site.
-/
def SelectedSiteVisibilityFair
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  ∀ site start
    (represented :
      (execution.supportedPrefix start).candidate.Represents site),
    WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start →
    ∃ visibilityCutoff,
      start ≤ visibilityCutoff ∧
        ∀ time,
          visibilityCutoff ≤ time →
          ∀ occurrence : AtomicOccurrence Value,
            execution.source.event time = .atomic occurrence →
            occurrence.action.site = site →
            occurrence.toRC11Atom.IsRead →
            execution.observedWrite time =
              (execution.prefixMaximalWriteAt
                start site represented).atom.id

/-- Per-site prefix-finite `fr` derives concrete selected-site visibility. -/
theorem selectedSiteVisibilityFair_of_fromReadFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (fromReadFair : execution.FromReadFair) :
    execution.SelectedSiteVisibilityFair := by
  intro site start represented stable
  let selected : Nat → Prop := fun time =>
    start ≤ time ∧
      ∃ occurrence : AtomicOccurrence Value,
        execution.source.event time = .atomic occurrence ∧
          occurrence.action.site = site ∧
          occurrence.toRC11Atom.IsRead
  have visible :=
    execution.eventually_selected_observes_prefixMaximal_of_fromReadFair
      fromReadFair site start represented stable selected
      (fun time chosen => chosen.1)
      (fun time chosen => chosen.2)
  obtain ⟨rawCutoff, visibleAfter⟩ := visible
  refine ⟨max start rawCutoff, Nat.le_max_left _ _, ?_⟩
  intro time afterCutoff occurrence event atSite read
  apply visibleAfter time
    (Nat.le_trans (Nat.le_max_right start rawCutoff) afterCutoff)
  exact ⟨Nat.le_trans (Nat.le_max_left start rawCutoff) afterCutoff,
    occurrence, event, atSite, read⟩

/-- Conventional per-site memory fairness derives selected-site visibility. -/
theorem selectedSiteVisibilityFair_of_memoryFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (memoryFair : execution.MemoryFair) :
    execution.SelectedSiteVisibilityFair :=
  execution.selectedSiteVisibilityFair_of_fromReadFair
    (execution.fromReadFair_of_memoryFair memoryFair)

/-- Stable pointer value written by the cutoff-prefix maximal atom at a site. -/
noncomputable def stableValueAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start : Nat)
    (site : Site) : Ptr := by
  classical
  exact
    if represented :
        (execution.supportedPrefix start).candidate.Represents site then
      Classical.choose
        (writtenValue_exists_of_isWrite
          (execution.prefixMaximalWriteAt start site represented).atom
          (execution.prefixMaximalWriteAt start site represented).isWrite)
    else
      .null

/-- At a represented site, `stableValueAt` is the maximal write's value. -/
theorem prefixMaximal_writtenValue_eq_stableValueAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start : Nat)
    (site : Site)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site) :
    (execution.prefixMaximalWriteAt start site represented).atom.writtenValue =
      some (execution.stableValueAt start site) := by
  have specification :=
    Classical.choose_spec
      (writtenValue_exists_of_isWrite
        (execution.prefixMaximalWriteAt start site represented).atom
        (execution.prefixMaximalWriteAt start site represented).isWrite)
  simpa [stableValueAt, represented] using specification

/-- Sites represented at one prefix, retained as a finite list. -/
def representedSites
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start : Nat) : List Site :=
  (execution.supportedPrefix start).candidate.atoms.map
    MultiLocationRC11.Atom.location

theorem mem_representedSites_iff
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start : Nat)
    (site : Site) :
    site ∈ execution.representedSites start ↔
      (execution.supportedPrefix start).candidate.Represents site := by
  constructor
  · intro member
    obtain ⟨atom, atomMember, location⟩ := List.mem_map.mp member
    exact ⟨atom, atomMember, location⟩
  · rintro ⟨atom, atomMember, location⟩
    exact List.mem_map.mpr ⟨atom, atomMember, location⟩

/-- A later atomic read's site was already represented before stabilization. -/
theorem site_represented_at_start_of_later_read
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (start time : Nat)
    (afterStart : start ≤ time)
    (allStable :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site start)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence)
    (read : occurrence.toRC11Atom.IsRead) :
    (execution.supportedPrefix start).candidate.Represents
      occurrence.action.site := by
  let finiteExecution := execution.supportedPrefix (time + 1)
  have targetMember : occurrence.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms time occurrence event
  obtain ⟨source, readsFrom⟩ :=
    finiteExecution.valid.everyRead_hasSource targetMember read
  have sourceLocation : source.location = occurrence.action.site := by
    simpa [AtomicOccurrence.toRC11Atom] using readsFrom.sameLocation
  have sourceAtStart :
      source ∈ (execution.supportedPrefix start).candidate.atoms :=
    execution.write_mem_startPrefix_of_noModification
      occurrence.action.site start (time + 1) (by omega)
      (allStable occurrence.action.site)
      readsFrom.1 sourceLocation readsFrom.2.2.1
  exact ⟨source, sourceAtStart, sourceLocation⟩

/-!
If a later read observes the cutoff-prefix maximal write, its source-level
pointer is exactly `stableValueAt` for that site.
-/
theorem readValue_eq_stableValueAt_of_observedMaximal
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site)
    (start time : Nat)
    (afterStart : start ≤ time)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence)
    (atSite : occurrence.action.site = site)
    (read : occurrence.toRC11Atom.IsRead)
    (observed :
      execution.observedWrite time =
        (execution.prefixMaximalWriteAt start site represented).atom.id) :
    occurrence.toRC11Atom.readValue =
      some (execution.stableValueAt start site) := by
  let finiteExecution := execution.supportedPrefix (time + 1)
  have targetMember : occurrence.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms time occurrence event
  obtain ⟨source, readsFrom⟩ :=
    finiteExecution.valid.everyRead_hasSource targetMember read
  have sourceLocation : source.location = site := by
    exact readsFrom.sameLocation.trans (by
      simpa [AtomicOccurrence.toRC11Atom] using atSite)
  have sourceAtStart :
      source ∈ (execution.supportedPrefix start).candidate.atoms :=
    execution.write_mem_startPrefix_of_noModification
      site start (time + 1) (by omega) stable
      readsFrom.1 sourceLocation readsFrom.2.2.1
  have restrictionRaw :=
    execution.prefixReadSource (time + 1)
      occurrence.toRC11Atom targetMember
  have restriction :
      finiteExecution.candidate.sourceId occurrence.toRC11Atom.id =
        execution.readSource occurrence.toRC11Atom.id := by
    exact restrictionRaw
  have globalSource :
      execution.readSource occurrence.id = some source.id :=
    restriction.symm.trans readsFrom.2.2.2.2.2.2
  have observedSource :=
    execution.readSource_eq_observedWrite_of_atomic
      time occurrence event read
  have sourceId :
      source.id =
        (execution.prefixMaximalWriteAt start site represented).atom.id := by
    exact Option.some.inj
      (globalSource.symm.trans
        (observedSource.trans (congrArg some observed)))
  have sourceIsMaximal :
      source =
        (execution.prefixMaximalWriteAt start site represented).atom :=
    (execution.supportedPrefix start).valid.atom_eq_of_id_eq
      sourceAtStart
      (execution.prefixMaximalWriteAt start site represented).member
      sourceId
  have valueAgreement := readsFrom.valueAgreement
  rw [sourceIsMaximal,
    execution.prefixMaximal_writtenValue_eq_stableValueAt
      start site represented] at valueAgreement
  exact valueAgreement.symm

private theorem uniform_visibility_on_site_list
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (visibility : execution.SelectedSiteVisibilityFair)
    (start : Nat)
    (allStable :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site start) :
    ∀ sites : List Site,
      (∀ site, site ∈ sites →
        (execution.supportedPrefix start).candidate.Represents site) →
      ∃ cutoff,
        start ≤ cutoff ∧
          ∀ site,
            site ∈ sites →
            ∀ time,
              cutoff ≤ time →
              ∀ occurrence : AtomicOccurrence Value,
                execution.source.event time = .atomic occurrence →
                occurrence.action.site = site →
                occurrence.toRC11Atom.IsRead →
                occurrence.toRC11Atom.readValue =
                  some (execution.stableValueAt start site) := by
  intro sites represented
  induction sites with
  | nil =>
      exact ⟨start, Nat.le_refl _, fun site impossible =>
        False.elim (by simp at impossible)⟩
  | cons focus tail inductionHypothesis =>
      have focusRepresented := represented focus (by simp)
      obtain ⟨focusCutoff, focusAfter, focusVisible⟩ :=
        visibility focus start focusRepresented (allStable focus)
      obtain ⟨tailCutoff, tailAfter, tailVisible⟩ :=
        inductionHypothesis
          (fun site member => represented site (by simp [member]))
      refine ⟨max focusCutoff tailCutoff, by omega, ?_⟩
      intro site member time afterCutoff occurrence event atSite read
      simp only [List.mem_cons] at member
      rcases member with same | inTail
      · have atFocus : occurrence.action.site = focus := atSite.trans same
        subst site
        have observed := focusVisible time
          (Nat.le_trans (Nat.le_max_left _ _) afterCutoff)
          occurrence event atFocus read
        rw [atFocus]
        exact execution.readValue_eq_stableValueAt_of_observedMaximal
          focus start time (by omega) focusRepresented (allStable focus)
          occurrence event atFocus read observed
      · exact tailVisible site inTail time
          (Nat.le_trans (Nat.le_max_right _ _) afterCutoff)
          occurrence event atSite read

/-!
Finite representation turns pointwise selected-site visibility into one
uniform stable-value cutoff for every later atomic read.
-/
theorem eventually_allReads_observe_stableValueAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (visibility : execution.SelectedSiteVisibilityFair)
    (start : Nat)
    (allStable :
      ∀ site,
        WeakCAS.SiteProgressRule.NoModificationAtFrom
          execution.progressInterface site start) :
    ∃ cutoff,
      start ≤ cutoff ∧
        ∀ time,
          cutoff ≤ time →
          (execution.source.event time).ObservesStable
            (execution.stableValueAt start) := by
  obtain ⟨cutoff, afterStart, visible⟩ :=
    execution.uniform_visibility_on_site_list visibility start allStable
      (execution.representedSites start)
      (fun site member =>
        (execution.mem_representedSites_iff start site).mp member)
  refine ⟨cutoff, afterStart, ?_⟩
  intro time afterCutoff
  cases eventEq : execution.source.event time with
  | atomic occurrence =>
      simp only [TraceEvent.ObservesStable]
      intro read
      have siteRepresented :=
        execution.site_represented_at_start_of_later_read
          start time (by omega) allStable occurrence eventEq read
      have siteMember :=
        (execution.mem_representedSites_iff
          start occurrence.action.site).mpr siteRepresented
      exact visible occurrence.action.site siteMember time afterCutoff
        occurrence eventEq rfl read
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      simp [TraceEvent.ObservesStable]

/-!
Once selected-site visibility has begun, any two same-site atomic reads have
the same pointer value.  This is the exact value-level fact consumed by queue
retry provenance: a cached load and its later validation/CAS compare against
one supplying write.
-/
theorem readValues_eq_of_selectedSiteVisibility
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (visibility : execution.SelectedSiteVisibilityFair)
    (site : Site)
    (start : Nat)
    (represented :
      (execution.supportedPrefix start).candidate.Represents site)
    (stable :
      WeakCAS.SiteProgressRule.NoModificationAtFrom
        execution.progressInterface site start)
    {firstTime secondTime : Nat}
    {first second : AtomicOccurrence Value}
    (firstAfter :
      (Classical.choose (visibility site start represented stable)) ≤
        firstTime)
    (secondAfter :
      (Classical.choose (visibility site start represented stable)) ≤
        secondTime)
    (firstEvent : execution.source.event firstTime = .atomic first)
    (secondEvent : execution.source.event secondTime = .atomic second)
    (firstSite : first.action.site = site)
    (secondSite : second.action.site = site)
    (firstRead : first.toRC11Atom.IsRead)
    (secondRead : second.toRC11Atom.IsRead) :
    first.toRC11Atom.readValue = second.toRC11Atom.readValue := by
  let witness := visibility site start represented stable
  let cutoff := Classical.choose witness
  have cutoffFacts := Classical.choose_spec witness
  have firstObserved :=
    cutoffFacts.2 firstTime firstAfter first firstEvent firstSite firstRead
  have secondObserved :=
    cutoffFacts.2 secondTime secondAfter second secondEvent secondSite secondRead
  have firstSource :=
    execution.readSource_eq_observedWrite_of_atomic
      firstTime first firstEvent firstRead
  have secondSource :=
    execution.readSource_eq_observedWrite_of_atomic
      secondTime second secondEvent secondRead
  apply execution.readValue_eq_of_same_readSource
      firstTime secondTime first second firstEvent secondEvent
      firstRead secondRead
      (execution.prefixMaximalWriteAt start site represented).atom.id
  · rw [firstSource]
    exact congrArg some firstObserved
  · rw [secondSource]
    exact congrArg some secondObserved

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
