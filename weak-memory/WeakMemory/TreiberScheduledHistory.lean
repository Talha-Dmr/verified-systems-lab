import WeakMemory.TreiberClientHistory

namespace WeakMemory.TreiberRC11

/-!
# Recovering identified commits from graph schedules

Canonical graph events deliberately omit source operation identifiers. This
module reconstructs that metadata without changing `Event`: atomic source
labels are projected to a parallel metadata list, numbered by exactly the same
scheme as `EventGraph.atomicEventsFrom`, and looked up by the resulting event.

Filtering this lookup in source-carrier order recovers
`sourceCommittedOperations`. Filtering it in a respecting graph schedule
preserves the schedule order while retaining each operation's source thread
and `OperationId`.
-/

/-- Source metadata retained for one atomic-head label. -/
structure AtomicSourceMetadata (α : Type) where
  thread : Nat
  operation : ControlFlow.OperationId
  action : TreiberRA.Action α

/-- Extract atomic metadata and discard every source-only label. -/
def atomicSourceMetadata?
    (owned : EventGraph.OwnedLabel α) :
    Option (AtomicSourceMetadata α) :=
  match owned.label with
  | .atomic operation action =>
      some {
        thread := owned.thread
        operation := operation
        action := action
      }
  | _ => none

/-- Atomic metadata in source-label order. -/
def atomicSourceMetadata
    (labels : List (EventGraph.OwnedLabel α)) :
    List (AtomicSourceMetadata α) :=
  labels.filterMap atomicSourceMetadata?

/-- Number a metadata list using the canonical atomic-event scheme. -/
def eventsFromMetadata :
    EventId →
    List (AtomicSourceMetadata α) →
    List (Event α)
  | _, [] => []
  | next, metadata :: rest =>
      Event.mk next (.algorithm metadata.action) ::
        eventsFromMetadata (next + 1) rest

/--
Look up the exact source metadata paired with a numbered canonical event.

Full event equality, rather than action equality alone, distinguishes repeated
equal retry actions at different source occurrences.
-/
def findAtomicSourceMetadata?
    [DecidableEq α]
    (next : EventId)
    (metadata : List (AtomicSourceMetadata α))
    (event : Event α) :
    Option (AtomicSourceMetadata α) :=
  match metadata with
  | [] => none
  | source :: rest =>
      if Event.mk next (.algorithm source.action) = event then
        some source
      else
        findAtomicSourceMetadata? (next + 1) rest event

/-- Initializer events never have atomic source metadata. -/
@[simp] private theorem findAtomicSourceMetadata?_initial
    [DecidableEq α]
    (next id : EventId)
    (metadata : List (AtomicSourceMetadata α)) :
    findAtomicSourceMetadata?
        next metadata (Event.mk id .initial) =
      none := by
  induction metadata generalizing next with
  | nil =>
      rfl
  | cons source rest inductionHypothesis =>
      simp [findAtomicSourceMetadata?,
        inductionHypothesis]

/-- Project one metadata entry to its identified abstract commit, if any. -/
def metadataCommit?
    (metadata : AtomicSourceMetadata α) :
    Option (HerlihyWing.IdentifiedCompleted α) :=
  metadata.action.commit?.map
    (identifiedCommit metadata.thread metadata.operation)

/-- Recover an identified commit from one canonical skeleton event. -/
def identifiedEventCommit?
    [DecidableEq α]
    (skeleton : EventGraph.Skeleton α)
    (event : Event α) :
    Option (HerlihyWing.IdentifiedCompleted α) :=
  (findAtomicSourceMetadata?
      1 (atomicSourceMetadata skeleton.labels) event).bind
    metadataCommit?

/--
Identified abstract commits in the chosen graph-schedule order.

The source skeleton supplies thread and operation identity; the schedule
supplies only the ordering.
-/
def scheduledOperations
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) :
    List (HerlihyWing.IdentifiedCompleted α) :=
  schedule.filterMap
    (identifiedEventCommit? execution.source.skeleton)

/-- Metadata numbering agrees definitionally with source-label numbering. -/
theorem eventsFromMetadata_atomicSourceMetadata
    (next : EventId)
    (labels : List (EventGraph.OwnedLabel α)) :
    eventsFromMetadata next (atomicSourceMetadata labels) =
      EventGraph.atomicEventsFrom next labels := by
  induction labels generalizing next with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      have tailSame
          (later : EventId) :
          eventsFromMetadata later
              (List.filterMap atomicSourceMetadata? rest) =
            EventGraph.atomicEventsFrom later rest := by
        simpa only [atomicSourceMetadata] using
          inductionHypothesis later
      cases label <;>
        simp only [atomicSourceMetadata, List.filterMap_cons,
          atomicSourceMetadata?, eventsFromMetadata,
          EventGraph.atomicEventsFrom]
      all_goals simp only [tailSame]

/-- Numbered metadata events have identifiers at least their starting ID. -/
private theorem eventsFromMetadata_id_lowerBound
    {next : EventId}
    {metadata : List (AtomicSourceMetadata α)}
    {event : Event α}
    (member : event ∈ eventsFromMetadata next metadata) :
    next ≤ event.id := by
  induction metadata generalizing next event with
  | nil =>
      simp [eventsFromMetadata] at member
  | cons source rest inductionHypothesis =>
      simp only [eventsFromMetadata, List.mem_cons] at member
      rcases member with isHead | inRest
      · subst event
        exact Nat.le_refl next
      · exact Nat.le_trans
          (Nat.le_succ next)
          (inductionHypothesis
            (next := next + 1) inRest)

/-- A tail event cannot equal the preceding numbered metadata event. -/
private theorem head_ne_of_mem_metadataTail
    {next : EventId}
    {source : AtomicSourceMetadata α}
    {rest : List (AtomicSourceMetadata α)}
    {event : Event α}
    (member :
      event ∈ eventsFromMetadata (next + 1) rest) :
    Event.mk next (.algorithm source.action) ≠ event := by
  intro same
  subst event
  have lowerBound :
      next + 1 ≤
        (Event.mk next
          (.algorithm source.action) : Event α).id :=
    eventsFromMetadata_id_lowerBound member
  exact (Nat.not_succ_le_self next) lowerBound

/-- Looking through a fresh head does not change lookup for a tail event. -/
private theorem findAtomicSourceMetadata?_cons_of_mem_tail
    [DecidableEq α]
    {next : EventId}
    {source : AtomicSourceMetadata α}
    {rest : List (AtomicSourceMetadata α)}
    {event : Event α}
    (member :
      event ∈ eventsFromMetadata (next + 1) rest) :
    findAtomicSourceMetadata?
        next (source :: rest) event =
      findAtomicSourceMetadata?
        (next + 1) rest event := by
  simp [findAtomicSourceMetadata?,
    head_ne_of_mem_metadataTail member]

/-- `filterMap` functions agreeing on every member give equal results. -/
private theorem filterMap_congr_of_mem
    {items : List β}
    {left right : β → Option γ}
    (same :
      ∀ item,
        item ∈ items →
        left item = right item) :
    items.filterMap left =
      items.filterMap right := by
  induction items with
  | nil =>
      rfl
  | cons item rest inductionHypothesis =>
      have head := same item (by simp)
      have tail :
          rest.filterMap left =
            rest.filterMap right :=
        inductionHypothesis
          (fun later member =>
            same later (by simp [member]))
      simp only [List.filterMap_cons, head, tail]

/-- Exact lookup recovers metadata in its original list order. -/
private theorem filterMap_eventsFromMetadata_lookup
    [DecidableEq α]
    (next : EventId)
    (metadata : List (AtomicSourceMetadata α)) :
    (eventsFromMetadata next metadata).filterMap
        (fun event =>
          (findAtomicSourceMetadata?
            next metadata event).bind metadataCommit?) =
      metadata.filterMap metadataCommit? := by
  induction metadata generalizing next with
  | nil =>
      rfl
  | cons source rest inductionHypothesis =>
      have headLookup :
          findAtomicSourceMetadata?
              next (source :: rest)
                (Event.mk next
                  (.algorithm source.action)) =
            some source := by
        simp [findAtomicSourceMetadata?]
      have tailLookup :
          (eventsFromMetadata (next + 1) rest).filterMap
              (fun event =>
                (findAtomicSourceMetadata?
                  next (source :: rest) event).bind
                    metadataCommit?) =
            (eventsFromMetadata (next + 1) rest).filterMap
              (fun event =>
                (findAtomicSourceMetadata?
                  (next + 1) rest event).bind
                    metadataCommit?) := by
        apply filterMap_congr_of_mem
        intro event member
        rw [findAtomicSourceMetadata?_cons_of_mem_tail member]
      simp only [eventsFromMetadata, List.filterMap_cons]
      rw [headLookup, tailLookup,
        inductionHypothesis (next := next + 1)]
      rfl

/-- Metadata commits are exactly source-label commits, in source order. -/
private theorem filterMap_metadataCommit_eq_source
    (labels : List (EventGraph.OwnedLabel α)) :
    (atomicSourceMetadata labels).filterMap metadataCommit? =
      sourceCommittedOperations
        ({ labels := labels } : EventGraph.Skeleton α) := by
  induction labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      have tailSame :
          (List.filterMap atomicSourceMetadata? rest).filterMap
              metadataCommit? =
            List.filterMap sourceCommit? rest := by
        simpa only [atomicSourceMetadata,
          sourceCommittedOperations] using
          inductionHypothesis
      cases label with
      | invokePush =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | invokePop =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | invokeIsEmpty =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | writeNext =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | readNext =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | respond =>
          simpa [atomicSourceMetadata,
            atomicSourceMetadata?,
            sourceCommittedOperations, sourceCommit?]
            using tailSame
      | atomic operation action =>
          cases commits : action.commit? <;>
            simp [atomicSourceMetadata,
              atomicSourceMetadata?, metadataCommit?,
              sourceCommittedOperations, sourceCommit?,
              commits, tailSame]

/--
Filtering the canonical event carrier through exact metadata lookup recovers
the source commit list without reordering it.
-/
theorem filterMap_identifiedEventCommit_eq_source
    [DecidableEq α]
    (skeleton : EventGraph.Skeleton α) :
    skeleton.events.filterMap
        (identifiedEventCommit? skeleton) =
      sourceCommittedOperations skeleton := by
  rw [show skeleton.events =
      EventGraph.Skeleton.initialEvent ::
        EventGraph.atomicEventsFrom 1 skeleton.labels by rfl]
  simp only [List.filterMap_cons]
  simp only [identifiedEventCommit?,
    EventGraph.Skeleton.initialEvent,
    findAtomicSourceMetadata?_initial, Option.bind]
  rw [← eventsFromMetadata_atomicSourceMetadata
    1 skeleton.labels]
  exact (filterMap_eventsFromMetadata_lookup
    1 (atomicSourceMetadata skeleton.labels)).trans
      (filterMap_metadataCommit_eq_source skeleton.labels)

/-- A respecting schedule is a permutation of the canonical source carrier. -/
private theorem sourceEvents_perm_schedule
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule) :
    execution.source.skeleton.events.Perm schedule := by
  apply (List.perm_iff_count).2
  intro event
  have sourceNodup :
      execution.source.skeleton.events.Nodup :=
    execution.source.skeleton.noDuplicateEvents
  rw [sourceNodup.count, respects.noDuplicates.count]
  have membership :
      event ∈ execution.source.skeleton.events ↔
        event ∈ schedule := by
    simpa using respects.covers event
  by_cases sourceMember :
      event ∈ execution.source.skeleton.events
  · have scheduleMember : event ∈ schedule :=
      membership.mp sourceMember
    simp [sourceMember, scheduleMember]
  · have scheduleMember : event ∉ schedule := by
      intro member
      exact sourceMember (membership.mpr member)
    simp [sourceMember, scheduleMember]

/--
Reordering the canonical event carrier by a respecting schedule reorders, but
neither loses nor invents, identified source commits.
-/
theorem sourceCommittedOperations_perm_scheduledOperations
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule) :
    sourceCommittedOperations execution.source.skeleton
      |>.Perm (scheduledOperations execution schedule) := by
  rw [← filterMap_identifiedEventCommit_eq_source]
  exact
    (sourceEvents_perm_schedule execution respects).filterMap
      (identifiedEventCommit? execution.source.skeleton)

/-- Erase source identity from the commit represented by one graph event. -/
def erasedEventCommit?
    (event : Event α) :
    Option (StackSpec.CompletedOperation α) :=
  match event.action? with
  | none => none
  | some action =>
      action.commit?.map Treiber.Commit.completed

/-- Every numbered metadata event recovers its exact source metadata. -/
private theorem exists_findAtomicSourceMetadata?_of_mem
    [DecidableEq α]
    {next : EventId}
    {metadata : List (AtomicSourceMetadata α)}
    {event : Event α}
    (member : event ∈ eventsFromMetadata next metadata) :
    ∃ source,
      findAtomicSourceMetadata? next metadata event =
          some source ∧
        event.action? = some source.action := by
  induction metadata generalizing next event with
  | nil =>
      simp [eventsFromMetadata] at member
  | cons source rest inductionHypothesis =>
      simp only [eventsFromMetadata, List.mem_cons] at member
      rcases member with isHead | inRest
      · subst event
        exact ⟨source, by
          simp [findAtomicSourceMetadata?], rfl⟩
      · obtain ⟨found, lookup, actionShape⟩ :=
          inductionHypothesis
            (next := next + 1) inRest
        refine ⟨found, ?_, actionShape⟩
        rw [findAtomicSourceMetadata?_cons_of_mem_tail inRest]
        exact lookup

/-- Exact identified lookup erases to the graph event's ordinary commit. -/
private theorem identifiedEventCommit?_map_erase
    [DecidableEq α]
    (skeleton : EventGraph.Skeleton α)
    {event : Event α}
    (member : event ∈ skeleton.events) :
    (identifiedEventCommit? skeleton event).map
        HerlihyWing.IdentifiedCompleted.erase =
      erasedEventCommit? event := by
  simp only [EventGraph.Skeleton.events,
    List.mem_cons] at member
  rcases member with isInitial | inAtomic
  · subst event
    simp [identifiedEventCommit?,
      EventGraph.Skeleton.initialEvent,
      erasedEventCommit?, Event.action?]
  · have metadataMember :
        event ∈
          eventsFromMetadata
            1 (atomicSourceMetadata skeleton.labels) := by
      rw [eventsFromMetadata_atomicSourceMetadata]
      exact inAtomic
    obtain ⟨source, lookup, actionShape⟩ :=
      exists_findAtomicSourceMetadata?_of_mem metadataMember
    cases commits : source.action.commit? <;>
      simp [identifiedEventCommit?, lookup, metadataCommit?,
        erasedEventCommit?, actionShape, commits]

/-- Ordinary commit extraction is pointwise filtering over graph events. -/
private theorem completedHistory_commits_projectedActions
    (events : List (Event α)) :
    Treiber.completedHistory
        (TreiberRA.commits (projectedActions events)) =
      events.filterMap erasedEventCommit? := by
  induction events with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases event with
      | mk id kind =>
          cases kind with
          | initial =>
              have right :
                  ({ id := id, kind := .initial } :: rest).filterMap
                      erasedEventCommit? =
                    rest.filterMap erasedEventCommit? := by
                simp [erasedEventCommit?, Event.action?]
              rw [right]
              simpa [projectedActions, Event.action?] using
                inductionHypothesis
          | algorithm action =>
              cases commits : action.commit? with
              | none =>
                  have projected :
                      TreiberRA.commits
                          (action :: projectedActions rest) =
                        TreiberRA.commits
                          (projectedActions rest) := by
                    simp [TreiberRA.commits, commits]
                  have right :
                      ({ id := id,
                          kind := .algorithm action } :: rest).filterMap
                            erasedEventCommit? =
                        rest.filterMap erasedEventCommit? := by
                    simp [erasedEventCommit?, Event.action?,
                      commits]
                  simp only [projectedActions, Event.action?]
                  rw [projected, right]
                  exact inductionHypothesis
              | some commit =>
                  have projected :
                      TreiberRA.commits
                          (action :: projectedActions rest) =
                        commit ::
                          TreiberRA.commits
                            (projectedActions rest) := by
                    simp [TreiberRA.commits, commits]
                  have right :
                      ({ id := id,
                          kind := .algorithm action } :: rest).filterMap
                            erasedEventCommit? =
                        commit.completed ::
                          rest.filterMap erasedEventCommit? := by
                    simp [erasedEventCommit?, Event.action?,
                      commits]
                  simp only [projectedActions, Event.action?]
                  rw [projected, right]
                  exact congrArg
                    (List.cons commit.completed)
                    inductionHypothesis

/--
Erasing schedule-side source identity gives exactly the existing anonymous
commit history consumed by the sequential stack proof.
-/
theorem eraseIdentities_scheduledOperations
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule) :
    HerlihyWing.eraseIdentities
        (scheduledOperations execution schedule) =
      Treiber.completedHistory
        (TreiberRA.commits (projectedActions schedule)) := by
  unfold HerlihyWing.eraseIdentities scheduledOperations
  rw [List.map_filterMap]
  have pointwise :
      schedule.filterMap
          (fun event =>
            (identifiedEventCommit?
              execution.source.skeleton event).map
                HerlihyWing.IdentifiedCompleted.erase) =
        schedule.filterMap erasedEventCommit? := by
    apply filterMap_congr_of_mem
    intro event member
    apply identifiedEventCommit?_map_erase
    have graphMember :
        event ∈ execution.relations.graph.events :=
      (respects.covers event).mpr member
    simpa using graphMember
  rw [pointwise]
  exact (completedHistory_commits_projectedActions schedule).symm

end WeakMemory.TreiberRC11
