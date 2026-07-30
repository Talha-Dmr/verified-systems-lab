import WeakMemory.TreiberScheduledHistory

namespace WeakMemory.TreiberRC11

/-!
# Per-thread equivalence of source and scheduled commits

A respecting graph schedule may reorder commits from different client
threads.  It cannot reorder two commits from the same thread: canonical event
identifiers follow source occurrence order, generated program order relates
every increasing same-thread pair, and `RespectsGraph.programOrder` preserves
each such pair in the schedule.
-/

/-- Keep a graph event exactly when it commits an operation of one thread. -/
private def committedEventForThread?
    [DecidableEq α]
    (skeleton : EventGraph.Skeleton α)
    (thread : Nat)
    (event : Event α) :
    Option (Event α) :=
  match findAtomicSourceMetadata?
      1 (atomicSourceMetadata skeleton.labels) event with
  | none => none
  | some metadata =>
      match metadataCommit? metadata with
      | none => none
      | some _ =>
          if metadata.thread = thread then some event else none

/-- A metadata lookup can return only an element of the searched list. -/
private theorem findAtomicSourceMetadata?_some_mem
    [DecidableEq α]
    {next : EventId}
    {metadata : List (AtomicSourceMetadata α)}
    {event : Event α}
    {found : AtomicSourceMetadata α}
    (lookup :
      findAtomicSourceMetadata? next metadata event =
        some found) :
    found ∈ metadata := by
  induction metadata generalizing next with
  | nil =>
      simp [findAtomicSourceMetadata?] at lookup
  | cons source rest inductionHypothesis =>
      by_cases isHead :
          Event.mk next (.algorithm source.action) = event
      · simp [findAtomicSourceMetadata?, isHead] at lookup
        subst found
        simp
      · simp [findAtomicSourceMetadata?, isHead] at lookup
        exact List.mem_cons_of_mem source
          (inductionHypothesis lookup)

/-- A successful metadata lookup exposes the action of the selected event. -/
private theorem findAtomicSourceMetadata?_some_action
    [DecidableEq α]
    {next : EventId}
    {metadata : List (AtomicSourceMetadata α)}
    {event : Event α}
    {found : AtomicSourceMetadata α}
    (lookup :
      findAtomicSourceMetadata? next metadata event =
        some found) :
    event.action? = some found.action := by
  induction metadata generalizing next with
  | nil =>
      simp [findAtomicSourceMetadata?] at lookup
  | cons source rest inductionHypothesis =>
      by_cases isHead :
          Event.mk next (.algorithm source.action) = event
      · simp [findAtomicSourceMetadata?, isHead] at lookup
        subst found
        rw [← isHead]
        rfl
      · simp [findAtomicSourceMetadata?, isHead] at lookup
        exact inductionHypothesis lookup

/-- Atomic source metadata retains the ownership proof of its source label. -/
private theorem atomicSourceMetadata_actionThread
    {labels : List (EventGraph.OwnedLabel α)}
    {metadata : AtomicSourceMetadata α}
    (member : metadata ∈ atomicSourceMetadata labels) :
    ControlFlow.actionThread metadata.action =
      metadata.thread := by
  induction labels with
  | nil =>
      simp [atomicSourceMetadata] at member
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | invokePop operation =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | invokeIsEmpty operation =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | writeNext operation node next =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | readNext operation node next =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | respond operation response =>
          exact inductionHypothesis (by
            simpa [atomicSourceMetadata,
              atomicSourceMetadata?] using member)
      | atomic operation action =>
        simp only [atomicSourceMetadata, List.filterMap_cons,
          atomicSourceMetadata?, List.mem_cons] at member
        rcases member with isHead | inRest
        · subst metadata
          exact ownership
        · exact inductionHypothesis inRest

/-- An algorithm event's thread is the thread embedded in its action. -/
private theorem Event.thread?_eq_actionThread
    {event : Event α}
    {action : TreiberRA.Action α}
    (projects : event.action? = some action) :
    event.thread? =
      some (ControlFlow.actionThread action) := by
  rcases event with ⟨id, kind⟩
  cases kind with
  | initial =>
      simp [Event.action?] at projects
  | algorithm eventAction =>
      simp [Event.action?] at projects
      subst eventAction
      cases action <;> rfl

/-- A selected event really belongs to the requested client thread. -/
private theorem committedEventForThread?_thread
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    {thread : Nat}
    {event selected : Event α}
    (selection :
      committedEventForThread? skeleton thread event =
        some selected) :
    event.thread? = some thread := by
  unfold committedEventForThread? at selection
  cases lookup :
      findAtomicSourceMetadata?
        1 (atomicSourceMetadata skeleton.labels) event with
  | none =>
      simp [lookup] at selection
  | some metadata =>
      cases commits : metadataCommit? metadata with
      | none =>
          simp [lookup, commits] at selection
      | some entry =>
          by_cases sameThread : metadata.thread = thread
          · have actionThread :
                ControlFlow.actionThread metadata.action =
                  metadata.thread :=
              atomicSourceMetadata_actionThread
                (findAtomicSourceMetadata?_some_mem lookup)
            calc
              event.thread? =
                  some (ControlFlow.actionThread metadata.action) :=
                Event.thread?_eq_actionThread
                  (findAtomicSourceMetadata?_some_action lookup)
              _ = some thread := by
                rw [actionThread, sameThread]
          · simp [lookup, commits, sameThread] at selection

/-- Thread filtering never changes the selected event itself. -/
private theorem committedEventForThread?_eq_some_self
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    {thread : Nat}
    {event selected : Event α}
    (selection :
      committedEventForThread? skeleton thread event =
        some selected) :
    selected = event := by
  unfold committedEventForThread? at selection
  split at selection <;> try contradiction
  next metadata lookup =>
    split at selection <;> try contradiction
    next entry commits =>
      split at selection <;> simp_all

/-- Committed metadata projects to an entry owned by the metadata thread. -/
private theorem metadataCommit?_thread
    {metadata : AtomicSourceMetadata α}
    {entry : HerlihyWing.IdentifiedCompleted α}
    (commits : metadataCommit? metadata = some entry) :
    entry.thread = metadata.thread := by
  unfold metadataCommit? at commits
  cases actionCommits : metadata.action.commit? with
  | none =>
      simp [actionCommits] at commits
  | some commit =>
      simp [actionCommits] at commits
      subst entry
      rfl

/--
Filtering selected events and then recovering their commits is the same as
recovering all commits and retaining one thread.
-/
private theorem filterMap_committedEventForThread?
    [DecidableEq α]
    (skeleton : EventGraph.Skeleton α)
    (thread : Nat)
    (events : List (Event α)) :
    (events.filterMap
        (committedEventForThread? skeleton thread)).filterMap
          (identifiedEventCommit? skeleton) =
      HerlihyWing.operationsForThread thread
        (events.filterMap (identifiedEventCommit? skeleton)) := by
  induction events with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases lookup :
          findAtomicSourceMetadata?
            1 (atomicSourceMetadata skeleton.labels) event with
      | none =>
          have selected :
              committedEventForThread? skeleton thread event =
                none := by
            simp [committedEventForThread?, lookup]
          have commits :
              identifiedEventCommit? skeleton event =
                none := by
            simp [identifiedEventCommit?, lookup]
          simp only [List.filterMap_cons, selected, commits]
          exact inductionHypothesis
      | some metadata =>
          cases metadataCommits : metadataCommit? metadata with
          | none =>
              have selected :
                  committedEventForThread? skeleton thread event =
                    none := by
                simp [committedEventForThread?, lookup,
                  metadataCommits]
              have commits :
                  identifiedEventCommit? skeleton event =
                    none := by
                simp [identifiedEventCommit?, lookup,
                  metadataCommits]
              simp only [List.filterMap_cons, selected, commits]
              exact inductionHypothesis
          | some entry =>
              have entryThread :
                  entry.thread = metadata.thread :=
                metadataCommit?_thread metadataCommits
              have commits :
                  identifiedEventCommit? skeleton event =
                    some entry := by
                simp [identifiedEventCommit?, lookup,
                  metadataCommits]
              by_cases sameThread : metadata.thread = thread
              · have selected :
                    committedEventForThread? skeleton thread event =
                      some event := by
                  simp [committedEventForThread?, lookup,
                    metadataCommits, sameThread]
                have entryIsThread :
                    entry.thread = thread :=
                  entryThread.trans sameThread
                simp only [List.filterMap_cons, selected, commits,
                  HerlihyWing.operationsForThread, entryIsThread,
                  ↓reduceIte]
                exact congrArg (List.cons entry)
                  inductionHypothesis
              · have entryNotThread : entry.thread ≠ thread := by
                  rw [entryThread]
                  exact sameThread
                have selected :
                    committedEventForThread? skeleton thread event =
                      none := by
                  simp [committedEventForThread?, lookup,
                    metadataCommits, sameThread]
                simp only [List.filterMap_cons, selected, commits,
                  HerlihyWing.operationsForThread, entryNotThread,
                  ↓reduceIte]
                exact inductionHypothesis

/-- Both endpoints of a schedule-order witness belong to the schedule. -/
private theorem Before.endpoints
    {first second : Event α}
    {schedule : List (Event α)}
    (before : Before first second schedule) :
    first ∈ schedule ∧ second ∈ schedule := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst schedule
  simp

/-- Every earlier list position gives a decomposition-based `Before` witness. -/
private theorem pairwise_before_self
    (events : List (Event α)) :
    events.Pairwise
      (fun first second => Before first second events) := by
  induction events with
  | nil =>
      exact List.Pairwise.nil
  | cons first rest inductionHypothesis =>
      apply List.Pairwise.cons
      · intro second member
        obtain ⟨between, later, restShape⟩ :=
          List.append_of_mem member
        subst rest
        exact ⟨[], between, later, rfl⟩
      · apply inductionHypothesis.imp
        intro earlier later before
        rcases before with
          ⟨leading, between, trailing, shape⟩
        subst rest
        exact ⟨first :: leading, between, trailing, rfl⟩

/-- Inductive order view used to rule out two opposite `Before` witnesses. -/
private inductive ListPrecedes
    (first second : Event α) :
    List (Event α) → Prop where
  | here {tail} :
      second ∈ tail →
      ListPrecedes first second (first :: tail)
  | there {head tail} :
      ListPrecedes first second tail →
      ListPrecedes first second (head :: tail)

private theorem ListPrecedes.second_mem
    {first second : Event α}
    {events : List (Event α)}
    (precedes : ListPrecedes first second events) :
    second ∈ events := by
  induction precedes with
  | here member =>
      simp [member]
  | there later inductionHypothesis =>
      simp [inductionHypothesis]

private theorem Before.toListPrecedes
    {first second : Event α}
    {events : List (Event α)}
    (before : Before first second events) :
    ListPrecedes first second events := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst events
  induction earlier with
  | nil =>
      apply ListPrecedes.here
      simp
  | cons head tail inductionHypothesis =>
      exact ListPrecedes.there inductionHypothesis

private theorem ListPrecedes.asymm
    {first second : Event α}
    {events : List (Event α)}
    (noDuplicates : events.Nodup)
    (forward : ListPrecedes first second events) :
    ¬ ListPrecedes second first events := by
  induction forward with
  | @here tail secondInTail =>
      intro reverse
      have firstNotInTail :=
        (List.nodup_cons.mp noDuplicates).1
      cases reverse with
      | here firstInTail =>
          exact firstNotInTail firstInTail
      | there reverseTail =>
          exact firstNotInTail reverseTail.second_mem
  | @there head tail forward inductionHypothesis =>
      intro reverse
      have headNotInTail :=
        (List.nodup_cons.mp noDuplicates).1
      have tailNodup :=
        (List.nodup_cons.mp noDuplicates).2
      cases reverse with
      | here firstInTail =>
          exact headNotInTail forward.second_mem
      | there reverseTail =>
          exact inductionHypothesis tailNodup reverseTail

private theorem Before.asymm
    {first second : Event α}
    {events : List (Event α)}
    (noDuplicates : events.Nodup)
    (forward : Before first second events) :
    ¬ Before second first events := by
  intro reverse
  exact
    (Before.toListPrecedes forward).asymm noDuplicates
      (Before.toListPrecedes reverse)

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
Every respecting schedule preserves the source order of each client's
completed operations.
-/
theorem SourceAtomicExecution.scheduleEquivalent
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {schedule : List (Event α)}
    (respects :
      RespectsGraph execution.relations.graph schedule) :
    HerlihyWing.Equivalent
      (sourceCommittedOperations execution.source.skeleton)
      (scheduledOperations execution schedule) := by
  refine ⟨
    sourceCommittedOperations_perm_scheduledOperations
      execution respects,
    ?_⟩
  intro thread
  let select :=
    committedEventForThread?
      execution.source.skeleton thread
  have carrierPermutation :
      execution.source.skeleton.events.Perm schedule :=
    sourceEvents_perm_schedule execution respects
  have selectedPermutation :
      (execution.source.skeleton.events.filterMap select).Perm
        (schedule.filterMap select) :=
    carrierPermutation.filterMap select
  have sourceSorted :
      (execution.source.skeleton.events.filterMap select).Pairwise
        (fun first second => first.id ≤ second.id) := by
    rw [List.pairwise_filterMap]
    apply execution.source.skeleton.events_pairwise_id_lt.imp
    intro first second earlier
      firstSelected firstSelection secondSelected secondSelection
    have firstSame :
        firstSelected = first :=
      committedEventForThread?_eq_some_self firstSelection
    have secondSame :
        secondSelected = second :=
      committedEventForThread?_eq_some_self secondSelection
    subst firstSelected
    subst secondSelected
    exact Nat.le_of_lt earlier
  have scheduleSorted :
      (schedule.filterMap select).Pairwise
        (fun first second => first.id ≤ second.id) := by
    rw [List.pairwise_filterMap]
    apply (pairwise_before_self schedule).imp
    intro first second forward
      firstSelected firstSelection secondSelected secondSelection
    have firstSame :
        firstSelected = first :=
      committedEventForThread?_eq_some_self firstSelection
    have secondSame :
        secondSelected = second :=
      committedEventForThread?_eq_some_self secondSelection
    subst firstSelected
    subst secondSelected
    apply Nat.le_of_not_gt
    intro reverseIds
    have firstThread :
        first.thread? = some thread :=
      committedEventForThread?_thread firstSelection
    have secondThread :
        second.thread? = some thread :=
      committedEventForThread?_thread secondSelection
    have endpoints := forward.endpoints
    have reverseProgramOrder :
        execution.relations.graph.programOrder second first := by
      change execution.source.skeleton.programOrder second first
      exact ⟨
        (respects.covers second).mpr endpoints.2,
        (respects.covers first).mpr endpoints.1,
        thread, secondThread, firstThread, reverseIds⟩
    exact
      (forward.asymm respects.noDuplicates)
        (respects.programOrder reverseProgramOrder)
  have selectedEqual :
      execution.source.skeleton.events.filterMap select =
        schedule.filterMap select := by
    apply List.Perm.eq_of_pairwise
      (le := fun first second : Event α =>
        first.id ≤ second.id)
    · intro first second firstMember secondMember
        firstBefore secondBefore
      apply execution.source.skeleton.uniqueIds
      · obtain ⟨origin, originMember, selected⟩ :=
          List.mem_filterMap.mp firstMember
        have same :
            first = origin :=
          committedEventForThread?_eq_some_self selected
        simpa [same] using originMember
      · have secondInSchedule :
            second ∈ schedule := by
          obtain ⟨origin, originMember, selected⟩ :=
            List.mem_filterMap.mp secondMember
          have same :
              second = origin :=
            committedEventForThread?_eq_some_self selected
          simpa [same] using originMember
        exact (respects.covers second).mpr secondInSchedule
      · exact Nat.le_antisymm firstBefore secondBefore
    · exact sourceSorted
    · exact scheduleSorted
    · exact selectedPermutation
  rw [← filterMap_identifiedEventCommit_eq_source]
  unfold scheduledOperations
  rw [
    ← filterMap_committedEventForThread?
      execution.source.skeleton thread
        execution.source.skeleton.events,
    ← filterMap_committedEventForThread?
      execution.source.skeleton thread schedule,
    selectedEqual
  ]

end WeakMemory.TreiberRC11
