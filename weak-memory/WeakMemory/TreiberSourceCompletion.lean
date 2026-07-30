import WeakMemory.TreiberMethodTrace
import WeakMemory.TreiberScheduledHistory

namespace WeakMemory.TreiberRC11

/-!
# Completing source histories

The source method trace retains invocation, abstract commit, and response
events.  This module proves that its commit projection is a Herlihy--Wing
completion of its client-visible projection.  In particular, an operation
whose source prefix ends after its commit but before its response is selected
as a pending completed operation.
-/

namespace SourceCompletion

/-- An inductive presentation of strict list order. -/
private inductive ListPrecedes (first second : β) : List β → Prop where
  | head {rest : List β} :
      second ∈ rest →
      ListPrecedes first second (first :: rest)
  | tail {item : β} {rest : List β} :
      ListPrecedes first second rest →
      ListPrecedes first second (item :: rest)

namespace ListPrecedes

private theorem first_mem
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    first ∈ items := by
  induction precedes with
  | head =>
      simp
  | tail _ inductionHypothesis =>
      exact List.mem_cons_of_mem _ inductionHypothesis

private theorem second_mem
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    second ∈ items := by
  induction precedes with
  | head member =>
      exact List.mem_cons_of_mem _ member
  | tail _ inductionHypothesis =>
      exact List.mem_cons_of_mem _ inductionHypothesis

private theorem toBefore
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    HerlihyWing.Before first second items := by
  induction precedes with
  | @head rest member =>
      obtain ⟨between, later, shape⟩ :=
        List.append_of_mem member
      exact ⟨[], between, later, by simp [shape]⟩
  | @tail item rest _ inductionHypothesis =>
      obtain ⟨earlier, between, later, shape⟩ :=
        inductionHypothesis
      exact ⟨item :: earlier, between, later, by
        simp [shape]⟩

private theorem ofBefore
    {first second : β}
    {items : List β}
    (before : HerlihyWing.Before first second items) :
    ListPrecedes first second items := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  induction earlier with
  | nil =>
      apply ListPrecedes.head
      simp
  | cons item rest inductionHypothesis =>
      exact ListPrecedes.tail inductionHypothesis

private theorem of_pair_sublist
    {first second : β}
    {items : List β}
    (sublist : [first, second].Sublist items) :
    ListPrecedes first second items := by
  induction items with
  | nil =>
      cases sublist
  | cons item rest inductionHypothesis =>
      cases sublist with
      | cons _ tailSublist =>
          exact ListPrecedes.tail
            (inductionHypothesis tailSublist)
      | cons_cons _ tailSublist =>
          apply ListPrecedes.head
          exact tailSublist.subset (by simp)

private theorem filterMap
    {first second : β}
    {items : List β}
    {project : β → Option γ}
    {projectedFirst projectedSecond : γ}
    (precedes : ListPrecedes first second items)
    (firstProjects : project first = some projectedFirst)
    (secondProjects : project second = some projectedSecond) :
    ListPrecedes projectedFirst projectedSecond
      (items.filterMap project) := by
  induction precedes with
  | @head rest secondMember =>
      simp only [List.filterMap_cons, firstProjects]
      apply ListPrecedes.head
      exact List.mem_filterMap.mpr
        ⟨second, secondMember, secondProjects⟩
  | @tail item rest _ inductionHypothesis =>
      simp only [List.filterMap_cons]
      cases project item <;>
        simp only
      · exact inductionHypothesis
      · exact ListPrecedes.tail inductionHypothesis

private theorem of_filterMap
    {first second : β}
    {items : List β}
    {project : β → Option γ}
    {projectedFirst projectedSecond : γ}
    (precedes :
      ListPrecedes projectedFirst projectedSecond
        (items.filterMap project))
    (firstUnique :
      ∀ item,
        project item = some projectedFirst →
        item = first)
    (secondUnique :
      ∀ item,
        project item = some projectedSecond →
        item = second) :
    ListPrecedes first second items := by
  induction items generalizing first second with
  | nil =>
      cases precedes
  | cons item rest inductionHypothesis =>
      simp only [List.filterMap_cons] at precedes
      cases projected : project item with
      | none =>
          simp only [projected] at precedes
          exact ListPrecedes.tail
            (inductionHypothesis precedes firstUnique secondUnique)
      | some output =>
          simp only [projected] at precedes
          cases precedes with
          | head secondMember =>
              have itemIsFirst :
                  item = first :=
                firstUnique item projected
              subst item
              apply ListPrecedes.head
              obtain ⟨source, sourceMember, sourceProjects⟩ :=
                List.mem_filterMap.mp secondMember
              have sourceIsSecond :
                  source = second :=
                secondUnique source sourceProjects
              simpa [sourceIsSecond] using sourceMember
          | tail later =>
              exact ListPrecedes.tail
                (inductionHypothesis later firstUnique secondUnique)

private theorem map
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items)
    (project : β → γ) :
    ListPrecedes (project first) (project second)
      (items.map project) := by
  induction precedes with
  | head secondMember =>
      apply ListPrecedes.head
      exact List.mem_map.mpr
        ⟨second, secondMember, rfl⟩
  | tail _ inductionHypothesis =>
      exact ListPrecedes.tail inductionHypothesis

private theorem not_of_nodup_self
    {item : β}
    {items : List β}
    (noDuplicates : items.Nodup) :
    ¬ ListPrecedes item item items := by
  intro precedes
  induction precedes with
  | head member =>
      exact (List.nodup_cons.mp noDuplicates).1 member
  | tail _ inductionHypothesis =>
      exact inductionHypothesis
        (List.nodup_cons.mp noDuplicates).2

private theorem not_before_head_of_nodup
    {first head : β}
    {rest : List β}
    (noDuplicates : (head :: rest).Nodup) :
    ¬ ListPrecedes first head (head :: rest) := by
  intro precedes
  cases precedes with
  | head member =>
      exact (List.nodup_cons.mp noDuplicates).1 member
  | tail later =>
      exact (List.nodup_cons.mp noDuplicates).1
        later.second_mem

private theorem tail_of_cons_of_first_ne
    {first second head : β}
    {rest : List β}
    (precedes :
      ListPrecedes first second (head :: rest))
    (firstNotHead : first ≠ head) :
    ListPrecedes first second rest := by
  cases precedes with
  | head =>
      exact False.elim (firstNotHead rfl)
  | tail later =>
      exact later

private theorem total_of_mem_of_mem_of_ne
    {first second : β}
    {items : List β}
    (firstMember : first ∈ items)
    (secondMember : second ∈ items)
    (different : first ≠ second) :
    ListPrecedes first second items ∨
      ListPrecedes second first items := by
  induction items generalizing first second with
  | nil =>
      simp at firstMember
  | cons item rest inductionHypothesis =>
      rcases List.mem_cons.mp firstMember with firstIsHead | firstInRest
      · subst item
        exact Or.inl (ListPrecedes.head
          ((List.mem_cons.mp secondMember).resolve_left
            different.symm))
      · rcases List.mem_cons.mp secondMember with
          secondIsHead | secondInRest
        · subst item
          exact Or.inr (ListPrecedes.head firstInRest)
        · exact (inductionHypothesis
            firstInRest secondInRest different).imp
              ListPrecedes.tail ListPrecedes.tail

end ListPrecedes

/--
The only possible finite traces of a method machine that starts idle.
-/
private inductive ThreadChunks :
    List (MethodTrace.Event α) → Prop where
  | nil :
      ThreadChunks []
  | pending
      (invocation : HerlihyWing.Invocation α) :
      ThreadChunks [.invoke invocation]
  | committed
      (entry : HerlihyWing.IdentifiedCompleted α) :
      ThreadChunks [
        .invoke entry.invocation,
        .commit entry
      ]
  | completed
      (entry : HerlihyWing.IdentifiedCompleted α)
      {rest : List (MethodTrace.Event α)} :
      ThreadChunks rest →
      ThreadChunks (
        .invoke entry.invocation ::
        .commit entry ::
        .respond entry.returned ::
        rest)

namespace ThreadChunks

private theorem ofThreadForm
    {events : List (MethodTrace.Event α)}
    (shape : MethodTrace.ThreadForm events) :
    ThreadChunks events := by
  cases shape with
  | nil =>
      exact .nil
  | invoke pendingShape =>
      cases pendingShape with
      | nil =>
          exact .pending _
      | commit committedShape =>
          cases committedShape with
          | nil =>
              exact .committed _
          | respond restShape =>
              exact .completed _ (ofThreadForm restShape)

private theorem commit_invocation_mem
    {events : List (MethodTrace.Event α)}
    (shape : ThreadChunks events)
    {entry : HerlihyWing.IdentifiedCompleted α}
    (commitMember :
      MethodTrace.Event.commit entry ∈ events) :
    MethodTrace.Event.invoke entry.invocation ∈ events := by
  induction shape with
  | nil =>
      simp at commitMember
  | pending =>
      simp at commitMember
  | committed selected =>
      simp only [List.mem_cons] at commitMember
      rcases commitMember with impossible | isSelected | impossible
      · contradiction
      · injection isSelected with entryShape
        subst entry
        simp
      · contradiction
  | @completed selected rest restShape inductionHypothesis =>
      simp only [List.mem_cons] at commitMember
      rcases commitMember with impossible |
          isSelected | impossible | inRest
      · contradiction
      · injection isSelected with entryShape
        subst entry
        simp
      · contradiction
      · exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (inductionHypothesis inRest)))

private theorem response_context
    {events : List (MethodTrace.Event α)}
    (shape : ThreadChunks events)
    {returned : HerlihyWing.Return α}
    (responseMember :
      MethodTrace.Event.respond returned ∈ events) :
    ∃ entry : HerlihyWing.IdentifiedCompleted α,
      MethodTrace.Event.commit entry ∈ events ∧
        entry.returned = returned ∧
        ListPrecedes
          (MethodTrace.Event.invoke entry.invocation)
          (MethodTrace.Event.respond returned)
          events := by
  induction shape with
  | nil =>
      simp at responseMember
  | pending =>
      simp at responseMember
  | committed =>
      simp at responseMember
  | @completed selected rest restShape inductionHypothesis =>
      simp only [List.mem_cons] at responseMember
      rcases responseMember with impossible |
          impossible | isSelected | inRest
      · contradiction
      · contradiction
      · injection isSelected with returnedShape
        subst returned
        refine ⟨selected, by simp, rfl, ?_⟩
        apply ListPrecedes.head
        simp
      · obtain ⟨entry, commitMember, returnedShape,
          invocationBeforeResponse⟩ :=
          inductionHypothesis inRest
        refine ⟨entry, ?_, returnedShape, ?_⟩
        · simp [commitMember]
        · exact ListPrecedes.tail
            (ListPrecedes.tail
              (ListPrecedes.tail
                invocationBeforeResponse))

private theorem commitIds_sublist_invocationIds
    {events : List (MethodTrace.Event α)}
    (shape : ThreadChunks events) :
    (MethodTrace.completedOperations events).map
        HerlihyWing.IdentifiedCompleted.id
      |>.Sublist
        (HerlihyWing.invocationIds
          (MethodTrace.history events)) := by
  induction shape with
  | nil =>
      exact .refl []
  | pending invocation =>
      exact .cons _ (.refl [])
  | committed entry =>
      exact .refl [entry.id]
  | @completed entry rest restShape inductionHypothesis =>
      exact .cons_cons entry.id inductionHypothesis

private theorem commit_order_of_id_order
    {events : List (MethodTrace.Event α)}
    (shape : ThreadChunks events)
    (invocationIdsNodup :
      (HerlihyWing.invocationIds
        (MethodTrace.history events)).Nodup)
    {first second : HerlihyWing.IdentifiedCompleted α}
    (firstMember :
      first ∈ MethodTrace.completedOperations events)
    (secondMember :
      second ∈ MethodTrace.completedOperations events)
    (idOrder :
      ListPrecedes first.id second.id
        (HerlihyWing.invocationIds
          (MethodTrace.history events))) :
    ListPrecedes first second
      (MethodTrace.completedOperations events) := by
  induction shape with
  | nil =>
      simp [MethodTrace.completedOperations] at firstMember
  | pending =>
      simp [MethodTrace.completedOperations,
        MethodTrace.Event.completed?] at firstMember
  | committed selected =>
      have firstShape : first = selected := by
        simpa [MethodTrace.completedOperations,
          MethodTrace.Event.completed?] using firstMember
      have secondShape : second = selected := by
        simpa [MethodTrace.completedOperations,
          MethodTrace.Event.completed?] using secondMember
      subst first
      subst second
      exact False.elim
        (ListPrecedes.not_of_nodup_self
          invocationIdsNodup idOrder)
  | @completed selected rest restShape inductionHypothesis =>
      have operationShape :
          MethodTrace.completedOperations
              (MethodTrace.Event.invoke selected.invocation ::
                MethodTrace.Event.commit selected ::
                MethodTrace.Event.respond selected.returned ::
                rest) =
            selected ::
              MethodTrace.completedOperations rest := by
        rfl
      have invocationShape :
          HerlihyWing.invocationIds
              (MethodTrace.history
                (MethodTrace.Event.invoke selected.invocation ::
                  MethodTrace.Event.commit selected ::
                  MethodTrace.Event.respond selected.returned ::
                  rest)) =
            selected.id ::
              HerlihyWing.invocationIds
                (MethodTrace.history rest) := by
        rfl
      rw [operationShape] at firstMember secondMember ⊢
      rw [invocationShape] at invocationIdsNodup idOrder
      have restInvocationNodup :=
        (List.nodup_cons.mp invocationIdsNodup).2
      rcases List.mem_cons.mp firstMember with
          firstIsSelected | firstInRest
      · subst first
        rcases List.mem_cons.mp secondMember with
            secondIsSelected | secondInRest
        · subst second
          exact False.elim
            (ListPrecedes.not_of_nodup_self
              invocationIdsNodup idOrder)
        · exact ListPrecedes.head secondInRest
      · rcases List.mem_cons.mp secondMember with
            secondIsSelected | secondInRest
        · subst second
          exact False.elim
            (ListPrecedes.not_before_head_of_nodup
              invocationIdsNodup idOrder)
        · have firstIdInRest :
              first.id ∈
                HerlihyWing.invocationIds
                  (MethodTrace.history rest) :=
            ((commitIds_sublist_invocationIds restShape).subset
              (List.mem_map.mpr
                ⟨first, firstInRest, rfl⟩))
          have firstIdNotSelected :
              first.id ≠ selected.id := by
            intro same
            exact (List.nodup_cons.mp
              invocationIdsNodup).1
                (same ▸ firstIdInRest)
          have restOrder :
              ListPrecedes first.id second.id
                (HerlihyWing.invocationIds
                  (MethodTrace.history rest)) :=
            ListPrecedes.tail_of_cons_of_first_ne
              idOrder firstIdNotSelected
          exact ListPrecedes.tail
            (inductionHypothesis restInvocationNodup
              firstInRest secondInRest restOrder)

end ThreadChunks

/-- Keep a method event exactly when it belongs to the selected thread. -/
private def eventForThread?
    (thread : Nat)
    (event : MethodTrace.Event α) :
    Option (MethodTrace.Event α) :=
  if event.thread = thread then some event else none

private theorem eventsForThread_eq_filterMap
    (thread : Nat)
    (events : List (MethodTrace.Event α)) :
    MethodTrace.eventsForThread thread events =
      events.filterMap (eventForThread? thread) := by
  induction events with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      by_cases eventThread : event.thread = thread <;>
        simp [MethodTrace.eventsForThread, eventForThread?,
          eventThread, inductionHypothesis]

private theorem eventsForThread_sublist
    (thread : Nat)
    (events : List (MethodTrace.Event α)) :
    (MethodTrace.eventsForThread thread events).Sublist events := by
  induction events with
  | nil =>
      exact .refl []
  | cons event rest inductionHypothesis =>
      by_cases eventThread : event.thread = thread
      · simp only [MethodTrace.eventsForThread, eventThread,
          ↓reduceIte]
        exact .cons_cons event inductionHypothesis
      · simp only [MethodTrace.eventsForThread, eventThread,
          ↓reduceIte]
        exact .cons event inductionHypothesis

private theorem mem_eventsForThread_of_mem
    {thread : Nat}
    {event : MethodTrace.Event α}
    {events : List (MethodTrace.Event α)}
    (member : event ∈ events)
    (eventThread : event.thread = thread) :
    event ∈ MethodTrace.eventsForThread thread events := by
  rw [eventsForThread_eq_filterMap]
  apply List.mem_filterMap.mpr
  exact ⟨event, member, by
    simp [eventForThread?, eventThread]⟩

private theorem precedes_eventsForThread
    {thread : Nat}
    {first second : MethodTrace.Event α}
    {events : List (MethodTrace.Event α)}
    (precedes : ListPrecedes first second events)
    (firstThread : first.thread = thread)
    (secondThread : second.thread = thread) :
    ListPrecedes first second
      (MethodTrace.eventsForThread thread events) := by
  rw [eventsForThread_eq_filterMap]
  apply precedes.filterMap
  · simp [eventForThread?, firstThread]
  · simp [eventForThread?, secondThread]

private theorem precedes_of_eventsForThread
    {thread : Nat}
    {first second : MethodTrace.Event α}
    {events : List (MethodTrace.Event α)}
    (precedes :
      ListPrecedes first second
        (MethodTrace.eventsForThread thread events)) :
    ListPrecedes first second events := by
  rw [eventsForThread_eq_filterMap] at precedes
  apply ListPrecedes.of_filterMap precedes
  · intro event projects
    simp only [eventForThread?] at projects
    split at projects
    · simpa using projects
    · contradiction
  · intro event projects
    simp only [eventForThread?] at projects
    split at projects
    · simpa using projects
    · contradiction

private theorem history_invoke_mem
    {events : List (MethodTrace.Event α)}
    {invocation : HerlihyWing.Invocation α} :
    HerlihyWing.HistoryEvent.invoke invocation ∈
        MethodTrace.history events ↔
      MethodTrace.Event.invoke invocation ∈ events := by
  constructor
  · intro member
    obtain ⟨event, eventMember, projects⟩ :=
      List.mem_filterMap.mp member
    cases event with
    | invoke source =>
        simp [MethodTrace.Event.historyEvent?] at projects
        simpa [projects] using eventMember
    | commit =>
        simp [MethodTrace.Event.historyEvent?] at projects
    | respond =>
        simp [MethodTrace.Event.historyEvent?] at projects
  · intro member
    exact List.mem_filterMap.mpr
      ⟨.invoke invocation, member, rfl⟩

private theorem history_respond_mem
    {events : List (MethodTrace.Event α)}
    {returned : HerlihyWing.Return α} :
    HerlihyWing.HistoryEvent.respond returned ∈
        MethodTrace.history events ↔
      MethodTrace.Event.respond returned ∈ events := by
  constructor
  · intro member
    obtain ⟨event, eventMember, projects⟩ :=
      List.mem_filterMap.mp member
    cases event with
    | invoke =>
        simp [MethodTrace.Event.historyEvent?] at projects
    | commit =>
        simp [MethodTrace.Event.historyEvent?] at projects
    | respond source =>
        simp [MethodTrace.Event.historyEvent?] at projects
        simpa [projects] using eventMember
  · intro member
    exact List.mem_filterMap.mpr
      ⟨.respond returned, member, rfl⟩

private theorem completed_mem
    {events : List (MethodTrace.Event α)}
    {entry : HerlihyWing.IdentifiedCompleted α} :
    entry ∈ MethodTrace.completedOperations events ↔
      MethodTrace.Event.commit entry ∈ events := by
  constructor
  · intro member
    obtain ⟨event, eventMember, projects⟩ :=
      List.mem_filterMap.mp member
    cases event with
    | invoke =>
        simp [MethodTrace.Event.completed?] at projects
    | commit source =>
        simp [MethodTrace.Event.completed?] at projects
        simpa [projects] using eventMember
    | respond =>
        simp [MethodTrace.Event.completed?] at projects
  · intro member
    exact List.mem_filterMap.mpr
      ⟨.commit entry, member, rfl⟩

private theorem precedes_history_invocations
    {events : List (MethodTrace.Event α)}
    {first second : HerlihyWing.Invocation α}
    (precedes :
      ListPrecedes
        (HerlihyWing.HistoryEvent.invoke first)
        (HerlihyWing.HistoryEvent.invoke second)
        (MethodTrace.history events)) :
    ListPrecedes
      (MethodTrace.Event.invoke first)
      (MethodTrace.Event.invoke second)
      events := by
  apply ListPrecedes.of_filterMap precedes
  · intro event projects
    cases event <;>
      simp [MethodTrace.Event.historyEvent?] at projects
    simp [projects]
  · intro event projects
    cases event <;>
      simp [MethodTrace.Event.historyEvent?] at projects
    simp [projects]

private theorem precedes_history_of_trace
    {events : List (MethodTrace.Event α)}
    {entry : HerlihyWing.IdentifiedCompleted α}
    (precedes :
      ListPrecedes
        (MethodTrace.Event.invoke entry.invocation)
        (MethodTrace.Event.respond entry.returned)
        events) :
    ListPrecedes
      (HerlihyWing.HistoryEvent.invoke entry.invocation)
      (HerlihyWing.HistoryEvent.respond entry.returned)
      (MethodTrace.history events) :=
  precedes.filterMap rfl rfl

private theorem precedes_completed_of_trace
    {events : List (MethodTrace.Event α)}
    {first second : HerlihyWing.IdentifiedCompleted α}
    (precedes :
      ListPrecedes
        (MethodTrace.Event.commit first)
        (MethodTrace.Event.commit second)
        events) :
    ListPrecedes first second
      (MethodTrace.completedOperations events) :=
  precedes.filterMap rfl rfl

private theorem precedes_trace_of_completed
    {events : List (MethodTrace.Event α)}
    {first second : HerlihyWing.IdentifiedCompleted α}
    (precedes :
      ListPrecedes first second
        (MethodTrace.completedOperations events)) :
    ListPrecedes
      (MethodTrace.Event.commit first)
      (MethodTrace.Event.commit second)
      events := by
  apply ListPrecedes.of_filterMap precedes
  · intro event projects
    cases event <;>
      simp [MethodTrace.Event.completed?] at projects
    simp [projects]
  · intro event projects
    cases event <;>
      simp [MethodTrace.Event.completed?] at projects
    simp [projects]

private theorem invocationIds_sourceHistory
    (labels : List (EventGraph.OwnedLabel α)) :
    HerlihyWing.invocationIds
        (sourceHistory
          ({ labels := labels } : EventGraph.Skeleton α)) =
      Interleaving.invocationOperations labels := by
  induction labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      have tailSame :
          (rest.filterMap sourceHistoryEvent?).filterMap
              HerlihyWing.HistoryEvent.invocationId? =
            rest.filterMap
              Interleaving.invocationOperation? := by
        simpa [sourceHistory,
          HerlihyWing.invocationIds,
          Interleaving.invocationOperations] using
          inductionHypothesis
      cases label <;>
        simp [sourceHistory, sourceHistoryEvent?,
          HerlihyWing.invocationIds,
          HerlihyWing.HistoryEvent.invocationId?,
          Interleaving.invocationOperations,
          Interleaving.invocationOperation?,
          tailSame]

private theorem completedOperationIdsNodup
    {events : List (MethodTrace.Event α)}
    (invocationIdsNodup :
      (HerlihyWing.invocationIds
        (MethodTrace.history events)).Nodup)
    (threadChunks :
      ∀ thread,
        ThreadChunks
          (MethodTrace.eventsForThread thread events)) :
    (MethodTrace.completedOperations events |>.map
      HerlihyWing.IdentifiedCompleted.id).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map,
    List.pairwise_iff_forall_sublist]
  intro first second pairSublist
  intro sameId
  have operationOrder :
      ListPrecedes first second
        (MethodTrace.completedOperations events) :=
    ListPrecedes.of_pair_sublist pairSublist
  have commitOrder :
      ListPrecedes
        (MethodTrace.Event.commit first)
        (MethodTrace.Event.commit second)
        events :=
    precedes_trace_of_completed operationOrder
  by_cases sameThread : first.thread = second.thread
  · have localCommitOrder :
        ListPrecedes
          (MethodTrace.Event.commit first)
          (MethodTrace.Event.commit second)
          (MethodTrace.eventsForThread first.thread events) :=
      precedes_eventsForThread commitOrder
        (by rfl)
        (by
          simp [MethodTrace.Event.thread, sameThread])
    have localOperationOrder :
        ListPrecedes first second
          (MethodTrace.completedOperations
            (MethodTrace.eventsForThread first.thread events)) :=
      precedes_completed_of_trace localCommitOrder
    have localIdOrder :
        ListPrecedes first.id second.id
          ((MethodTrace.completedOperations
              (MethodTrace.eventsForThread first.thread events)).map
            HerlihyWing.IdentifiedCompleted.id) :=
      localOperationOrder.map
        HerlihyWing.IdentifiedCompleted.id
    have localHistorySublist :
        (MethodTrace.history
            (MethodTrace.eventsForThread first.thread events)).Sublist
          (MethodTrace.history events) :=
      (eventsForThread_sublist first.thread events).filterMap
        MethodTrace.Event.historyEvent?
    have localInvocationIdsNodup :
        (HerlihyWing.invocationIds
          (MethodTrace.history
            (MethodTrace.eventsForThread
              first.thread events))).Nodup :=
      ((localHistorySublist.filterMap
        HerlihyWing.HistoryEvent.invocationId?).nodup
          invocationIdsNodup)
    have localCommitIdsNodup :
        ((MethodTrace.completedOperations
            (MethodTrace.eventsForThread first.thread events)).map
          HerlihyWing.IdentifiedCompleted.id).Nodup :=
      ((ThreadChunks.commitIds_sublist_invocationIds
          (threadChunks first.thread)).nodup
        localInvocationIdsNodup)
    apply ListPrecedes.not_of_nodup_self
      localCommitIdsNodup
    simpa [sameId] using localIdOrder
  · have firstCommitMember :
        MethodTrace.Event.commit first ∈ events :=
      commitOrder.first_mem
    have secondCommitMember :
        MethodTrace.Event.commit second ∈ events :=
      commitOrder.second_mem
    have firstInvocationLocal :
        MethodTrace.Event.invoke first.invocation ∈
          MethodTrace.eventsForThread first.thread events :=
      (threadChunks first.thread).commit_invocation_mem
        (mem_eventsForThread_of_mem firstCommitMember (by rfl))
    have secondInvocationLocal :
        MethodTrace.Event.invoke second.invocation ∈
          MethodTrace.eventsForThread second.thread events :=
      (threadChunks second.thread).commit_invocation_mem
        (mem_eventsForThread_of_mem secondCommitMember (by rfl))
    have firstInvocationMember :
        MethodTrace.Event.invoke first.invocation ∈ events :=
      (eventsForThread_sublist first.thread events).subset
        firstInvocationLocal
    have secondInvocationMember :
        MethodTrace.Event.invoke second.invocation ∈ events :=
      (eventsForThread_sublist second.thread events).subset
        secondInvocationLocal
    have invocationDifferent :
        MethodTrace.Event.invoke first.invocation ≠
          MethodTrace.Event.invoke second.invocation := by
      intro equal
      have threadEqual :=
        congrArg MethodTrace.Event.thread equal
      change first.thread = second.thread at threadEqual
      exact sameThread threadEqual
    rcases ListPrecedes.total_of_mem_of_mem_of_ne
        firstInvocationMember secondInvocationMember
        invocationDifferent with
      firstBeforeSecond | secondBeforeFirst
    · have idOrder :=
        (firstBeforeSecond.filterMap
          (project := MethodTrace.Event.historyEvent?)
          rfl rfl).filterMap
            (project :=
              HerlihyWing.HistoryEvent.invocationId?)
            rfl rfl
      change
        ListPrecedes first.id second.id
          (HerlihyWing.invocationIds
            (MethodTrace.history events))
        at idOrder
      apply ListPrecedes.not_of_nodup_self invocationIdsNodup
      simpa [sameId] using idOrder
    · have idOrder :=
        (secondBeforeFirst.filterMap
          (project := MethodTrace.Event.historyEvent?)
          rfl rfl).filterMap
            (project :=
              HerlihyWing.HistoryEvent.invocationId?)
            rfl rfl
      change
        ListPrecedes second.id first.id
          (HerlihyWing.invocationIds
            (MethodTrace.history events))
        at idOrder
      apply ListPrecedes.not_of_nodup_self invocationIdsNodup
      simpa [sameId] using idOrder

private theorem completed_eq_of_id_eq
    {events : List (MethodTrace.Event α)}
    (operationIdsNodup :
      (MethodTrace.completedOperations events |>.map
        HerlihyWing.IdentifiedCompleted.id).Nodup)
    {first second : HerlihyWing.IdentifiedCompleted α}
    (firstMember :
      first ∈ MethodTrace.completedOperations events)
    (secondMember :
      second ∈ MethodTrace.completedOperations events)
    (sameId : first.id = second.id) :
    first = second := by
  classical
  by_cases equal : first = second
  · exact equal
  rcases ListPrecedes.total_of_mem_of_mem_of_ne
      firstMember secondMember equal with
    firstBeforeSecond | secondBeforeFirst
  · exact False.elim
      (ListPrecedes.not_of_nodup_self operationIdsNodup
        (by
          simpa [sameId] using
            (firstBeforeSecond.map
              HerlihyWing.IdentifiedCompleted.id)))
  · exact False.elim
      (ListPrecedes.not_of_nodup_self operationIdsNodup
        (by
          simpa [sameId] using
            (secondBeforeFirst.map
              HerlihyWing.IdentifiedCompleted.id)))

private theorem completion_of_threadChunks
    {events : List (MethodTrace.Event α)}
    (invocationIdsNodup :
      (HerlihyWing.invocationIds
        (MethodTrace.history events)).Nodup)
    (threadChunks :
      ∀ thread,
        ThreadChunks
          (MethodTrace.eventsForThread thread events)) :
    HerlihyWing.Completion
      (MethodTrace.history events)
      (MethodTrace.completedOperations events) := by
  let operationIdsNodup :=
    completedOperationIdsNodup invocationIdsNodup threadChunks
  refine {
    operationIdsNodup := operationIdsNodup
    selected := ?_
    retainsReturns := ?_
    threadOrder := ?_
  }
  · intro entry entryMember
    have commitMember :
        MethodTrace.Event.commit entry ∈ events :=
      completed_mem.mp entryMember
    let localEvents :=
      MethodTrace.eventsForThread entry.thread events
    have localCommitMember :
        MethodTrace.Event.commit entry ∈ localEvents :=
      mem_eventsForThread_of_mem commitMember (by rfl)
    have localShape : ThreadChunks localEvents :=
      threadChunks entry.thread
    have localInvocationMember :
        MethodTrace.Event.invoke entry.invocation ∈ localEvents :=
      localShape.commit_invocation_mem localCommitMember
    have invocationMember :
        MethodTrace.Event.invoke entry.invocation ∈ events :=
      (eventsForThread_sublist entry.thread events).subset
        localInvocationMember
    have historyInvocationMember :
        HerlihyWing.HistoryEvent.invoke entry.invocation ∈
          MethodTrace.history events :=
      history_invoke_mem.mpr invocationMember
    refine ⟨historyInvocationMember, ?_⟩
    by_cases responseMember :
        MethodTrace.Event.respond entry.returned ∈ localEvents
    · obtain ⟨returnedEntry, returnedCommitMember,
          returnedShape, invocationBeforeResponse⟩ :=
        localShape.response_context responseMember
      have returnedCommitGlobal :
          MethodTrace.Event.commit returnedEntry ∈ events :=
        (eventsForThread_sublist entry.thread events).subset
          returnedCommitMember
      have returnedEntryMember :
          returnedEntry ∈ MethodTrace.completedOperations events :=
        completed_mem.mpr returnedCommitGlobal
      have returnedIdShape :
          returnedEntry.id = entry.id := by
        have ids :=
          congrArg HerlihyWing.Return.id returnedShape
        change returnedEntry.id = entry.id at ids
        exact ids
      have returnedEntryShape :
          returnedEntry = entry :=
        completed_eq_of_id_eq operationIdsNodup
          returnedEntryMember entryMember returnedIdShape
      subst returnedEntry
      have globalInvocationBeforeResponse :
          ListPrecedes
            (MethodTrace.Event.invoke entry.invocation)
            (MethodTrace.Event.respond entry.returned)
            events :=
        precedes_of_eventsForThread
          invocationBeforeResponse
      exact Or.inl
        ((precedes_history_of_trace
          globalInvocationBeforeResponse).toBefore)
    · refine Or.inr ⟨historyInvocationMember, ?_⟩
      intro returned matching returnedHistoryMember
      have responseGlobal :
          MethodTrace.Event.respond returned ∈ events :=
        history_respond_mem.mp returnedHistoryMember
      have responseLocal :
          MethodTrace.Event.respond returned ∈ localEvents :=
        mem_eventsForThread_of_mem responseGlobal (by
          change returned.thread = entry.thread
          exact matching.1.symm)
      obtain ⟨returnedEntry, returnedCommitMember,
          returnedShape, invocationBeforeResponse⟩ :=
        localShape.response_context responseLocal
      have returnedCommitGlobal :
          MethodTrace.Event.commit returnedEntry ∈ events :=
        (eventsForThread_sublist entry.thread events).subset
          returnedCommitMember
      have returnedEntryMember :
          returnedEntry ∈ MethodTrace.completedOperations events :=
        completed_mem.mpr returnedCommitGlobal
      have returnedIdShape :
          returnedEntry.id = entry.id := by
        have returnedId :=
          congrArg HerlihyWing.Return.id returnedShape
        change returnedEntry.id = returned.id at returnedId
        exact returnedId.trans matching.2.symm
      have returnedEntryShape :
          returnedEntry = entry :=
        completed_eq_of_id_eq operationIdsNodup
          returnedEntryMember entryMember returnedIdShape
      subst returnedEntry
      apply responseMember
      rw [returnedShape]
      exact responseLocal
  · intro returned returnedHistoryMember
    have responseGlobal :
        MethodTrace.Event.respond returned ∈ events :=
      history_respond_mem.mp returnedHistoryMember
    let localEvents :=
      MethodTrace.eventsForThread returned.thread events
    have responseLocal :
        MethodTrace.Event.respond returned ∈ localEvents :=
      mem_eventsForThread_of_mem responseGlobal (by rfl)
    have localShape : ThreadChunks localEvents :=
      threadChunks returned.thread
    obtain ⟨entry, commitLocal, returnedShape,
        invocationBeforeResponse⟩ :=
      localShape.response_context responseLocal
    have commitGlobal :
        MethodTrace.Event.commit entry ∈ events :=
      (eventsForThread_sublist returned.thread events).subset
        commitLocal
    have entryMember :
        entry ∈ MethodTrace.completedOperations events :=
      completed_mem.mpr commitGlobal
    have localPresentOrder :
        ListPrecedes
          (MethodTrace.Event.invoke entry.invocation)
          (MethodTrace.Event.respond entry.returned)
          localEvents := by
      simpa [returnedShape] using invocationBeforeResponse
    have globalPresentOrder :
        ListPrecedes
          (MethodTrace.Event.invoke entry.invocation)
          (MethodTrace.Event.respond entry.returned)
          events :=
      precedes_of_eventsForThread localPresentOrder
    exact ⟨entry, entryMember, returnedShape,
      (precedes_history_of_trace globalPresentOrder).toBefore⟩
  · intro first second firstMember secondMember sameThread
      invocationBeforeInvocation
    have firstCommitGlobal :
        MethodTrace.Event.commit first ∈ events :=
      completed_mem.mp firstMember
    have secondCommitGlobal :
        MethodTrace.Event.commit second ∈ events :=
      completed_mem.mp secondMember
    let localEvents :=
      MethodTrace.eventsForThread first.thread events
    have firstCommitLocal :
        MethodTrace.Event.commit first ∈ localEvents :=
      mem_eventsForThread_of_mem firstCommitGlobal (by rfl)
    have secondCommitLocal :
        MethodTrace.Event.commit second ∈ localEvents :=
      mem_eventsForThread_of_mem secondCommitGlobal (by
        simp [MethodTrace.Event.thread, sameThread])
    have firstLocalMember :
        first ∈ MethodTrace.completedOperations localEvents :=
      completed_mem.mpr firstCommitLocal
    have secondLocalMember :
        second ∈ MethodTrace.completedOperations localEvents :=
      completed_mem.mpr secondCommitLocal
    have traceInvocationOrder :
        ListPrecedes
          (MethodTrace.Event.invoke first.invocation)
          (MethodTrace.Event.invoke second.invocation)
          events :=
      precedes_history_invocations
        (ListPrecedes.ofBefore invocationBeforeInvocation)
    have localInvocationOrder :
        ListPrecedes
          (MethodTrace.Event.invoke first.invocation)
          (MethodTrace.Event.invoke second.invocation)
          localEvents :=
      precedes_eventsForThread traceInvocationOrder
        (by rfl)
        (by
          change second.thread = first.thread
          exact sameThread.symm)
    have localIdOrder :=
      (localInvocationOrder.filterMap
        (project := MethodTrace.Event.historyEvent?)
        rfl rfl).filterMap
          (project :=
            HerlihyWing.HistoryEvent.invocationId?)
          rfl rfl
    change
      ListPrecedes first.id second.id
        (HerlihyWing.invocationIds
          (MethodTrace.history localEvents))
      at localIdOrder
    have localHistorySublist :
        (MethodTrace.history localEvents).Sublist
          (MethodTrace.history events) :=
      (eventsForThread_sublist first.thread events).filterMap
        MethodTrace.Event.historyEvent?
    have localInvocationIdsNodup :
        (HerlihyWing.invocationIds
          (MethodTrace.history localEvents)).Nodup :=
      ((localHistorySublist.filterMap
        HerlihyWing.HistoryEvent.invocationId?).nodup
          invocationIdsNodup)
    have localOperationOrder :
        ListPrecedes first second
          (MethodTrace.completedOperations localEvents) :=
      (threadChunks first.thread).commit_order_of_id_order
        localInvocationIdsNodup
        firstLocalMember secondLocalMember localIdOrder
    have localCommitOrder :
        ListPrecedes
          (MethodTrace.Event.commit first)
          (MethodTrace.Event.commit second)
          localEvents :=
      precedes_trace_of_completed localOperationOrder
    have globalCommitOrder :
        ListPrecedes
          (MethodTrace.Event.commit first)
          (MethodTrace.Event.commit second)
          events :=
      precedes_of_eventsForThread localCommitOrder
    exact
      (precedes_completed_of_trace globalCommitOrder).toBefore

end SourceCompletion

namespace Interleaving.SourceSkeleton

/--
The commits already present in a certified finite source prefix form a
Herlihy--Wing completion of its client history.

Visible responses are all retained.  If the prefix stops after a commit and
before its response, that committed operation is selected as a pending
operation rather than discarded.
-/
theorem sourceCompletion
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate :
      Interleaving.SourceSkeleton initial skeleton) :
    HerlihyWing.Completion
      (sourceHistory skeleton)
      (sourceCommittedOperations skeleton) := by
  have invocationIdsNodup :
      (HerlihyWing.invocationIds
        (MethodTrace.history
          (MethodTrace.ofSkeleton skeleton))).Nodup := by
    rw [MethodTrace.history_ofSkeleton]
    have sourceIds :=
      SourceCompletion.invocationIds_sourceHistory
        skeleton.labels
    simpa using
      (sourceIds ▸ certificate.operationIdsNodup)
  have threadChunks :
      ∀ thread,
        SourceCompletion.ThreadChunks
          (MethodTrace.eventsForThread thread
            (MethodTrace.ofSkeleton skeleton)) := by
    intro thread
    obtain ⟨final, execution⟩ :=
      certificate.methodExecution thread
    exact
      SourceCompletion.ThreadChunks.ofThreadForm
        execution.toThreadForm
  have completion :=
    SourceCompletion.completion_of_threadChunks
      invocationIdsNodup threadChunks
  simpa only [MethodTrace.history_ofSkeleton,
    MethodTrace.completedOperations_ofSkeleton] using completion

end Interleaving.SourceSkeleton

end WeakMemory.TreiberRC11
