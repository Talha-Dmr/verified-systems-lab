import WeakMemory.TreiberOrderAcyclic

namespace WeakMemory.TreiberRC11

/-!
# Treiber-specific invariants for graph replay

The RC11 graph relations determine which head value each event observes. They
do not determine whether a node identifier is freshly allocated or whether a
pop's payload and next pointer agree with the immutable node that was
published earlier.

This module states those Treiber-specific obligations explicitly and uses them
to bridge a respecting finite graph schedule to executable replay.
`WeakMemory.TreiberTyping` derives the obligations from a functional allocator
table and local event-typing rules.
-/

namespace Event

/-- The immutable heap entry allocated by a successful push, if any. -/
def allocation? : Event α → Option (TreiberRA.NodeId × TreiberRA.Node α)
  | ⟨_, .algorithm (.pushSuccess _ nodeId value expected)⟩ =>
      some (nodeId, { value := value, next := expected })
  | _ => none

end Event

/--
Treiber-specific facts not supplied by the generic RC11 relations.

The publication field links every successful pop to the unique push that
allocated its immutable node. Requiring an extended-coherence edge makes that
publication precede the pop in every respecting schedule.
-/
structure ReplayInvariant
    (graph : Graph α)
    (initial : TreiberRA.State α) : Prop where
  initialHeadEmpty :
    initial.head = none
  allocationFresh :
    ∀ {event : Event α} {nodeId : TreiberRA.NodeId}
      {node : TreiberRA.Node α},
      event ∈ graph.events →
      event.allocation? = some (nodeId, node) →
      initial.heap nodeId = none
  allocationUnique :
    ∀ {first second : Event α} {nodeId : TreiberRA.NodeId}
      {firstNode secondNode : TreiberRA.Node α},
      first ∈ graph.events →
      second ∈ graph.events →
      first.allocation? = some (nodeId, firstNode) →
      second.allocation? = some (nodeId, secondNode) →
      first = second
  popPublished :
    ∀ {event : Event α} {thread nodeId : Nat}
      {value : α} {next : Option TreiberRA.NodeId},
      event ∈ graph.events →
      event.kind =
        .algorithm (.popSuccess thread nodeId value next) →
      ∃ publisher,
        publisher ∈ graph.events ∧
          publisher.allocation? =
            some (nodeId, { value := value, next := next }) ∧
          graph.ExtendedCoherence publisher event

/--
Apply the state update encoded by an event without checking whether its
observation is enabled. The later replay theorem proves that every such update
is accepted under `ReplayInvariant`.
-/
def advanceUnchecked
    (state : TreiberRA.State α)
    (event : Event α) : TreiberRA.State α :=
  match event.kind with
  | .initial => state
  | .algorithm action =>
      match action with
      | .pushSuccess _ nodeId value expected =>
          {
            heap := state.heap.insert nodeId
              { value := value, next := expected }
            head := some nodeId
          }
      | .pushFailure .. => state
      | .popSuccess _ _ _ next =>
          { heap := state.heap, head := next }
      | .popFailure .. => state
      | .popEmpty .. => state

/-- Execute a list of unchecked event updates from left to right. -/
def advanceUncheckedList :
    TreiberRA.State α →
    List (Event α) →
    TreiberRA.State α
  | state, [] => state
  | state, event :: rest =>
      advanceUncheckedList (advanceUnchecked state event) rest

@[simp] theorem advanceUncheckedList_nil
    (state : TreiberRA.State α) :
    advanceUncheckedList state [] = state :=
  rfl

@[simp] theorem advanceUncheckedList_cons
    (state : TreiberRA.State α)
    (event : Event α)
    (rest : List (Event α)) :
    advanceUncheckedList state (event :: rest) =
      advanceUncheckedList (advanceUnchecked state event) rest :=
  rfl

theorem advanceUncheckedList_append
    (state : TreiberRA.State α)
    (first second : List (Event α)) :
    advanceUncheckedList state (first ++ second) =
      advanceUncheckedList
        (advanceUncheckedList state first) second := by
  induction first generalizing state with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, advanceUncheckedList_cons]
      exact inductionHypothesis (advanceUnchecked state event)

/--
An inductive view of the existing decomposition-based `Before` predicate.
It is convenient for proofs about prefixes of a duplicate-free schedule.
-/
private inductive ListPrecedes
    (first second : Event α) : List (Event α) → Prop where
  | here {tail} :
      second ∈ tail →
      ListPrecedes first second (first :: tail)
  | there {head tail} :
      ListPrecedes first second tail →
      ListPrecedes first second (head :: tail)

private theorem ListPrecedes.second_mem
    {first second : Event α}
    {schedule : List (Event α)}
    (precedes : ListPrecedes first second schedule) :
    second ∈ schedule := by
  induction precedes with
  | here member =>
      simp [member]
  | there later inductionHypothesis =>
      simp [inductionHypothesis]

private theorem Before.toListPrecedes
    {first second : Event α}
    {schedule : List (Event α)}
    (before : Before first second schedule) :
    ListPrecedes first second schedule := by
  rcases before with ⟨earlier, between, later, scheduleShape⟩
  subst schedule
  induction earlier with
  | nil =>
      simp only [List.nil_append]
      apply ListPrecedes.here
      simp
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]
      exact ListPrecedes.there inductionHypothesis

private theorem ListPrecedes.toBefore
    {first second : Event α}
    {schedule : List (Event α)}
    (precedes : ListPrecedes first second schedule) :
    Before first second schedule := by
  induction precedes with
  | @here tail secondMember =>
      obtain ⟨between, later, tailShape⟩ :=
        List.append_of_mem secondMember
      subst tail
      exact ⟨[], between, later, rfl⟩
  | @there head tail later inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨earlier, between, trailing, tailShape⟩
      subst tail
      exact ⟨head :: earlier, between, trailing, rfl⟩

/-- Every member of a processed prefix precedes the next event. -/
private theorem ListPrecedes.of_mem_processed
    {first second : Event α}
    {processed suffix : List (Event α)}
    (member : first ∈ processed) :
    ListPrecedes first second (processed ++ second :: suffix) := by
  induction processed with
  | nil =>
      simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with firstIsHead | firstInTail
      · subst head
        apply ListPrecedes.here
        simp
      · exact ListPrecedes.there
          (inductionHypothesis firstInTail)

/--
An explicitly positioned event precedes every member of the following segment.
-/
private theorem ListPrecedes.of_mem_after
    {first second : Event α}
    {leading after trailing : List (Event α)}
    (member : second ∈ after) :
    ListPrecedes first second
      (leading ++ first :: after ++ trailing) := by
  induction leading with
  | nil =>
      simp only [List.nil_append]
      apply ListPrecedes.here
      simp [member]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]
      exact ListPrecedes.there inductionHypothesis

/--
If `second` is the next event after a prefix, every event that precedes it in a
duplicate-free schedule belongs to that prefix.
-/
private theorem ListPrecedes.first_mem_prefix
    {first second : Event α}
    {processed suffix : List (Event α)}
    (noDuplicates : (processed ++ second :: suffix).Nodup)
    (precedes :
      ListPrecedes first second (processed ++ second :: suffix)) :
    first ∈ processed := by
  induction processed with
  | nil =>
      simp only [List.nil_append] at noDuplicates precedes
      have secondNotInSuffix :=
        (List.nodup_cons.mp noDuplicates).1
      cases precedes with
      | here secondInSuffix =>
          exact (secondNotInSuffix secondInSuffix).elim
      | there later =>
          exact (secondNotInSuffix later.second_mem).elim
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append] at noDuplicates precedes ⊢
      cases precedes with
      | here secondInTail =>
          simp
      | there later =>
          simp only [List.mem_cons]
          exact Or.inr (inductionHypothesis
            (List.nodup_cons.mp noDuplicates).2 later)

private theorem ListPrecedes.asymm
    {first second : Event α}
    {schedule : List (Event α)}
    (noDuplicates : schedule.Nodup)
    (forward : ListPrecedes first second schedule) :
    ¬ ListPrecedes second first schedule := by
  induction forward with
  | @here tail secondInTail =>
      intro reverse
      have firstNotInTail := (List.nodup_cons.mp noDuplicates).1
      cases reverse with
      | here firstInTail =>
          exact firstNotInTail firstInTail
      | there reverseTail =>
          exact firstNotInTail reverseTail.second_mem
  | @there head tail forward inductionHypothesis =>
      intro reverse
      have headNotInTail := (List.nodup_cons.mp noDuplicates).1
      have tailNodup := (List.nodup_cons.mp noDuplicates).2
      cases reverse with
      | here firstInTail =>
          exact headNotInTail forward.second_mem
      | there reverseTail =>
          exact inductionHypothesis tailNodup reverseTail

private theorem Before.asymm
    {first second : Event α}
    {schedule : List (Event α)}
    (noDuplicates : schedule.Nodup)
    (forward : Before first second schedule) :
    ¬ Before second first schedule := by
  intro reverse
  exact forward.toListPrecedes.asymm noDuplicates
    reverse.toListPrecedes

/--
Between a reads-from source and its read there can be no scheduled write.

Modification-order totality places any candidate write on one side of the
source. One side contradicts modification-order scheduling; the other creates
a reads-before edge that must occur after the read.
-/
private theorem no_writes_after_readsFrom_source
    {graph : Graph α}
    {schedule processed remaining : List (Event α)}
    {source target : Event α}
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule)
    (scheduleShape :
      schedule = processed ++ target :: remaining)
    (readsFrom : graph.readsFrom source target) :
    ∃ leading after,
      processed = leading ++ source :: after ∧
        ∀ middle,
          middle ∈ after →
          ¬ middle.IsWrite := by
  have sourceBeforeTarget :
      Before source target schedule :=
    respects.extendedCoherence
      (Graph.ExtendedCoherence.readsFrom readsFrom)
  have scheduleNodup : (processed ++ target :: remaining).Nodup := by
    rw [← scheduleShape]
    exact respects.noDuplicates
  have sourceInProcessed : source ∈ processed := by
    rw [scheduleShape] at sourceBeforeTarget
    exact sourceBeforeTarget.toListPrecedes.first_mem_prefix
      scheduleNodup
  obtain ⟨leading, after, processedShape⟩ :=
    List.append_of_mem sourceInProcessed
  refine ⟨leading, after, processedShape, ?_⟩
  intro middle middleInAfter middleWrites
  have fullShape :
      schedule =
        leading ++ source :: after ++ target :: remaining := by
    simpa [processedShape, List.append_assoc] using scheduleShape
  have sourceBeforeMiddle :
      Before source middle schedule := by
    rw [fullShape]
    exact (ListPrecedes.of_mem_after
      (trailing := target :: remaining) middleInAfter).toBefore
  have middleInProcessed : middle ∈ processed := by
    rw [processedShape]
    simp [middleInAfter]
  have middleBeforeTarget :
      Before middle target schedule := by
    rw [scheduleShape]
    exact (ListPrecedes.of_mem_processed
      (suffix := remaining) middleInProcessed).toBefore
  have middleMember : middle ∈ graph.events := by
    apply (respects.covers middle).2
    rw [scheduleShape]
    simp [middleInProcessed]
  have sourceMember : source ∈ graph.events :=
    (wellFormed.readsFromClosed readsFrom).1
  obtain ⟨value, sourceWritesValue, _⟩ :=
    wellFormed.readsFromValues readsFrom
  have sourceWrites : source.IsWrite :=
    ⟨value, sourceWritesValue⟩
  have sourceNeMiddle : source ≠ middle := by
    intro equal
    subst middle
    exact (sourceBeforeMiddle.asymm respects.noDuplicates)
      sourceBeforeMiddle
  have targetNeMiddle : target ≠ middle := by
    intro equal
    subst middle
    exact (middleBeforeTarget.asymm respects.noDuplicates)
      middleBeforeTarget
  rcases wellFormed.modificationOrderTotal
      sourceMember middleMember sourceWrites middleWrites
      sourceNeMiddle with sourceBefore | middleBefore
  · have targetBeforeMiddle :
        Before target middle schedule := by
      apply respects.extendedCoherence
      apply Graph.ExtendedCoherence.readsBefore
      exact ⟨source, readsFrom, sourceBefore, targetNeMiddle⟩
    exact (middleBeforeTarget.asymm respects.noDuplicates)
      targetBeforeMiddle
  · have middleBeforeSource :
        Before middle source schedule :=
      respects.extendedCoherence
        (Graph.ExtendedCoherence.modificationOrder middleBefore)
    exact (sourceBeforeMiddle.asymm respects.noDuplicates)
      middleBeforeSource

/-- No write can be scheduled before the unique initial head event. -/
private theorem no_writes_before_initial
    {graph : Graph α}
    {schedule leading trailing : List (Event α)}
    {initial : Event α}
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule)
    (scheduleShape :
      schedule = leading ++ initial :: trailing)
    (isInitial : initial.IsInitial) :
    ∀ middle,
      middle ∈ leading →
      ¬ middle.IsWrite := by
  intro middle middleInLeading middleWrites
  have middleBeforeInitial :
      Before middle initial schedule := by
    rw [scheduleShape]
    exact (ListPrecedes.of_mem_processed
      (suffix := trailing) middleInLeading).toBefore
  have middleMember : middle ∈ graph.events := by
    apply (respects.covers middle).2
    rw [scheduleShape]
    simp [middleInLeading]
  have initialMember : initial ∈ graph.events := by
    apply (respects.covers initial).2
    rw [scheduleShape]
    simp
  have middleNeInitial : middle ≠ initial := by
    intro equal
    subst middle
    exact (middleBeforeInitial.asymm respects.noDuplicates)
      middleBeforeInitial
  have middleNotInitial : ¬ middle.IsInitial := by
    intro middleInitial
    obtain ⟨chosen, chosenMember, chosenInitial, unique⟩ :=
      wellFormed.initialExistsUnique
    have middleIsChosen :=
      unique middle middleMember middleInitial
    have initialIsChosen :=
      unique initial initialMember isInitial
    exact middleNeInitial
      (middleIsChosen.trans initialIsChosen.symm)
  have initialBeforeMiddle :
      graph.modificationOrder initial middle :=
    wellFormed.initialPrecedesWrites
      initialMember isInitial middleMember middleWrites
      middleNotInitial
  have scheduledInitialBeforeMiddle :
      Before initial middle schedule :=
    respects.extendedCoherence
      (Graph.ExtendedCoherence.modificationOrder
        initialBeforeMiddle)
  exact (middleBeforeInitial.asymm respects.noDuplicates)
    scheduledInitialBeforeMiddle

/-- An unchecked non-write event leaves the concrete head unchanged. -/
private theorem advanceUnchecked_head_of_not_write
    (state : TreiberRA.State α)
    {event : Event α}
    (doesNotWrite : ¬ event.IsWrite) :
    (advanceUnchecked state event).head = state.head := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          exact (doesNotWrite ⟨none, rfl⟩).elim
      | algorithm action =>
          cases action with
          | pushSuccess thread nodeId value expected =>
              exact (doesNotWrite ⟨some nodeId, rfl⟩).elim
          | pushFailure =>
              rfl
          | popSuccess thread nodeId value next =>
              exact (doesNotWrite ⟨next, rfl⟩).elim
          | popFailure =>
              rfl
          | popEmpty =>
              rfl

/-- A list containing no writes leaves the concrete head unchanged. -/
private theorem advanceUncheckedList_head_of_no_writes
    (state : TreiberRA.State α)
    (events : List (Event α))
    (noWrites :
      ∀ event,
        event ∈ events →
        ¬ event.IsWrite) :
    (advanceUncheckedList state events).head = state.head := by
  induction events generalizing state with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      have eventDoesNotWrite : ¬ event.IsWrite :=
        noWrites event (by simp)
      have restHasNoWrites :
          ∀ later,
            later ∈ rest →
            ¬ later.IsWrite := by
        intro later laterMember
        exact noWrites later (by simp [laterMember])
      calc
        (advanceUncheckedList state (event :: rest)).head =
            (advanceUnchecked state event).head :=
          inductionHypothesis
            (advanceUnchecked state event) restHasNoWrites
        _ = state.head :=
          advanceUnchecked_head_of_not_write
            state eventDoesNotWrite

/--
An unchecked write installs its declared value. The only special case is the
logical initial write, which is a replay no-op and therefore requires an empty
incoming head.
-/
private theorem advanceUnchecked_head_of_writtenValue
    (state : TreiberRA.State α)
    {event : Event α}
    {value : Option TreiberRA.NodeId}
    (writesValue : event.writtenValue = some value)
    (initialHead :
      event.IsInitial →
      state.head = none) :
    (advanceUnchecked state event).head = value := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp only [Event.writtenValue] at writesValue
          cases writesValue
          exact initialHead trivial
      | algorithm action =>
          cases action <;>
            simp [Event.writtenValue, advanceUnchecked] at writesValue ⊢ <;>
            assumption

/--
For a respecting schedule, the unchecked state immediately before a read has
the value supplied by its reads-from source.
-/
private theorem readsFrom_matches_unchecked_head
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule processed remaining : List (Event α)}
    {source target : Event α}
    {value : Option TreiberRA.NodeId}
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule)
    (invariant : ReplayInvariant graph initial)
    (scheduleShape :
      schedule = processed ++ target :: remaining)
    (readsFrom : graph.readsFrom source target)
    (sourceWritesValue :
      source.writtenValue = some value) :
    (advanceUncheckedList initial processed).head = value := by
  obtain ⟨leading, after, processedShape, noWritesAfter⟩ :=
    no_writes_after_readsFrom_source
      wellFormed respects scheduleShape readsFrom
  have fullShape :
      schedule =
        leading ++ source :: (after ++ target :: remaining) := by
    simpa [processedShape, List.append_assoc] using scheduleShape
  let beforeSource := advanceUncheckedList initial leading
  have beforeSourceHead :
      source.IsInitial →
      beforeSource.head = none := by
    intro sourceInitial
    calc
      beforeSource.head = initial.head := by
        apply advanceUncheckedList_head_of_no_writes
        exact no_writes_before_initial
          wellFormed respects fullShape sourceInitial
      _ = none := invariant.initialHeadEmpty
  have sourceInstallsValue :
      (advanceUnchecked beforeSource source).head = value :=
    advanceUnchecked_head_of_writtenValue
      beforeSource sourceWritesValue beforeSourceHead
  have afterPreservesHead :
      (advanceUncheckedList
        (advanceUnchecked beforeSource source) after).head =
        (advanceUnchecked beforeSource source).head :=
    advanceUncheckedList_head_of_no_writes
      (advanceUnchecked beforeSource source)
      after
      noWritesAfter
  calc
    (advanceUncheckedList initial processed).head =
        (advanceUncheckedList
          (advanceUnchecked beforeSource source) after).head := by
      rw [processedShape, advanceUncheckedList_append]
      rfl
    _ = (advanceUnchecked beforeSource source).head :=
      afterPreservesHead
    _ = value := sourceInstallsValue

/--
If an event does not allocate a given node identifier, its unchecked update
preserves that heap lookup.
-/
private theorem advanceUnchecked_heap_lookup_of_no_allocation
    (state : TreiberRA.State α)
    (event : Event α)
    (nodeId : TreiberRA.NodeId)
    (doesNotAllocate :
      ∀ node,
        event.allocation? ≠ some (nodeId, node)) :
    (advanceUnchecked state event).heap nodeId =
      state.heap nodeId := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          rfl
      | algorithm action =>
          cases action with
          | pushSuccess thread allocated value expected =>
              by_cases same : nodeId = allocated
              · subst allocated
                exact (doesNotAllocate
                  { value := value, next := expected } rfl).elim
              · exact TreiberRA.Heap.insert_other
                  state.heap allocated nodeId
                  { value := value, next := expected }
                  same
          | pushFailure =>
              rfl
          | popSuccess =>
              rfl
          | popFailure =>
              rfl
          | popEmpty =>
              rfl

/-- A list with no allocation of `nodeId` preserves its heap lookup. -/
private theorem advanceUncheckedList_heap_lookup_of_no_allocation
    (state : TreiberRA.State α)
    (events : List (Event α))
    (nodeId : TreiberRA.NodeId)
    (doesNotAllocate :
      ∀ event,
        event ∈ events →
        ∀ node,
          event.allocation? ≠ some (nodeId, node)) :
    (advanceUncheckedList state events).heap nodeId =
      state.heap nodeId := by
  induction events generalizing state with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      have firstDoesNotAllocate :
          ∀ node,
            event.allocation? ≠ some (nodeId, node) :=
        doesNotAllocate event (by simp)
      have restDoesNotAllocate :
          ∀ later,
            later ∈ rest →
            ∀ node,
              later.allocation? ≠ some (nodeId, node) := by
        intro later laterMember node
        exact doesNotAllocate later (by simp [laterMember]) node
      calc
        (advanceUncheckedList state (event :: rest)).heap nodeId =
            (advanceUnchecked state event).heap nodeId :=
          inductionHypothesis
            (advanceUnchecked state event)
            restDoesNotAllocate
        _ = state.heap nodeId :=
          advanceUnchecked_heap_lookup_of_no_allocation
            state event nodeId firstDoesNotAllocate

/-- An unchecked allocation installs its immutable node in the heap. -/
private theorem advanceUnchecked_heap_of_allocation
    (state : TreiberRA.State α)
    {event : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (allocation :
      event.allocation? = some (nodeId, node)) :
    (advanceUnchecked state event).heap nodeId = some node := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp [Event.allocation?] at allocation
      | algorithm action =>
          cases action with
          | pushSuccess thread allocated value expected =>
              simp only [Event.allocation?, Option.some.injEq,
                Prod.mk.injEq] at allocation
              rcases allocation with ⟨allocatedIsNodeId, nodeShape⟩
              subst allocated
              subst node
              exact TreiberRA.Heap.insert_same
                state.heap nodeId
                { value := value, next := expected }
          | pushFailure =>
              simp [Event.allocation?] at allocation
          | popSuccess =>
              simp [Event.allocation?] at allocation
          | popFailure =>
              simp [Event.allocation?] at allocation
          | popEmpty =>
              simp [Event.allocation?] at allocation

/-- Every allocation is fresh when its event is reached in the schedule. -/
private theorem allocation_is_fresh_in_unchecked_state
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule processed remaining : List (Event α)}
    {event : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (respects : RespectsGraph graph schedule)
    (invariant : ReplayInvariant graph initial)
    (scheduleShape :
      schedule = processed ++ event :: remaining)
    (allocation :
      event.allocation? = some (nodeId, node)) :
    (advanceUncheckedList initial processed).heap nodeId = none := by
  have eventMember : event ∈ graph.events := by
    apply (respects.covers event).2
    rw [scheduleShape]
    simp
  have noPriorAllocation :
      ∀ earlier,
        earlier ∈ processed →
        ∀ earlierNode,
          earlier.allocation? ≠ some (nodeId, earlierNode) := by
    intro earlier earlierInProcessed earlierNode earlierAllocation
    have earlierMember : earlier ∈ graph.events := by
      apply (respects.covers earlier).2
      rw [scheduleShape]
      simp [earlierInProcessed]
    have earlierIsEvent :=
      invariant.allocationUnique
        earlierMember eventMember earlierAllocation allocation
    have earlierBeforeEvent :
        Before earlier event schedule := by
      rw [scheduleShape]
      exact (ListPrecedes.of_mem_processed
        (suffix := remaining) earlierInProcessed).toBefore
    subst earlier
    exact (earlierBeforeEvent.asymm respects.noDuplicates)
      earlierBeforeEvent
  calc
    (advanceUncheckedList initial processed).heap nodeId =
        initial.heap nodeId :=
      advanceUncheckedList_heap_lookup_of_no_allocation
        initial processed nodeId noPriorAllocation
    _ = none :=
      invariant.allocationFresh eventMember allocation

/--
Once an allocation has occurred, uniqueness prevents later events in the
processed prefix from overwriting the same immutable node.
-/
private theorem published_allocation_in_unchecked_heap
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule processed remaining : List (Event α)}
    {publisher target : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (respects : RespectsGraph graph schedule)
    (invariant : ReplayInvariant graph initial)
    (scheduleShape :
      schedule = processed ++ target :: remaining)
    (publisherMember : publisher ∈ graph.events)
    (allocation :
      publisher.allocation? = some (nodeId, node))
    (publisherBefore :
      Before publisher target schedule) :
    (advanceUncheckedList initial processed).heap nodeId =
      some node := by
  have scheduleNodup : (processed ++ target :: remaining).Nodup := by
    rw [← scheduleShape]
    exact respects.noDuplicates
  have publisherInProcessed : publisher ∈ processed := by
    rw [scheduleShape] at publisherBefore
    exact publisherBefore.toListPrecedes.first_mem_prefix
      scheduleNodup
  obtain ⟨leading, after, processedShape⟩ :=
    List.append_of_mem publisherInProcessed
  have fullShape :
      schedule =
        leading ++ publisher :: after ++ target :: remaining := by
    simpa [processedShape, List.append_assoc] using scheduleShape
  have noLaterAllocation :
      ∀ later,
        later ∈ after →
        ∀ laterNode,
          later.allocation? ≠ some (nodeId, laterNode) := by
    intro later laterInAfter laterNode laterAllocation
    have laterMember : later ∈ graph.events := by
      apply (respects.covers later).2
      rw [fullShape]
      simp [laterInAfter]
    have publisherIsLater :=
      invariant.allocationUnique
        publisherMember laterMember allocation laterAllocation
    have publisherBeforeLater :
        Before publisher later schedule := by
      rw [fullShape]
      exact (ListPrecedes.of_mem_after
        (trailing := target :: remaining) laterInAfter).toBefore
    subst later
    exact (publisherBeforeLater.asymm respects.noDuplicates)
      publisherBeforeLater
  let beforePublisher :=
    advanceUncheckedList initial leading
  have publisherInstalled :
      (advanceUnchecked beforePublisher publisher).heap nodeId =
        some node :=
    advanceUnchecked_heap_of_allocation
      beforePublisher allocation
  have laterPreserves :
      (advanceUncheckedList
        (advanceUnchecked beforePublisher publisher) after).heap nodeId =
        (advanceUnchecked beforePublisher publisher).heap nodeId :=
    advanceUncheckedList_heap_lookup_of_no_allocation
      (advanceUnchecked beforePublisher publisher)
      after nodeId noLaterAllocation
  calc
    (advanceUncheckedList initial processed).heap nodeId =
        (advanceUncheckedList
          (advanceUnchecked beforePublisher publisher) after).heap nodeId := by
      rw [processedShape, advanceUncheckedList_append]
      rfl
    _ = (advanceUnchecked beforePublisher publisher).heap nodeId :=
      laterPreserves
    _ = some node := publisherInstalled

/-- Every algorithm event reads the atomic head. -/
private theorem algorithm_event_isRead
    (id : EventId)
    (action : TreiberRA.Action α) :
    (Event.mk id (.algorithm action)).IsRead := by
  cases action <;>
    simp [Event.IsRead, Event.readValue]

/--
Every algorithm event is enabled when it is reached in a respecting schedule.
-/
private theorem scheduled_algorithm_enabled
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule processed remaining : List (Event α)}
    (id : EventId)
    (action : TreiberRA.Action α)
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule)
    (invariant : ReplayInvariant graph initial)
    (scheduleShape :
      schedule =
        processed ++ Event.mk id (.algorithm action) :: remaining) :
    applyAction?
        (advanceUncheckedList initial processed) action =
      some (advanceUnchecked
        (advanceUncheckedList initial processed)
        (Event.mk id (.algorithm action))) := by
  let target : Event α := Event.mk id (.algorithm action)
  have targetMember : target ∈ graph.events := by
    apply (respects.covers target).2
    rw [scheduleShape]
    simp [target]
  obtain ⟨source, readsFrom⟩ :=
    wellFormed.everyReadHasSource
      targetMember
      (algorithm_event_isRead id action)
  obtain ⟨observed, sourceWritesValue, targetReadsValue⟩ :=
    wellFormed.readsFromValues readsFrom
  have headMatches :
      (advanceUncheckedList initial processed).head = observed :=
    readsFrom_matches_unchecked_head
      wellFormed respects invariant scheduleShape
      readsFrom sourceWritesValue
  cases action with
  | pushSuccess thread nodeId value expected =>
      simp only [target, Event.readValue, Option.some.injEq] at targetReadsValue
      have headEquals :
          (advanceUncheckedList initial processed).head = expected :=
        headMatches.trans targetReadsValue.symm
      have fresh :
          (advanceUncheckedList initial processed).heap nodeId = none :=
        allocation_is_fresh_in_unchecked_state
          respects invariant scheduleShape rfl
      simp [applyAction?, advanceUnchecked, headEquals, fresh]
  | pushFailure thread nodeId value expected actual =>
      simp only [target, Event.readValue, Option.some.injEq] at targetReadsValue
      have headEquals :
          (advanceUncheckedList initial processed).head = actual :=
        headMatches.trans targetReadsValue.symm
      simp [applyAction?, advanceUnchecked, headEquals]
  | popSuccess thread nodeId value next =>
      simp only [target, Event.readValue, Option.some.injEq] at targetReadsValue
      have headEquals :
          (advanceUncheckedList initial processed).head = some nodeId :=
        headMatches.trans targetReadsValue.symm
      obtain ⟨publisher, publisherMember, allocation, publication⟩ :=
        invariant.popPublished targetMember rfl
      have lookup :
          (advanceUncheckedList initial processed).heap nodeId =
            some { value := value, next := next } :=
        published_allocation_in_unchecked_heap
          respects invariant scheduleShape
          publisherMember allocation
          (respects.extendedCoherence publication)
      simp [applyAction?, advanceUnchecked, headEquals, lookup]
  | popFailure thread expected actual =>
      simp only [target, Event.readValue, Option.some.injEq] at targetReadsValue
      have headEquals :
          (advanceUncheckedList initial processed).head = actual :=
        headMatches.trans targetReadsValue.symm
      simp [applyAction?, advanceUnchecked, headEquals]
  | popEmpty thread =>
      simp only [target, Event.readValue, Option.some.injEq] at targetReadsValue
      have headEquals :
          (advanceUncheckedList initial processed).head = none :=
        headMatches.trans targetReadsValue.symm
      simp [applyAction?, advanceUnchecked, headEquals]

/--
Every respecting schedule satisfying the explicit Treiber invariants is
accepted by executable replay.
-/
theorem replay?_eq_some_advanceUncheckedList
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule : List (Event α)}
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule)
    (invariant : ReplayInvariant graph initial) :
    replay? initial schedule =
      some (advanceUncheckedList initial schedule) := by
  have replayRemaining :
      ∀ (remaining processed : List (Event α)),
        schedule = processed ++ remaining →
        replay?
            (advanceUncheckedList initial processed)
            remaining =
          some (advanceUncheckedList initial schedule) := by
    intro remaining
    induction remaining with
    | nil =>
        intro processed scheduleShape
        simp only [List.append_nil] at scheduleShape
        subst schedule
        rfl
    | cons event rest inductionHypothesis =>
        intro processed scheduleShape
        have extendedShape :
            schedule = (processed ++ [event]) ++ rest := by
          simpa [List.append_assoc] using scheduleShape
        have tailReplay :=
          inductionHypothesis (processed ++ [event]) extendedShape
        have extendedState :
            advanceUncheckedList initial (processed ++ [event]) =
              advanceUnchecked
                (advanceUncheckedList initial processed) event := by
          rw [advanceUncheckedList_append]
          rfl
        rw [extendedState] at tailReplay
        cases event with
        | mk id kind =>
            cases kind with
            | initial =>
                simpa [replay?, advanceUnchecked] using tailReplay
            | algorithm action =>
                have enabled :=
                  scheduled_algorithm_enabled
                    id action wellFormed respects invariant
                    scheduleShape
                simp only [replay?, enabled]
                exact tailReplay
  simpa using replayRemaining schedule [] (by simp)

namespace CoreConsistent

/--
Topological scheduling and Treiber replay invariants construct a complete
certificate for the existing graph-to-operational bridge.
-/
theorem existsCertifiedSchedule_of_replayInvariant
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (consistent : CoreConsistent graph)
    (invariant : ReplayInvariant graph initial) :
    ∃ schedule final,
      RespectsGraph graph schedule ∧
        replay? initial schedule = some final ∧
        CertifiedSchedule graph initial schedule final := by
  obtain ⟨schedule, respects⟩ :=
    consistent.existsRespectsGraph consistent.orderAcyclic
  let final := advanceUncheckedList initial schedule
  have replayAccepted :
      replay? initial schedule = some final :=
    replay?_eq_some_advanceUncheckedList
      consistent.toWellFormed respects invariant
  have contained :
      ∀ event,
        event ∈ schedule →
        event ∈ graph.events := by
    intro event member
    exact (respects.covers event).2 member
  have certificate :
      CertifiedSchedule graph initial schedule final := {
    consistent := consistent
    respectsGraph := respects
    executes :=
      replay?_sound graph contained replayAccepted
  }
  exact ⟨schedule, final, respects, replayAccepted, certificate⟩

end CoreConsistent

/--
End-to-end graph theorem under core consistency and Treiber invariants.

It constructs the schedule and final operational state, proves executable
replay succeeds, and yields a legal sequential stack history.
-/
theorem linearizable_of_replayInvariant
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (consistent : CoreConsistent graph)
    (invariant : ReplayInvariant graph initial)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    ∃ schedule final finalValues,
      RespectsGraph graph schedule ∧
        replay? initial schedule = some final ∧
        TreiberRA.Represents
          final.heap final.head finalValues ∧
        StackSpec.Legal initialValues
          (Treiber.completedHistory
            (TreiberRA.commits
              (projectedActions schedule)))
          finalValues := by
  obtain ⟨schedule, final, respects, replayAccepted, certificate⟩ :=
    consistent.existsCertifiedSchedule_of_replayInvariant
      invariant
  obtain ⟨finalValues, finalRepresentation, legalHistory⟩ :=
    certifiedSchedule_linearizable
      certificate initialRepresentation
  exact ⟨schedule, final, finalValues,
    respects, replayAccepted,
    finalRepresentation, legalHistory⟩

end WeakMemory.TreiberRC11
