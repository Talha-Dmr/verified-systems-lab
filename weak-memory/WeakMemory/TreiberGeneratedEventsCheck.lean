import WeakMemory.TreiberExtendedCoherenceCheck

namespace WeakMemory.TreiberRC11

/-!
# Executable generation checking

The chronological fold below constructs the allocator table while consuming
exactly one raw publication path for every successful pop.  Publication paths
are keyed by pop event identifier.  Missing or duplicate entries fail at the
pop; entries for non-pop or nonexistent events remain unconsumed and fail at
the end.
-/

namespace GeneratedEventsCheck

/-- One externally supplied publication path keyed by successful-pop ID. -/
structure RawPublication where
  popEventId : EventId
  path : ExtendedCoherenceCheck.RawPath
  deriving Repr, DecidableEq

/-- Select the identifier of a successful-pop event and ignore every other event. -/
def successfulPopEventId? :
    Event α → Option EventId
  | ⟨id, .algorithm (.popSuccess ..)⟩ =>
      some id
  | _ =>
      none

/-- Successful-pop identifiers, in event chronology and with multiplicity. -/
def successfulPopEventIds
    (events : List (Event α)) :
    List EventId :=
  events.filterMap successfulPopEventId?

/--
Consume exactly one publication entry with the requested pop identifier.

Zero or multiple matches are rejected.  All nonmatching entries are retained.
-/
def takePublication?
    (popEventId : EventId)
    (publications : List RawPublication) :
    Option
      (ExtendedCoherenceCheck.RawPath ×
        List RawPublication) :=
  match
      publications.filter fun publication =>
        decide (publication.popEventId = popEventId)
    with
  | [publication] =>
      some (
        publication.path,
        publications.filter fun candidate =>
          decide (candidate.popEventId ≠ popEventId))
  | _ =>
      none

/-- Successful consumption identifies the unique keyed input entry. -/
theorem takePublication?_sound
    {popEventId : EventId}
    {publications remaining : List RawPublication}
    {path : ExtendedCoherenceCheck.RawPath}
    (taken :
      takePublication? popEventId publications =
        some (path, remaining)) :
    (∃ publication,
      publication ∈ publications ∧
        publication.popEventId = popEventId ∧
        publication.path = path) ∧
      (∀ publication,
        publication ∈ remaining ↔
          publication ∈ publications ∧
            publication.popEventId ≠ popEventId) := by
  unfold takePublication? at taken
  cases filteredShape :
      publications.filter fun publication =>
        decide (publication.popEventId = popEventId) with
  | nil =>
      simp [filteredShape] at taken
  | cons selected filteredTail =>
      cases filteredTail with
      | nil =>
          have pairShape :
              (selected.path,
                  publications.filter fun candidate =>
                    decide
                      (candidate.popEventId ≠ popEventId)) =
                (path, remaining) :=
            Option.some.inj
              (by simpa [filteredShape] using taken)
          have pathShape :
              selected.path = path :=
            congrArg Prod.fst pairShape
          have remainingShape :
              (publications.filter fun candidate =>
                  decide
                    (candidate.popEventId ≠ popEventId)) =
                remaining :=
            congrArg Prod.snd pairShape
          have selectedFiltered :
              selected ∈
                publications.filter fun publication =>
                  decide
                    (publication.popEventId = popEventId) := by
            rw [filteredShape]
            simp
          have selectedDescription :=
            List.mem_filter.mp selectedFiltered
          refine ⟨⟨selected, selectedDescription.1, ?_, pathShape⟩,
            ?_⟩
          · simpa using selectedDescription.2
          · intro publication
            rw [← remainingShape]
            simp
      | cons duplicate trailing =>
          simp [filteredShape] at taken

/--
Publication lookup fails exactly when the requested key does not occur once.
This covers both a missing path and every duplicate-key case, including
identical duplicate records.
-/
theorem takePublication?_eq_none_iff_count_ne_one
    (popEventId : EventId)
    (publications : List RawPublication) :
    takePublication? popEventId publications = none ↔
      (publications.filter fun publication =>
        decide (publication.popEventId = popEventId)).length ≠ 1 := by
  unfold takePublication?
  cases filteredShape :
      publications.filter fun publication =>
        decide (publication.popEventId = popEventId) with
  | nil =>
      simp
  | cons selected filteredTail =>
      cases filteredTail with
      | nil =>
          simp
      | cons duplicate trailing =>
          simp

/--
A leading publication is selected exactly when all remaining keys differ.
-/
theorem takePublication?_cons_of_fresh
    (popEventId : EventId)
    (path : ExtendedCoherenceCheck.RawPath)
    (remaining : List RawPublication)
    (fresh :
      ∀ publication,
        publication ∈ remaining →
        publication.popEventId ≠ popEventId) :
    takePublication? popEventId
        ({ popEventId := popEventId, path := path } :: remaining) =
      some (path, remaining) := by
  have matchingTail :
      remaining.filter (fun publication =>
        decide (publication.popEventId = popEventId)) = [] := by
    induction remaining with
    | nil =>
        rfl
    | cons publication rest inductionHypothesis =>
        have headFresh :
            publication.popEventId ≠ popEventId :=
          fresh publication (by simp)
        have restFresh :
            ∀ candidate,
              candidate ∈ rest →
                candidate.popEventId ≠ popEventId := by
          intro candidate member
          exact fresh candidate (by simp [member])
        simp [headFresh, inductionHypothesis restFresh]
  have retainedTail :
      remaining.filter (fun publication =>
        decide (publication.popEventId ≠ popEventId)) =
          remaining := by
    apply List.filter_eq_self.mpr
    intro publication member
    simp [fresh publication member]
  have selectedShape :
      ({ popEventId := popEventId, path := path } :: remaining).filter
          (fun publication =>
            decide (publication.popEventId = popEventId)) =
        [{ popEventId := popEventId, path := path }] := by
    simp only [List.filter_cons, matchingTail]
    simp
  have remainingShape :
      ({ popEventId := popEventId, path := path } :: remaining).filter
          (fun publication =>
            decide (publication.popEventId ≠ popEventId)) =
        remaining := by
    simp only [List.filter_cons, retainedTail]
    simp
  unfold takePublication?
  rw [selectedShape, remainingShape]

/-- Fold state: constructed allocator plus unconsumed publication inputs. -/
structure State (α : Type) where
  allocator : AllocatorTable α
  publications : List RawPublication

/-- Initial fold state. -/
def initialState
    (publications : List RawPublication) :
    State α where
  allocator :=
    AllocatorTable.empty
  publications :=
    publications

/--
Validate and append one chronological canonical event.
-/
def advance?
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (state : State α)
    (event : Event α) :
    Option (State α) :=
  match event.kind with
  | .initial =>
      some state
  | .algorithm action =>
      match action with
      | .pushLoad .. =>
          some state
      | .popLoad .. =>
          some state
      | .isEmptyLoad .. =>
          some state
      | .pushSuccess _ nodeId value expected =>
          if _ :
              initial.heap nodeId = none ∧
                state.allocator nodeId = none
          then
            some {
              allocator :=
                AllocatorTable.insert state.allocator nodeId
                  event { value := value, next := expected }
              publications :=
                state.publications
            }
          else
            none
      | .pushFailure .. =>
          some state
      | .popSuccess _ nodeId value next =>
          match state.allocator nodeId,
              takePublication? event.id state.publications with
          | some (publisher, node),
              some (path, remaining) =>
              if _ :
                  node = { value := value, next := next } ∧
                    path.source = publisher.id ∧
                    ExtendedCoherenceCheck.finalTargetId
                        path.first path.rest =
                      event.id ∧
                    ExtendedCoherenceCheck.check data path = true
              then
                some {
                  allocator :=
                    state.allocator
                  publications :=
                    remaining
                }
              else
                none
          | _, _ =>
              none
      | .popFailure .. =>
          some state
      | .popEmpty .. =>
          some state

/--
Process an event prefix without imposing the terminal “all publications were
consumed” condition.  This runner makes the completeness induction composable
across the append-at-the-end constructors of `GeneratedEvents`.
-/
def runPrefix?
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α) :
    State α → List (Event α) → Option (State α)
  | state, [] =>
      some state
  | state, event :: rest =>
      match advance? data initial state event with
      | none =>
          none
      | some next =>
          runPrefix? data initial next rest

/-- Prefix execution commutes with appending one final event. -/
theorem runPrefix?_append_singleton
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (state : State α)
    (events : List (Event α))
    (event : Event α) :
    runPrefix? data initial state (events ++ [event]) =
      match runPrefix? data initial state events with
      | none =>
          none
      | some beforeFinal =>
          advance? data initial beforeFinal event := by
  induction events generalizing state with
  | nil =>
      cases advanced :
          advance? data initial state event <;>
        simp [runPrefix?, advanced]
  | cons head rest inductionHypothesis =>
      simp only [List.cons_append, runPrefix?]
      cases advanced :
          advance? data initial state head with
      | none =>
          rfl
      | some next =>
          exact inductionHypothesis next

/--
Chronologically process a finite event suffix.  Success additionally requires
that every raw publication entry was consumed.
-/
def fold?
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α) :
    State α → List (Event α) → Option (AllocatorTable α)
  | state, [] =>
      match state.publications with
      | [] =>
          some state.allocator
      | _ :: _ =>
          none
  | state, event :: rest =>
      match advance? data initial state event with
      | none =>
          none
      | some next =>
          fold? data initial next rest

/-- A prefix run ending with no publications is accepted by the terminal fold. -/
theorem fold?_of_runPrefix?_empty
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    {state : State α}
    {events : List (Event α)}
    {allocator : AllocatorTable α}
    (ran :
      runPrefix? data initial state events =
        some {
          allocator := allocator
          publications := []
        }) :
    fold? data initial state events = some allocator := by
  induction events generalizing state with
  | nil =>
      simp only [runPrefix?] at ran
      cases ran
      rfl
  | cons event rest inductionHypothesis =>
      simp only [runPrefix?] at ran
      simp only [fold?]
      cases advanced :
          advance? data initial state event with
      | none =>
          simp [advanced] at ran
      | some next =>
          simp only [advanced] at ran ⊢
          exact inductionHypothesis ran

/--
At the terminal fold state, any unconsumed publication input is rejected.
Thus entries keyed by non-pop, failed-pop, or nonexistent event IDs cannot be
silently ignored.
-/
theorem fold?_nil_eq_none_iff_publications_ne_nil
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (state : State α) :
    fold? data initial state [] = none ↔
      state.publications ≠ [] := by
  cases state with
  | mk allocator publications =>
      cases publications with
      | nil =>
          simp [fold?]
      | cons publication rest =>
          simp [fold?]

/-- Run the chronological fold over the exact canonical carrier. -/
def generate?
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (publications : List RawPublication) :
    Option (AllocatorTable α) :=
  fold? data initial
    (initialState publications) skeleton.events

/-- Boolean acceptance view of `generate?`. -/
def check
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (publications : List RawPublication) :
    Bool :=
  (generate? data initial publications).isSome

/-- Every allocator binding points to an event in the emitted prefix. -/
private def AllocatorClosed
    (allocator : AllocatorTable α)
    (events : List (Event α)) : Prop :=
  ∀ {nodeId event node},
    allocator nodeId = some (event, node) →
      event ∈ events

private theorem AllocatorClosed.append
    {allocator : AllocatorTable α}
    {events : List (Event α)}
    (closed : AllocatorClosed allocator events)
    (event : Event α) :
    AllocatorClosed allocator (events ++ [event]) := by
  intro nodeId publisher node recorded
  exact List.mem_append_left _ (closed recorded)

private theorem AllocatorClosed.insert
    {allocator : AllocatorTable α}
    {events : List (Event α)}
    (closed : AllocatorClosed allocator events)
    (nodeId : TreiberRA.NodeId)
    (publisher : Event α)
    (node : TreiberRA.Node α) :
    AllocatorClosed
      (AllocatorTable.insert allocator nodeId publisher node)
      (events ++ [publisher]) := by
  intro query recordedEvent recordedNode recorded
  by_cases same : query = nodeId
  · subst query
    rw [AllocatorTable.insert_same] at recorded
    cases Option.some.inj recorded
    simp
  · rw [AllocatorTable.insert_other
      allocator nodeId query publisher node same] at recorded
    exact List.mem_append_left _ (closed recorded)

private theorem append_closed
    {carrier emitted : List (Event α)}
    {event : Event α}
    (emittedClosed :
      ∀ candidate, candidate ∈ emitted → candidate ∈ carrier)
    (eventMember : event ∈ carrier) :
    ∀ candidate,
      candidate ∈ emitted ++ [event] →
        candidate ∈ carrier := by
  intro candidate member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with oldMember | isEvent
  · exact emittedClosed candidate oldMember
  · simpa [isEvent] using eventMember

/--
One successful executable step is justified by the corresponding generation
constructor.  Allocator publishers and the emitted prefix remain inside the
canonical carrier.
-/
private theorem advance?_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    {state next : State α}
    {event : Event α}
    {emitted : List (Event α)}
    (generated :
      GeneratedEvents data.graph initial state.allocator emitted)
    (allocatorClosed :
      AllocatorClosed state.allocator emitted)
    (emittedClosed :
      ∀ candidate,
        candidate ∈ emitted →
          candidate ∈ skeleton.events)
    (eventMember : event ∈ skeleton.events)
    (advanced :
      advance? data initial state event = some next) :
    GeneratedEvents data.graph initial next.allocator
        (emitted ++ [event]) ∧
      AllocatorClosed next.allocator (emitted ++ [event]) ∧
      ∀ candidate,
        candidate ∈ emitted ++ [event] →
          candidate ∈ skeleton.events := by
  rcases event with ⟨id, kind⟩
  cases kind with
  | initial =>
      simp only [advance?] at advanced
      cases advanced
      exact ⟨GeneratedEvents.initializer generated id,
        allocatorClosed.append _, append_closed emittedClosed eventMember⟩
  | algorithm action =>
      cases action with
      | pushLoad thread observed =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨GeneratedEvents.pushLoad generated id thread observed,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩
      | popLoad thread observed =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨GeneratedEvents.popLoad generated id thread observed,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩
      | isEmptyLoad thread observed =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨GeneratedEvents.isEmptyLoad generated id thread observed,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩
      | pushSuccess thread nodeId value expected =>
          by_cases valid :
              initial.heap nodeId = none ∧
                state.allocator nodeId = none
          · simp only [advance?, valid] at advanced
            cases advanced
            exact ⟨
              GeneratedEvents.pushSuccess generated id thread nodeId
                value expected valid.1 valid.2,
              allocatorClosed.insert nodeId
                (Event.mk id
                  (.algorithm
                    (.pushSuccess thread nodeId value expected)))
                { value := value, next := expected },
              append_closed emittedClosed eventMember⟩
          · simp [advance?, valid] at advanced
      | pushFailure thread nodeId value expected actual =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨
            GeneratedEvents.pushFailure generated id thread nodeId
              value expected actual,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩
      | popSuccess thread nodeId value nextNode =>
          cases recorded : state.allocator nodeId with
          | none =>
              simp [advance?, recorded] at advanced
          | some allocation =>
              rcases allocation with ⟨publisher, node⟩
              cases taken :
                  takePublication? id state.publications with
              | none =>
                  simp [advance?, recorded, taken] at advanced
              | some publication =>
                  rcases publication with ⟨path, remaining⟩
                  by_cases valid :
                      node =
                          { value := value, next := nextNode } ∧
                        path.source = publisher.id ∧
                        ExtendedCoherenceCheck.finalTargetId
                            path.first path.rest =
                          id ∧
                        ExtendedCoherenceCheck.check data path = true
                  · simp only [advance?, recorded, taken, valid] at advanced
                    cases advanced
                    have recordedExact :
                        state.allocator nodeId =
                          some (publisher,
                            { value := value, next := nextNode }) := by
                      simpa [valid.1] using recorded
                    obtain ⟨source, target, sourceMember,
                        targetMember, sourceId, targetId, pathEdge⟩ :=
                      ExtendedCoherenceCheck.check_sound data path
                        valid.2.2.2
                    have publisherMember :
                        publisher ∈ skeleton.events :=
                      emittedClosed publisher
                        (allocatorClosed recorded)
                    have sourceShape : source = publisher :=
                      skeleton.uniqueIds sourceMember publisherMember
                        (sourceId.trans valid.2.1)
                    have targetShape :
                        target =
                          Event.mk id
                            (.algorithm
                              (.popSuccess thread nodeId value nextNode)) :=
                      skeleton.uniqueIds targetMember eventMember
                        (targetId.trans valid.2.2.1)
                    have publicationEdge :
                        data.graph.ExtendedCoherence publisher
                          (Event.mk id
                            (.algorithm
                              (.popSuccess thread nodeId value nextNode))) := by
                      simpa [sourceShape, targetShape] using pathEdge
                    exact ⟨
                      GeneratedEvents.popSuccess generated id thread
                        nodeId value nextNode publisher recordedExact
                        publicationEdge,
                      allocatorClosed.append _,
                      append_closed emittedClosed eventMember⟩
                  · simp [advance?, recorded, taken, valid] at advanced
      | popFailure thread expected actual =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨
            GeneratedEvents.popFailure generated id thread expected actual,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩
      | popEmpty thread =>
          simp only [advance?] at advanced
          cases advanced
          exact ⟨GeneratedEvents.popEmpty generated id thread,
            allocatorClosed.append _,
            append_closed emittedClosed eventMember⟩

/--
Soundness of the chronological suffix fold, relative to an already generated
prefix.
-/
private theorem fold?_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    {state : State α}
    {remaining emitted : List (Event α)}
    {finalAllocator : AllocatorTable α}
    (generated :
      GeneratedEvents data.graph initial state.allocator emitted)
    (allocatorClosed :
      AllocatorClosed state.allocator emitted)
    (emittedClosed :
      ∀ candidate,
        candidate ∈ emitted →
          candidate ∈ skeleton.events)
    (remainingClosed :
      ∀ candidate,
        candidate ∈ remaining →
          candidate ∈ skeleton.events)
    (accepted :
      fold? data initial state remaining = some finalAllocator) :
    GeneratedEvents data.graph initial finalAllocator
      (emitted ++ remaining) := by
  induction remaining generalizing state emitted with
  | nil =>
      simp only [fold?] at accepted
      cases publicationsShape : state.publications with
      | nil =>
          simp only [publicationsShape] at accepted
          cases accepted
          simpa using generated
      | cons publication rest =>
          simp [publicationsShape] at accepted
  | cons event rest inductionHypothesis =>
      simp only [fold?] at accepted
      cases advancedShape :
          advance? data initial state event with
      | none =>
          simp [advancedShape] at accepted
      | some next =>
          simp only [advancedShape] at accepted
          have eventMember : event ∈ skeleton.events :=
            remainingClosed event (by simp)
          obtain ⟨generatedNext, allocatorClosedNext,
              emittedClosedNext⟩ :=
            advance?_sound data initial generated allocatorClosed
              emittedClosed eventMember advancedShape
          have restClosed :
              ∀ candidate,
                candidate ∈ rest →
                  candidate ∈ skeleton.events := by
            intro candidate member
            exact remainingClosed candidate
              (List.mem_cons_of_mem event member)
          have generatedFinal :=
            inductionHypothesis
              (state := next)
              (emitted := emitted ++ [event])
              generatedNext allocatorClosedNext emittedClosedNext
              restClosed accepted
          simpa [List.append_assoc] using generatedFinal

/--
If the finite executable checker returns an allocator, the exact canonical
event list is constructible by `GeneratedEvents`.
-/
theorem generate?_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (publications : List RawPublication)
    {allocator : AllocatorTable α}
    (accepted :
      generate? data initial publications = some allocator) :
    GeneratedEvents data.graph initial allocator skeleton.events := by
  apply fold?_sound data initial
      (state := initialState publications)
      (remaining := skeleton.events)
      (emitted := [])
      (finalAllocator := allocator)
  · exact GeneratedEvents.nil
  · intro nodeId event node recorded
    simp [initialState, AllocatorTable.empty] at recorded
  · simp
  · intro event eventMember
    exact eventMember
  · simpa [generate?] using accepted

/--
Boolean acceptance yields a dependent certificate containing the constructed
allocator, the exact executable result, and its logical generation proof.
-/
theorem check_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    (publications : List RawPublication)
    (checked : check data initial publications = true) :
    ∃ allocator,
      generate? data initial publications = some allocator ∧
        GeneratedEvents data.graph initial allocator skeleton.events := by
  unfold check at checked
  cases generatedShape :
      generate? data initial publications with
  | none =>
      simp [generatedShape] at checked
  | some allocator =>
      exact ⟨allocator, rfl,
        generate?_sound data initial publications generatedShape⟩

/-- No publication reserved for later may be keyed by an emitted prefix event. -/
private def PublicationsFreshFor
    (publications : List RawPublication)
    (events : List (Event α)) : Prop :=
  ∀ publication,
    publication ∈ publications →
      ∀ event,
        event ∈ events →
          publication.popEventId ≠ event.id

/-- Facts inherited by a prefix when one final canonical event is removed. -/
private structure FinalStepFacts
    (skeleton : EventGraph.Skeleton α)
    (publications : List RawPublication)
    (events : List (Event α))
    (event : Event α) : Prop where
  prefixNodup :
    events.Nodup
  prefixClosed :
    ∀ candidate,
      candidate ∈ events →
        candidate ∈ skeleton.events
  eventMember :
    event ∈ skeleton.events
  publicationsFreshForPrefix :
    PublicationsFreshFor publications events
  finalIdFresh :
    ∀ earlier,
      earlier ∈ events →
        event.id ≠ earlier.id
  publicationIdsFreshForFinal :
    ∀ publication,
      publication ∈ publications →
        publication.popEventId ≠ event.id

theorem finalStepFacts
    {skeleton : EventGraph.Skeleton α}
    {publications : List RawPublication}
    {events : List (Event α)}
    {event : Event α}
    (noDuplicates :
      (events ++ [event]).Nodup)
    (closed :
      ∀ candidate,
        candidate ∈ events ++ [event] →
          candidate ∈ skeleton.events)
    (fresh :
      PublicationsFreshFor publications
        (events ++ [event])) :
    FinalStepFacts skeleton publications events event := by
  have parts := List.nodup_append.mp noDuplicates
  have prefixClosed :
      ∀ candidate,
        candidate ∈ events →
          candidate ∈ skeleton.events := by
    intro candidate member
    exact closed candidate (List.mem_append_left _ member)
  have eventMember : event ∈ skeleton.events :=
    closed event (by simp)
  refine {
    prefixNodup := parts.1
    prefixClosed := prefixClosed
    eventMember := eventMember
    publicationsFreshForPrefix := ?_
    finalIdFresh := ?_
    publicationIdsFreshForFinal := ?_
  }
  · intro publication publicationMember candidate candidateMember
    exact fresh publication publicationMember candidate
      (List.mem_append_left _ candidateMember)
  · intro earlier earlierMember sameId
    have different : earlier ≠ event :=
      parts.2.2 earlier earlierMember event (by simp)
    exact different
      (skeleton.uniqueIds
        (prefixClosed earlier earlierMember)
        eventMember sameId.symm)
  · intro publication publicationMember
    exact fresh publication publicationMember event (by simp)

/--
Completeness invariant with an arbitrary future-publication suffix.

The returned publications are exactly the successful-pop identifiers of the
generated prefix, in chronology.  Running that prefix consumes precisely
those records and leaves `future` untouched.
-/
theorem generated_runPrefix?_complete
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    {allocator : AllocatorTable α}
    {events : List (Event α)}
    (generated :
      GeneratedEvents data.graph initial allocator events)
    (noDuplicates : events.Nodup)
    (closed :
      ∀ event,
        event ∈ events →
          event ∈ skeleton.events)
    (future : List RawPublication)
    (futureFresh :
      PublicationsFreshFor future events) :
    ∃ publications,
      publications.map RawPublication.popEventId =
          successfulPopEventIds events ∧
        runPrefix? data initial
            (initialState (publications ++ future))
            events =
          some {
            allocator := allocator
            publications := future
          } := by
  induction generated generalizing future with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · rfl
      · rfl
  | initializer generated id inductionHypothesis =>
      let event : Event α := Event.mk id .initial
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | pushLoad generated id thread observed inductionHypothesis =>
      let event : Event α :=
        Event.mk id (.algorithm (.pushLoad thread observed))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | popLoad generated id thread observed inductionHypothesis =>
      let event : Event α :=
        Event.mk id (.algorithm (.popLoad thread observed))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | isEmptyLoad generated id thread observed inductionHypothesis =>
      let event : Event α :=
        Event.mk id (.algorithm (.isEmptyLoad thread observed))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | pushSuccess generated id thread nodeId value expected
      fresh unused inductionHypothesis =>
      let event : Event α :=
        Event.mk id
          (.algorithm
            (.pushSuccess thread nodeId value expected))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        simp [advance?, fresh, unused]
  | pushFailure generated id thread nodeId value expected actual
      inductionHypothesis =>
      let event : Event α :=
        Event.mk id
          (.algorithm
            (.pushFailure thread nodeId value expected actual))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | @popSuccess priorAllocator priorEvents generated
      id thread nodeId value next publisher
      recorded publication inductionHypothesis =>
      let event : Event α :=
        Event.mk id
          (.algorithm
            (.popSuccess thread nodeId value next))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨path, pathSource, pathTarget, pathChecked⟩ :=
        ExtendedCoherenceCheck.exists_checked_path
          data publication
      let raw : RawPublication := {
        popEventId := id
        path := path
      }
      have augmentedFresh :
          PublicationsFreshFor (α := α)
            (raw :: future) priorEvents := by
        intro candidate candidateMember earlier earlierMember
        simp only [List.mem_cons] at candidateMember
        rcases candidateMember with isRaw | inFuture
        · subst candidate
          exact facts.finalIdFresh earlier earlierMember
        · exact facts.publicationsFreshForPrefix
            candidate inFuture earlier earlierMember
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed (raw :: future) augmentedFresh
      refine ⟨publications ++ [raw], ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event, raw,
          List.map_append] using congrArg
            (fun ids => ids ++ [id]) publicationIds
      · rw [show
          (publications ++ [raw]) ++ future =
            publications ++ raw :: future by
              simp [List.append_assoc]]
        rw [runPrefix?_append_singleton, prefixRun]
        have taken :
            takePublication? id (raw :: future) =
              some (path, future) := by
          exact takePublication?_cons_of_fresh id path future
            facts.publicationIdsFreshForFinal
        simp [advance?, recorded, taken,
          pathSource, pathTarget, pathChecked, raw]
  | popFailure generated id thread expected actual inductionHypothesis =>
      let event : Event α :=
        Event.mk id
          (.algorithm (.popFailure thread expected actual))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl
  | popEmpty generated id thread inductionHypothesis =>
      let event : Event α :=
        Event.mk id (.algorithm (.popEmpty thread))
      have facts :=
        finalStepFacts
          (skeleton := skeleton)
          (publications := future)
          (events := _)
          (event := event)
          noDuplicates closed futureFresh
      obtain ⟨publications, publicationIds, prefixRun⟩ :=
        inductionHypothesis facts.prefixNodup
          facts.prefixClosed future
          facts.publicationsFreshForPrefix
      refine ⟨publications, ?_, ?_⟩
      · simpa [successfulPopEventIds,
          successfulPopEventId?, event] using publicationIds
      · rw [runPrefix?_append_singleton, prefixRun]
        rfl

/--
Every logically generated canonical execution has a complete raw publication
input accepted by the executable generator.  The returned list contains
exactly one record per successful pop, in event chronology.
-/
theorem generate?_complete
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (initial : TreiberRA.State α)
    {allocator : AllocatorTable α}
    (generated :
      GeneratedEvents data.graph initial allocator skeleton.events) :
    ∃ publications,
      publications.map RawPublication.popEventId =
          successfulPopEventIds skeleton.events ∧
        generate? data initial publications =
          some allocator := by
  have futureFresh :
      PublicationsFreshFor ([] : List RawPublication)
        skeleton.events := by
    intro publication member
    simp at member
  obtain ⟨publications, publicationIds, prefixRun⟩ :=
    generated_runPrefix?_complete data initial generated
      skeleton.noDuplicateEvents
      (fun event eventMember => eventMember)
      [] futureFresh
  refine ⟨publications, publicationIds, ?_⟩
  unfold generate?
  apply fold?_of_runPrefix?_empty data initial
  simpa using prefixRun

end GeneratedEventsCheck

end WeakMemory.TreiberRC11
