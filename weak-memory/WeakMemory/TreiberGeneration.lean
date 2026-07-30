import WeakMemory.TreiberTyping

namespace WeakMemory.TreiberRC11

/-!
# Generating typed Treiber candidate events

`GraphTyping` accepts a completed allocator table. This module constructs that
table together with a chronological emitted-event list and requires a
permutation witness connecting that list to the graph's event carrier. Each
generation rule corresponds to one observable Treiber action and carries only
its local typing side conditions.

Successful pushes extend the functional allocator table at an unused node
identifier. Successful pops must name an already recorded immutable node and
carry its publication edge. The main theorem proves that every generated
candidate has `GraphTyping` automatically. This layer does not yet generate
`po`, `rf`, `mo`, or `eco`, nor does it enforce per-thread retry control flow.
-/

namespace AllocatorTable

/-- The allocator table before any successful push. -/
def empty : AllocatorTable α :=
  fun _ => none

/-- Record one successful push at a previously unused node identifier. -/
def insert
    (allocator : AllocatorTable α)
    (nodeId : TreiberRA.NodeId)
    (event : Event α)
    (node : TreiberRA.Node α) :
    AllocatorTable α :=
  fun query =>
    if query = nodeId then some (event, node)
    else allocator query

@[simp] theorem insert_same
    (allocator : AllocatorTable α)
    (nodeId : TreiberRA.NodeId)
    (event : Event α)
    (node : TreiberRA.Node α) :
    insert allocator nodeId event node nodeId =
      some (event, node) := by
  simp [insert]

theorem insert_other
    (allocator : AllocatorTable α)
    (nodeId query : TreiberRA.NodeId)
    (event : Event α)
    (node : TreiberRA.Node α)
    (different : query ≠ nodeId) :
    insert allocator nodeId event node query =
      allocator query := by
  simp [insert, different]

/-- Every old allocation record is preserved by a table extension. -/
def Extends
    (old new : AllocatorTable α) : Prop :=
  ∀ ⦃nodeId event node⦄,
    old nodeId = some (event, node) →
    new nodeId = some (event, node)

theorem insert_extends
    (allocator : AllocatorTable α)
    (nodeId : TreiberRA.NodeId)
    (event : Event α)
    (node : TreiberRA.Node α)
    (unused : allocator nodeId = none) :
    Extends allocator
      (insert allocator nodeId event node) := by
  intro query oldEvent oldNode oldRecord
  by_cases same : query = nodeId
  · subst query
    rw [unused] at oldRecord
    contradiction
  · simpa [insert_other, same] using oldRecord

end AllocatorTable

namespace Event.TypedBy

/-- Local event typing is preserved when the allocator table is extended. -/
theorem mono
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {old new : AllocatorTable α}
    {event : Event α}
    (extension : AllocatorTable.Extends old new)
    (typed : event.TypedBy graph initial old) :
    event.TypedBy graph initial new := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          trivial
      | algorithm action =>
          cases action with
          | pushLoad =>
              trivial
          | popLoad =>
              trivial
          | isEmptyLoad =>
              trivial
          | pushSuccess thread nodeId value expected =>
              exact ⟨typed.1, extension typed.2⟩
          | pushFailure =>
              exact typed
          | popSuccess thread nodeId value next =>
              obtain ⟨publisher, recorded, publication⟩ := typed
              exact ⟨publisher, extension recorded, publication⟩
          | popFailure =>
              exact typed
          | popEmpty =>
              trivial

end Event.TypedBy

/--
An inductively generated event list paired with the allocator table produced
by its successful pushes.
-/
inductive GeneratedEvents
    (graph : Graph α)
    (initial : TreiberRA.State α) :
    AllocatorTable α →
    List (Event α) →
    Prop where
  | nil :
      GeneratedEvents graph initial AllocatorTable.empty []
  | initializer
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id : EventId) :
      GeneratedEvents graph initial allocator
        (events ++ [Event.mk id .initial])
  | pushLoad
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread : Nat)
      (observed : Option TreiberRA.NodeId) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm (.pushLoad thread observed))
        ])
  | popLoad
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread : Nat)
      (observed : Option TreiberRA.NodeId) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm (.popLoad thread observed))
        ])
  | isEmptyLoad
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread : Nat)
      (observed : Option TreiberRA.NodeId) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm (.isEmptyLoad thread observed))
        ])
  | pushSuccess
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread nodeId : Nat)
      (value : α)
      (expected : Option TreiberRA.NodeId)
      (fresh : initial.heap nodeId = none)
      (unused : allocator nodeId = none) :
      GeneratedEvents graph initial
        (AllocatorTable.insert allocator nodeId
          (Event.mk id
            (.algorithm
              (.pushSuccess thread nodeId value expected)))
          { value := value, next := expected })
        (events ++ [
          Event.mk id
            (.algorithm
              (.pushSuccess thread nodeId value expected))
        ])
  | pushFailure
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread nodeId : Nat)
      (value : α)
      (expected actual : Option TreiberRA.NodeId) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm
              (.pushFailure thread nodeId value expected actual))
        ])
  | popSuccess
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread nodeId : Nat)
      (value : α)
      (next : Option TreiberRA.NodeId)
      (publisher : Event α)
      (recorded :
        allocator nodeId =
          some (publisher, { value := value, next := next }))
      (publication :
        graph.ExtendedCoherence publisher
          (Event.mk id
            (.algorithm
              (.popSuccess thread nodeId value next)))) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm
              (.popSuccess thread nodeId value next))
        ])
  | popFailure
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread : Nat)
      (expected actual : Option TreiberRA.NodeId) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id
            (.algorithm (.popFailure thread expected actual))
        ])
  | popEmpty
      {allocator events}
      (generated :
        GeneratedEvents graph initial allocator events)
      (id thread : Nat) :
      GeneratedEvents graph initial allocator
        (events ++ [
          Event.mk id (.algorithm (.popEmpty thread))
        ])

/-- The two properties maintained by every generation step. -/
private structure GenerationInvariant
    (graph : Graph α)
    (initial : TreiberRA.State α)
    (allocator : AllocatorTable α)
    (events : List (Event α)) : Prop where
  allocatorSound :
    ∀ {nodeId : TreiberRA.NodeId}
      {event : Event α}
      {node : TreiberRA.Node α},
      allocator nodeId = some (event, node) →
      event ∈ events ∧
        event.allocation? = some (nodeId, node)
  eventTyped :
    ∀ event,
      event ∈ events →
      event.TypedBy graph initial allocator

/--
Generation maintains allocator soundness and local typing for every emitted
event.
-/
private theorem GeneratedEvents.generationInvariant
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {allocator : AllocatorTable α}
    {events : List (Event α)}
    (generated :
      GeneratedEvents graph initial allocator events) :
    GenerationInvariant graph initial allocator events := by
  induction generated with
  | nil =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro nodeId event node recorded
        simp [AllocatorTable.empty] at recorded
      · intro event member
        simp at member
  | initializer generated id inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro nodeId event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | pushLoad generated id thread observed inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro nodeId event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | popLoad generated id thread observed inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro nodeId event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | isEmptyLoad generated id thread observed inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro nodeId event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | @pushSuccess allocator events generated id thread nodeId value
      expected fresh unused inductionHypothesis =>
      let event : Event α :=
        Event.mk id
          (.algorithm
            (.pushSuccess thread nodeId value expected))
      let node : TreiberRA.Node α :=
        { value := value, next := expected }
      have extension :
          AllocatorTable.Extends allocator
            (AllocatorTable.insert allocator nodeId event node) :=
        AllocatorTable.insert_extends
          allocator nodeId event node unused
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro query recordedEvent recordedNode recorded
        by_cases same : query = nodeId
        · subst query
          rw [AllocatorTable.insert_same] at recorded
          have recordsEqual := Option.some.inj recorded
          cases recordsEqual
          exact ⟨by simp, rfl⟩
        · rw [AllocatorTable.insert_other
            allocator nodeId query event node same] at recorded
          have sound :=
            inductionHypothesis.allocatorSound recorded
          exact ⟨by simp [sound.1], sound.2⟩
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact Event.TypedBy.mono extension
            (inductionHypothesis.eventTyped candidate oldMember)
        · subst candidate
          exact ⟨fresh,
            AllocatorTable.insert_same
              allocator nodeId event node⟩
  | pushFailure generated id thread nodeId value expected actual
      inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro allocated event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | popSuccess generated id thread nodeId value next publisher
      recorded publication inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro allocated event node allocation
        have sound :=
          inductionHypothesis.allocatorSound allocation
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          exact ⟨publisher, recorded, publication⟩
  | popFailure generated id thread expected actual inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro allocated event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial
  | popEmpty generated id thread inductionHypothesis =>
      refine {
        allocatorSound := ?_
        eventTyped := ?_
      }
      · intro allocated event node recorded
        have sound :=
          inductionHypothesis.allocatorSound recorded
        exact ⟨by simp [sound.1], sound.2⟩
      · intro event member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with oldMember | newEvent
        · exact inductionHypothesis.eventTyped event oldMember
        · subst event
          trivial

/--
A graph whose event carrier is a permutation of an emitted event list produced
together with its allocator table by the local Treiber generation rules.
-/
structure GeneratedCandidate
    (graph : Graph α)
    (initial : TreiberRA.State α) where
  allocator :
    AllocatorTable α
  emitted :
    List (Event α)
  initialHeadEmpty :
    initial.head = none
  generated :
    GeneratedEvents graph initial allocator emitted
  eventsPermutation :
    emitted.Perm graph.events

/-- Every generated candidate is a typed candidate graph. -/
def GeneratedCandidate.toGraphTyping
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (candidate : GeneratedCandidate graph initial) :
    GraphTyping graph initial := by
  have invariant :=
    candidate.generated.generationInvariant
  exact {
    allocator := candidate.allocator
    initialHeadEmpty := candidate.initialHeadEmpty
    allocatorSound := by
      intro nodeId event node recorded
      have sound := invariant.allocatorSound recorded
      exact ⟨candidate.eventsPermutation.mem_iff.mp sound.1, sound.2⟩
    eventTyped := by
      intro event member
      exact invariant.eventTyped event
        (candidate.eventsPermutation.mem_iff.mpr member)
  }

/-- A generated candidate replays in every respecting schedule. -/
theorem GeneratedCandidate.replayAccepted
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule : List (Event α)}
    (candidate : GeneratedCandidate graph initial)
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule) :
    replay? initial schedule =
      some (advanceUncheckedList initial schedule) :=
  candidate.toGraphTyping.replayAccepted
    wellFormed respects

namespace CoreConsistent

/--
Core consistency turns a generated candidate into a complete certified
operational schedule. Scheduling acyclicity is derived from coherence.
-/
theorem existsCertifiedSchedule_of_generatedCandidate
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (consistent : CoreConsistent graph)
    (candidate : GeneratedCandidate graph initial) :
    ∃ schedule final,
      RespectsGraph graph schedule ∧
        replay? initial schedule = some final ∧
        CertifiedSchedule graph initial schedule final :=
  consistent.existsCertifiedSchedule_of_graphTyping
    candidate.toGraphTyping

end CoreConsistent

/-- End-to-end linearizability for a generated Treiber candidate graph. -/
theorem linearizable_of_generatedCandidate
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (consistent : CoreConsistent graph)
    (candidate : GeneratedCandidate graph initial)
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
          finalValues :=
  linearizable_of_graphTyping
    consistent candidate.toGraphTyping
    initialRepresentation

end WeakMemory.TreiberRC11
