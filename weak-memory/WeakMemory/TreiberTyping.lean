import WeakMemory.TreiberInvariant

namespace WeakMemory.TreiberRC11

/-!
# Typed Treiber candidate graphs

`ReplayInvariant` exposes the exact facts needed by the replay proof, but a
graph client should not have to prove pairwise allocation uniqueness and pop
publication separately. This module packages node provenance as a functional
allocator table and checks every graph event against that table.

Functionality of the table makes allocation uniqueness automatic. Local event
typing supplies initial freshness, immutable pop contents, and publication
order. Failed weak compare-exchanges may be spurious.
`WeakMemory.TreiberGeneration` constructs the table and event list together,
then derives this interface automatically.
-/

/--
For each allocated node identifier, record its unique successful push event
and immutable heap entry.
-/
abbrev AllocatorTable (α : Type) :=
  TreiberRA.NodeId → Option (Event α × TreiberRA.Node α)

namespace Event

/-- Local typing rules for one Treiber graph event. -/
def TypedBy
    (graph : Graph α)
    (initial : TreiberRA.State α)
    (allocator : AllocatorTable α)
    (event : Event α) : Prop :=
  match event.kind with
  | .initial =>
      True
  | .algorithm action =>
      match action with
      | .pushLoad .. =>
          True
      | .popLoad .. =>
          True
      | .isEmptyLoad .. =>
          True
      | .pushSuccess _ nodeId value expected =>
          initial.heap nodeId = none ∧
            allocator nodeId =
              some (event, { value := value, next := expected })
      | .pushFailure .. =>
          True
      | .popSuccess _ nodeId value next =>
          ∃ publisher,
            allocator nodeId =
                some (publisher, { value := value, next := next }) ∧
              graph.ExtendedCoherence publisher event
      | .popFailure .. =>
          True
      | .popEmpty _ =>
          True

end Event

/--
A finite RC11 graph whose Treiber events are typed by one functional allocator
table.

`allocatorSound` prevents fabricated table entries: every entry must point to
an actual successful push in the graph with exactly the recorded immutable
node.
-/
structure GraphTyping
    (graph : Graph α)
    (initial : TreiberRA.State α) where
  allocator :
    AllocatorTable α
  initialHeadEmpty :
    initial.head = none
  allocatorSound :
    ∀ {nodeId : TreiberRA.NodeId}
      {event : Event α}
      {node : TreiberRA.Node α},
      allocator nodeId = some (event, node) →
      event ∈ graph.events ∧
        event.allocation? = some (nodeId, node)
  eventTyped :
    ∀ event,
      event ∈ graph.events →
      event.TypedBy graph initial allocator

namespace Event.TypedBy

/--
Typing records every successful push in the allocator table and certifies that
its node identifier is initially fresh.
-/
theorem allocationRecorded
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {allocator : AllocatorTable α}
    {event : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (typed : event.TypedBy graph initial allocator)
    (allocation :
      event.allocation? = some (nodeId, node)) :
    initial.heap nodeId = none ∧
      allocator nodeId = some (event, node) := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp [Event.allocation?] at allocation
      | algorithm action =>
          cases action with
          | pushLoad =>
              simp [Event.allocation?] at allocation
          | popLoad =>
              simp [Event.allocation?] at allocation
          | isEmptyLoad =>
              simp [Event.allocation?] at allocation
          | pushSuccess thread allocated value expected =>
              simp only [Event.allocation?, Option.some.injEq,
                Prod.mk.injEq] at allocation
              rcases allocation with ⟨allocatedIsNodeId, nodeShape⟩
              subst allocated
              subst node
              exact typed
          | pushFailure =>
              simp [Event.allocation?] at allocation
          | popSuccess =>
              simp [Event.allocation?] at allocation
          | popFailure =>
              simp [Event.allocation?] at allocation
          | popEmpty =>
              simp [Event.allocation?] at allocation

end Event.TypedBy

/--
The allocator-table interface implies every lower-level replay obligation.
-/
theorem GraphTyping.toReplayInvariant
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (typing : GraphTyping graph initial) :
    ReplayInvariant graph initial where
  initialHeadEmpty :=
    typing.initialHeadEmpty
  allocationFresh eventMember allocation := by
    exact (typing.eventTyped _ eventMember
      |>.allocationRecorded allocation).1
  allocationUnique firstMember secondMember
      firstAllocation secondAllocation := by
    have firstRecorded :=
      (typing.eventTyped _ firstMember
        |>.allocationRecorded firstAllocation).2
    have secondRecorded :=
      (typing.eventTyped _ secondMember
        |>.allocationRecorded secondAllocation).2
    have recordsEqual :
        (_, _) = (_, _) :=
      Option.some.inj (firstRecorded.symm.trans secondRecorded)
    exact congrArg Prod.fst recordsEqual
  popPublished eventMember eventShape := by
    have typed := typing.eventTyped _ eventMember
    simp only [Event.TypedBy, eventShape] at typed
    obtain ⟨publisher, recorded, publication⟩ := typed
    have sound := typing.allocatorSound recorded
    exact ⟨publisher, sound.1, sound.2, publication⟩

/-- A typed candidate graph replays in every respecting schedule. -/
theorem GraphTyping.replayAccepted
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {schedule : List (Event α)}
    (typing : GraphTyping graph initial)
    (wellFormed : WellFormed graph)
    (respects : RespectsGraph graph schedule) :
    replay? initial schedule =
      some (advanceUncheckedList initial schedule) :=
  replay?_eq_some_advanceUncheckedList
    wellFormed respects typing.toReplayInvariant

namespace CoreConsistent

/--
Core consistency and local graph typing construct the complete certified
operational schedule. Scheduling acyclicity is derived from coherence.
-/
theorem existsCertifiedSchedule_of_graphTyping
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (consistent : CoreConsistent graph)
    (typing : GraphTyping graph initial) :
    ∃ schedule final,
      RespectsGraph graph schedule ∧
        replay? initial schedule = some final ∧
        CertifiedSchedule graph initial schedule final :=
  consistent.existsCertifiedSchedule_of_replayInvariant
    typing.toReplayInvariant

end CoreConsistent

/--
End-to-end linearizability from the local typed-candidate interface.
-/
theorem linearizable_of_graphTyping
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (consistent : CoreConsistent graph)
    (typing : GraphTyping graph initial)
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
  linearizable_of_replayInvariant
    consistent typing.toReplayInvariant
    initialRepresentation

end WeakMemory.TreiberRC11
