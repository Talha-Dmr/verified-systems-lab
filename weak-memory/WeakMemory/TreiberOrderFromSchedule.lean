import WeakMemory.TreiberSourceExecution

namespace WeakMemory.TreiberRC11

/-!
# Constructing relation order from a finite graph schedule

A `RespectsGraph` schedule is already a concrete linear extension of program
order and extended coherence.  Consequently, the position of an event in
that duplicate-free schedule is a common strict rank for program order,
reads-from, modification order, and reads-before.

The source package at the end of this module is deliberately called a
*relation model* execution.  Its respecting schedule is a finite model
certificate; the name does not claim that an external C11 semantics has
produced it.
-/

private def OccursBefore
    (first second : β)
    (items : List β) : Prop :=
  ∃ earlier between later,
    items = earlier ++ first :: between ++ second :: later

namespace OccursBefore

/-- Strict occurrence order gives strict position order without using choice. -/
private theorem idxOf_lt
    [BEq β] [LawfulBEq β]
    {first second : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (before : OccursBefore first second items) :
    items.idxOf first < items.idxOf second := by
  induction items with
  | nil =>
      rcases before with ⟨earlier, between, later, shape⟩
      simp at shape
  | cons head tail inductionHypothesis =>
      have headFresh : head ∉ tail :=
        (List.nodup_cons.mp noDuplicates).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp noDuplicates).2
      rcases before with ⟨earlier, between, later, shape⟩
      cases earlier with
      | nil =>
          simp only [List.nil_append] at shape
          injection shape with headIsFirst tailShape
          subst first
          subst tail
          have headNeSecond : head ≠ second := by
            intro same
            subst second
            exact headFresh (by simp)
          have headBeqSecond : (head == second) = false :=
            beq_eq_false_iff_ne.mpr headNeSecond
          simp [List.idxOf_cons, headBeqSecond]
      | cons leading earlier =>
          simp only [List.cons_append] at shape
          injection shape with headIsLeading tailShape
          have tailBefore :
              OccursBefore first second tail :=
            ⟨earlier, between, later, tailShape⟩
          have firstMember : first ∈ tail := by
            rw [tailShape]
            simp
          have secondMember : second ∈ tail := by
            rw [tailShape]
            simp
          have headNeFirst : head ≠ first := by
            intro same
            subst first
            exact headFresh firstMember
          have headNeSecond : head ≠ second := by
            intro same
            subst second
            exact headFresh secondMember
          have headBeqFirst : (head == first) = false :=
            beq_eq_false_iff_ne.mpr headNeFirst
          have headBeqSecond : (head == second) = false :=
            beq_eq_false_iff_ne.mpr headNeSecond
          have tailOrder :=
            inductionHypothesis tailNodup tailBefore
          simpa [List.idxOf_cons, headBeqFirst, headBeqSecond] using
            Nat.add_lt_add_right tailOrder 1

end OccursBefore

namespace Before

/-- Mapping event identifiers preserves strict schedule occurrence order. -/
private theorem map_ids
    {first second : Event α}
    {schedule : List (Event α)}
    (before : Before first second schedule) :
    OccursBefore first.id second.id
      (schedule.map Event.id) := by
  rcases before with ⟨earlier, between, later, rfl⟩
  exact
    ⟨earlier.map Event.id,
      between.map Event.id,
      later.map Event.id, by simp⟩

end Before

/--
Mapping identifiers preserves duplicate-freedom when identifiers are
injective on every scheduled event.
-/
private theorem eventIdsNodup
    {schedule carrier : List (Event α)}
    (noDuplicates : schedule.Nodup)
    (closed :
      ∀ event, event ∈ schedule → event ∈ carrier)
    (uniqueIds :
      ∀ {left right},
        left ∈ carrier →
        right ∈ carrier →
        left.id = right.id →
        left = right) :
    (schedule.map Event.id).Nodup := by
  induction schedule with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      have headFresh : head ∉ tail :=
        (List.nodup_cons.mp noDuplicates).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp noDuplicates).2
      have tailClosed :
          ∀ event, event ∈ tail → event ∈ carrier := by
        intro event member
        exact closed event (by simp [member])
      have tailIdsNodup :=
        inductionHypothesis tailNodup tailClosed
      apply List.nodup_cons.mpr
      refine ⟨?_, tailIdsNodup⟩
      intro headIdMember
      obtain ⟨event, eventMember, eventId⟩ :=
        List.mem_map.mp headIdMember
      have sameEvent : head = event :=
        uniqueIds
          (closed head (by simp))
          (tailClosed event eventMember)
          eventId.symm
      subst event
      exact headFresh eventMember

namespace RespectsGraph

/-- A respecting canonical schedule contains no duplicate event identifiers. -/
private theorem scheduledIdsNodup
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (respects : RespectsGraph data.graph schedule) :
    (schedule.map Event.id).Nodup := by
  apply eventIdsNodup respects.noDuplicates
  · intro event member
    exact (respects.covers event).mpr member
  · intro left right leftMember rightMember sameId
    exact skeleton.uniqueIds leftMember rightMember sameId

/--
A respecting schedule constructs the common rank required by
`RC11OrderWitness`; no separately supplied numeric order is needed.
-/
def toRC11OrderWitness
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (respects : RespectsGraph data.graph schedule) :
    RC11OrderWitness data where
  rank event :=
    (schedule.map Event.id).idxOf event.id
  programOrder_lt edge :=
    OccursBefore.idxOf_lt respects.scheduledIdsNodup
      (respects.programOrder edge).map_ids
  readsFrom_lt edge :=
    OccursBefore.idxOf_lt respects.scheduledIdsNodup
      (respects.extendedCoherence
        (.readsFrom edge)).map_ids
  modificationOrder_lt edge :=
    OccursBefore.idxOf_lt respects.scheduledIdsNodup
      (respects.extendedCoherence
        (.modificationOrder edge)).map_ids
  readsBefore_lt edge :=
    OccursBefore.idxOf_lt respects.scheduledIdsNodup
      (respects.extendedCoherence
        (.readsBefore edge)).map_ids

end RespectsGraph

/--
A source execution certified inside the finite scheduled-relation model.

This package does not represent, or purport to validate, an external C11
execution.  It records concrete relation data and one duplicate-free graph
schedule that orders all program-order and extended-coherence edges.
-/
structure ScheduledRelationModelExecution
    (initial : TreiberRA.State α) where
  source :
    ControlledSource initial
  relations :
    AtomicRelationData source.skeleton
  allocator :
    AllocatorTable α
  initialHeadEmpty :
    initial.head = none
  generated :
    GeneratedEvents relations.graph initial allocator
      source.skeleton.events
  relationSchedule :
    List (Event α)
  scheduleRespectsGraph :
    RespectsGraph relations.graph relationSchedule

namespace ScheduledRelationModelExecution

/-- Forget the model schedule after using it to construct the common rank. -/
def toSourceAtomicExecution
    {initial : TreiberRA.State α}
    (execution : ScheduledRelationModelExecution initial) :
    SourceAtomicExecution initial where
  source :=
    execution.source
  relations :=
    execution.relations
  order :=
    execution.scheduleRespectsGraph.toRC11OrderWitness
  allocator :=
    execution.allocator
  initialHeadEmpty :=
    execution.initialHeadEmpty
  generated :=
    execution.generated

end ScheduledRelationModelExecution

end WeakMemory.TreiberRC11
