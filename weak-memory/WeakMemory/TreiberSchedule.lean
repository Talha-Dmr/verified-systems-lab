import WeakMemory.TreiberReplay

namespace WeakMemory.TreiberRC11

/-!
# Finite schedules for RC11-style Treiber graphs

The replay layer accepts an event schedule that already respects program order
and extended coherence. This module constructs such a schedule from a finite
graph when the union of those two ordering constraints is acyclic.

This module keeps the acyclicity premise explicit in its generic finite
scheduling theorem. `WeakMemory.TreiberOrderAcyclic` proves that, for the
current Treiber event universe, well-formedness and RC11 coherence discharge
that premise. `WeakMemory.TreiberInvariant` consumes the resulting order and
proves replay acceptance under explicit Treiber-specific graph invariants.
-/

namespace Graph

/-- Every graph edge that an operational replay schedule must respect. -/
def OrderEdge (graph : Graph α) : Relation (Event α) :=
  fun source target =>
    graph.programOrder source target ∨
      graph.ExtendedCoherence source target

/--
The combined scheduling constraint has no directed cycle.

`Acyclic` means irreflexivity, so it is applied to the transitive closure of
`OrderEdge` rather than only to its immediate edges.
-/
def OrderAcyclic (graph : Graph α) : Prop :=
  Acyclic (Relation.TransGen graph.OrderEdge)

end Graph

namespace WellFormed

/-- Every endpoint of an extended-coherence edge belongs to the finite graph. -/
theorem extendedCoherence_closed
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (edge : graph.ExtendedCoherence source target) :
    source ∈ graph.events ∧ target ∈ graph.events := by
  induction edge with
  | readsFrom readsFrom =>
      exact wellFormed.readsFromClosed readsFrom
  | modificationOrder modificationOrder =>
      exact wellFormed.modificationOrderClosed modificationOrder
  | readsBefore readsBefore =>
      rcases readsBefore with
        ⟨origin, readsFrom, modificationOrder, _⟩
      exact ⟨(wellFormed.readsFromClosed readsFrom).2,
        (wellFormed.modificationOrderClosed modificationOrder).2⟩
  | transitive first second firstClosed secondClosed =>
      exact ⟨firstClosed.1, secondClosed.2⟩

/-- Every endpoint of a combined scheduling edge belongs to the finite graph. -/
theorem orderEdge_closed
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (edge : graph.OrderEdge source target) :
    source ∈ graph.events ∧ target ∈ graph.events := by
  rcases edge with programOrder | extendedCoherence
  · exact wellFormed.programOrderClosed programOrder
  · exact wellFormed.extendedCoherence_closed extendedCoherence

end WellFormed

/--
A nonempty finite list contains an element with no predecessor whenever the
relation is transitive and irreflexive.
-/
private theorem existsMinimal
    (relation : Relation β)
    (transitive :
      ∀ {first middle last},
        relation first middle →
        relation middle last →
        relation first last)
    (irreflexive : ∀ element, ¬ relation element element)
    (nodes : List β)
    (nonempty : nodes ≠ []) :
    ∃ minimal,
      minimal ∈ nodes ∧
        ∀ predecessor,
          predecessor ∈ nodes →
          ¬ relation predecessor minimal := by
  classical
  induction nodes with
  | nil =>
      exact (nonempty rfl).elim
  | cons head tail inductionHypothesis =>
      by_cases tailEmpty : tail = []
      · subst tail
        refine ⟨head, by simp, ?_⟩
        intro predecessor predecessorMember predecessorBefore
        simp only [List.mem_cons, List.not_mem_nil, or_false] at predecessorMember
        subst predecessor
        exact irreflexive head predecessorBefore
      · obtain ⟨minimal, minimalMember, minimality⟩ :=
          inductionHypothesis tailEmpty
        by_cases headBefore : relation head minimal
        · refine ⟨head, by simp, ?_⟩
          intro predecessor predecessorMember predecessorBefore
          simp only [List.mem_cons] at predecessorMember
          rcases predecessorMember with predecessorIsHead |
            predecessorInTail
          · subst predecessor
            exact irreflexive head predecessorBefore
          · exact minimality predecessor predecessorInTail
              (transitive predecessorBefore headBefore)
        · refine ⟨minimal, by simp [minimalMember], ?_⟩
          intro predecessor predecessorMember predecessorBefore
          simp only [List.mem_cons] at predecessorMember
          rcases predecessorMember with predecessorIsHead |
            predecessorInTail
          · subst predecessor
            exact headBefore predecessorBefore
          · exact minimality predecessor predecessorInTail
              predecessorBefore

/-- Prepending one event preserves every ordering witness in the tail. -/
private theorem Before.cons
    {first second leading : Event α}
    {schedule : List (Event α)}
    (before : Before first second schedule) :
    Before first second (leading :: schedule) := by
  rcases before with ⟨earlier, between, later, scheduleShape⟩
  subst schedule
  exact ⟨leading :: earlier, between, later, rfl⟩

/-- The head of a list appears before every member of its tail. -/
private theorem before_head_of_mem
    {head target : Event α}
    {tail : List (Event α)}
    (member : target ∈ tail) :
    Before head target (head :: tail) := by
  obtain ⟨earlier, later, tailShape⟩ := List.append_of_mem member
  subst tail
  exact ⟨[], earlier, later, rfl⟩

/--
Every finite, duplicate-free carrier has a linear extension of an acyclic
relation. The resulting list is a permutation of the carrier and orders every
relation edge whose endpoints belong to that carrier.
-/
private theorem existsTopologicalSchedule
    (relation : Relation (Event α))
    (nodes : List (Event α))
    (noDuplicates : nodes.Nodup)
    (acyclic : Acyclic (Relation.TransGen relation)) :
    ∃ schedule,
      nodes.Perm schedule ∧
        ∀ {source target},
          source ∈ nodes →
          target ∈ nodes →
          relation source target →
          Before source target schedule := by
  classical
  let rec build
      (current : List (Event α))
      (currentNodup : current.Nodup) :
      ∃ schedule,
        current.Perm schedule ∧
          ∀ {source target},
            source ∈ current →
            target ∈ current →
            relation source target →
            Before source target schedule := by
    by_cases currentEmpty : current = []
    · subst current
      refine ⟨[], List.Perm.refl [], ?_⟩
      intro source target sourceMember
      simp at sourceMember
    · obtain ⟨minimal, minimalMember, minimality⟩ :=
        existsMinimal
          (Relation.TransGen relation)
          Relation.TransGen.trans
          acyclic
          current
          currentEmpty
      let remaining := current.erase minimal
      have remainingNodup : remaining.Nodup := by
        exact currentNodup.erase minimal
      obtain ⟨restSchedule, restPermutation, restRespects⟩ :=
        build remaining remainingNodup
      refine ⟨minimal :: restSchedule, ?_, ?_⟩
      · exact (List.perm_cons_erase minimalMember).trans
          (restPermutation.cons minimal)
      · intro source target sourceMember targetMember edge
        by_cases targetIsMinimal : target = minimal
        · subst target
          exact (minimality source sourceMember
            (Relation.TransGen.single edge)).elim
        · have targetInRemaining : target ∈ remaining := by
            simpa only [remaining] using
              (currentNodup.mem_erase_iff).2
                ⟨targetIsMinimal, targetMember⟩
          by_cases sourceIsMinimal : source = minimal
          · subst source
            apply before_head_of_mem
            exact restPermutation.mem_iff.mp targetInRemaining
          · have sourceInRemaining : source ∈ remaining := by
              simpa only [remaining] using
                (currentNodup.mem_erase_iff).2
                  ⟨sourceIsMinimal, sourceMember⟩
            exact (restRespects
              sourceInRemaining targetInRemaining edge).cons
    termination_by current.length
    decreasing_by
      classical
      simp only [List.length_erase_of_mem minimalMember]
      exact Nat.sub_lt
        (List.length_pos_iff.mpr currentEmpty)
        (Nat.zero_lt_succ 0)
  exact build nodes noDuplicates

/--
An acyclic `po ∪ eco` constraint on a well-formed finite graph produces a
schedule that covers every event once and respects both constituent orders.
-/
theorem exists_respectsGraph_of_orderAcyclic
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (orderAcyclic : graph.OrderAcyclic) :
    ∃ schedule, RespectsGraph graph schedule := by
  obtain ⟨schedule, permutation, respectsOrder⟩ :=
    existsTopologicalSchedule
      graph.OrderEdge
      graph.events
      wellFormed.noDuplicateEvents
      orderAcyclic
  refine ⟨schedule, {
    covers := ?_
    noDuplicates := ?_
    programOrder := ?_
    extendedCoherence := ?_
  }⟩
  · intro event
    exact permutation.mem_iff
  · exact permutation.nodup wellFormed.noDuplicateEvents
  · intro source target edge
    have closed := wellFormed.orderEdge_closed (Or.inl edge)
    exact respectsOrder closed.1 closed.2 (Or.inl edge)
  · intro source target edge
    have closed := wellFormed.orderEdge_closed (Or.inr edge)
    exact respectsOrder closed.1 closed.2 (Or.inr edge)

namespace CoreConsistent

/--
A core-consistent graph has a respecting schedule once the combined scheduling
relation is explicitly known to be acyclic.
-/
theorem existsRespectsGraph
    {graph : Graph α}
    (consistent : CoreConsistent graph)
    (orderAcyclic : graph.OrderAcyclic) :
    ∃ schedule, RespectsGraph graph schedule :=
  exists_respectsGraph_of_orderAcyclic
    consistent.toWellFormed
    orderAcyclic

end CoreConsistent

end WeakMemory.TreiberRC11
