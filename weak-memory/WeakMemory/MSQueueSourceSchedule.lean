import WeakMemory.MSQueueSourceChain

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Finite atom schedules for source-backed Michael--Scott executions

`AtomSchedule` is the operational ordering boundary used by the structural
queue replay.  This module constructs that boundary rather than asking a
caller to choose a favorable enumeration: every candidate atom occurs exactly
once, and every `po` or `eco` edge points forward in the resulting list.

The one semantic premise is explicit.  The transitive closure of `po ∪ eco`
must be acyclic.  RC11 validity alone does not silently discharge this premise;
algorithm-specific reasoning may establish it for a more restricted class of
executions.
-/

/-- Every RC11 edge that an operational atom schedule must respect. -/
def AtomOrderEdge
    (candidate : MultiLocationRC11.Candidate Location Value) :
    Relation (MultiLocationRC11.Atom Location Value) :=
  fun source target =>
    MultiLocationRC11.PO candidate source target ∨
      MultiLocationRC11.ECO candidate source target

/-- The finite scheduling constraint `po ∪ eco` has no directed cycle. -/
def AtomOrderAcyclic
    (candidate : MultiLocationRC11.Candidate Location Value) : Prop :=
  MultiLocationRC11.Acyclic
    (Relation.TransGen (AtomOrderEdge candidate))

/-- A common strict rank for `po`, `rf`, `mo`, and `rb` excludes schedule cycles. -/
theorem atomOrderAcyclic_of_orderWitness
    {candidate : MultiLocationRC11.Candidate Location Value}
    (witness : MultiLocationRC11.OrderWitness candidate) :
    AtomOrderAcyclic candidate := by
  intro atom cycle
  have pathIncreases :
      ∀ {source target},
        Relation.TransGen (AtomOrderEdge candidate) source target →
          witness.rank source < witness.rank target := by
    intro source target path
    induction path with
    | single edge =>
        rcases edge with programOrder | extendedCoherence
        · exact witness.programOrderIncreases programOrder
        · exact witness.extendedCoherenceIncreases extendedCoherence
    | tail path edge pathIncreases =>
        rcases edge with programOrder | extendedCoherence
        · exact Nat.lt_trans pathIncreases
            (witness.programOrderIncreases programOrder)
        · exact Nat.lt_trans pathIncreases
            (witness.extendedCoherenceIncreases extendedCoherence)
  exact Nat.lt_irrefl _ (pathIncreases cycle)

/-- Every endpoint of a scheduling edge belongs to the candidate carrier. -/
theorem atomOrderEdge_closed
    {candidate : MultiLocationRC11.Candidate Location Value}
    {source target : MultiLocationRC11.Atom Location Value}
    (edge : AtomOrderEdge candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms := by
  rcases edge with programOrder | extendedCoherence
  · exact ⟨programOrder.1, programOrder.2.1⟩
  · exact extendedCoherence_closed extendedCoherence

namespace FiniteTopological

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

/-- Strict occurrence order in a finite list. -/
private def OccursBefore
    (first second : β)
    (items : List β) : Prop :=
  ∃ earlier between later,
    items = earlier ++ first :: between ++ second :: later

/-- Prepending an item preserves every strict occurrence order in the tail. -/
private theorem OccursBefore.cons
    {first second leading : β}
    {items : List β}
    (before : OccursBefore first second items) :
    OccursBefore first second (leading :: items) := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  exact ⟨leading :: earlier, between, later, rfl⟩

/-- The head of a list occurs before every member of its tail. -/
private theorem occursBefore_head_of_mem
    {head target : β}
    {tail : List β}
    (member : target ∈ tail) :
    OccursBefore head target (head :: tail) := by
  obtain ⟨earlier, later, tailShape⟩ := List.append_of_mem member
  subst tail
  exact ⟨[], earlier, later, rfl⟩

/--
Every finite duplicate-free carrier has a linear extension of an acyclic
relation.
-/
private theorem existsLinearExtension
    (relation : Relation β)
    (nodes : List β)
    (noDuplicates : nodes.Nodup)
    (acyclic : MultiLocationRC11.Acyclic (Relation.TransGen relation)) :
    ∃ schedule,
      nodes.Perm schedule ∧
        ∀ {source target},
          source ∈ nodes →
          target ∈ nodes →
          relation source target →
          OccursBefore source target schedule := by
  classical
  let rec build
      (current : List β)
      (currentNodup : current.Nodup) :
      ∃ schedule,
        current.Perm schedule ∧
          ∀ {source target},
            source ∈ current →
            target ∈ current →
            relation source target →
            OccursBefore source target schedule := by
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
      have remainingNodup : remaining.Nodup :=
        currentNodup.erase minimal
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
            exact occursBefore_head_of_mem
              (restPermutation.mem_iff.mp targetInRemaining)
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

/-- Strict occurrence order is preserved by mapping a list. -/
private theorem occursBefore_map
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items)
    (project : β → γ) :
    OccursBefore
      (project first) (project second) (items.map project) := by
  rcases before with ⟨earlier, between, later, shape⟩
  refine
    ⟨earlier.map project, between.map project,
      later.map project, ?_⟩
  simp [shape]

/-- Strict occurrence order gives strict `idxOf` order. -/
private theorem occursBefore_idxOf_lt
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
          have tailBefore : OccursBefore first second tail :=
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
          simpa [List.idxOf_cons, headBeqFirst,
            headBeqSecond] using
              Nat.add_lt_add_right tailOrder 1

private theorem nodup_of_map_nodup
    {items : List β}
    {project : β → γ}
    (projectedNodup : (items.map project).Nodup) :
    items.Nodup := by
  induction items with
  | nil => simp
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp projectedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        exact parts.1
          (List.mem_map.mpr ⟨head, headMember, rfl⟩)
      · exact inductionHypothesis parts.2

/--
Topologically sort a source-backed candidate and package the result as the
exact `AtomSchedule` consumed by structural replay.
-/
theorem existsAtomSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    (orderAcyclic : AtomOrderAcyclic execution.candidate) :
    Nonempty (AtomSchedule execution) := by
  classical
  have candidateAtomsNodup : execution.candidate.atoms.Nodup :=
    nodup_of_map_nodup execution.valid.atomIdsNodup
  obtain ⟨schedule, carrierPermutation, respects⟩ :=
    existsLinearExtension
      (AtomOrderEdge execution.candidate)
      execution.candidate.atoms
      candidateAtomsNodup
      orderAcyclic
  have scheduledIdsNodup :
      (schedule.map MultiLocationRC11.Atom.id).Nodup :=
    (carrierPermutation.map MultiLocationRC11.Atom.id).nodup
      execution.valid.atomIdsNodup
  have idBefore_of_edge
      {source target : MultiLocationRC11.Atom Site Ptr}
      (edge : AtomOrderEdge execution.candidate source target) :
      MultiLocationRC11.IdBefore source.id target.id
        (schedule.map MultiLocationRC11.Atom.id) := by
    have endpoints := atomOrderEdge_closed edge
    have before := respects endpoints.1 endpoints.2 edge
    have mappedBefore :=
      occursBefore_map before MultiLocationRC11.Atom.id
    have sourceMember :
        source.id ∈ schedule.map MultiLocationRC11.Atom.id := by
      rcases mappedBefore with ⟨earlier, between, later, shape⟩
      rw [shape]
      simp
    have targetMember :
        target.id ∈ schedule.map MultiLocationRC11.Atom.id := by
      rcases mappedBefore with ⟨earlier, between, later, shape⟩
      rw [shape]
      simp
    exact ⟨
      sourceMember,
      targetMember,
      occursBefore_idxOf_lt scheduledIdsNodup mappedBefore⟩
  refine ⟨{
    atoms := schedule
    permutation := carrierPermutation.symm
    respectsProgramOrder := ?_
    respectsExtendedCoherence := ?_
  }⟩
  · intro source target edge
    exact idBefore_of_edge (Or.inl edge)
  · intro source target edge
    exact idBefore_of_edge (Or.inr edge)

end FiniteTopological

namespace AtomSchedule

/-- Public constructor for a finite `po ∪ eco`-respecting atom schedule. -/
theorem exists_of_orderAcyclic
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    (orderAcyclic : AtomOrderAcyclic execution.candidate) :
    Nonempty (AtomSchedule execution) :=
  FiniteTopological.existsAtomSchedule execution orderAcyclic

/-- A checked common RC11 rank is a convenient sufficient schedule witness. -/
theorem exists_of_orderWitness
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    (witness : MultiLocationRC11.OrderWitness execution.candidate) :
    Nonempty (AtomSchedule execution) :=
  exists_of_orderAcyclic execution
    (atomOrderAcyclic_of_orderWitness witness)

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
