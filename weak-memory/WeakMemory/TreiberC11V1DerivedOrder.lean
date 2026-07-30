import WeakMemory.TreiberC11V1Execution

namespace WeakMemory.TreiberC11V1

/-!
# Deriving the client-compatible execution order

The independent RC11 candidate does not carry a downstream validator
schedule.  Cross-thread client real time is nevertheless extra-semantic:
without an explicit client-synchronization model it need not agree with the
atomic graph order.  We therefore state only the necessary declarative
admissibility condition: adding committed real-time edges to independent
program order and extended coherence must remain acyclic.

A finite topological construction below derives the concrete
`ClientCompatibleOrder`.  Thus a supported semantic execution carries no
manually selected event list or numeric rank.
-/

/-- A real-time edge connected to the two atoms that commit its operations. -/
def CommitRealTimeEdge
    (candidate : RC11.Candidate α)
    (source target : RC11.Atom α) : Prop :=
  ∃ first second : ClientOperation,
    source.commitOperation? = some first ∧
      target.commitOperation? = some second ∧
      RealTimeEdge candidate.trace first second

/--
Every ordering constraint on the finite independent atom carrier.

Carrier membership is explicit for the client-real-time branch, whose
operation keys alone otherwise carry no atom-membership evidence.
-/
def ClientOrderEdge
    (candidate : RC11.Candidate α) :
    Relation (RC11.Atom α) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      (RC11.PO candidate source target ∨
        RC11.ECO candidate source target ∨
        CommitRealTimeEdge candidate source target)

/--
Client real time is admissible when the union of independent `po`, `eco`, and
committed cross-thread real-time edges has no cycle.
-/
def ClientOrderAcyclic
    (candidate : RC11.Candidate α) : Prop :=
  RC11.Acyclic
    (Relation.TransGen (ClientOrderEdge candidate))

/--
An execution admitted by the declarative source/RC11/client semantics.

Unlike `SupportedExecution`, this structure contains no selected schedule.
`toSupportedExecution` below constructs that internal scheduling certificate.
-/
structure DeclarativeExecution (α : Type) where
  candidate :
    RC11.Candidate α
  rc11 :
    RC11.Valid candidate
  client :
    ClientContract candidate
  clientOrderAcyclic :
    ClientOrderAcyclic candidate

namespace DerivedOrder

/--
A nonempty finite list has a minimal element under a transitive irreflexive
relation.
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
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at predecessorMember
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

private theorem occursBefore_cons
    {first second leading : β}
    {schedule : List β}
    (before : OccursBefore first second schedule) :
    OccursBefore first second (leading :: schedule) := by
  obtain ⟨earlier, between, later, scheduleShape⟩ := before
  subst schedule
  exact ⟨leading :: earlier, between, later, rfl⟩

private theorem occursBefore_head_of_mem
    {head target : β}
    {tail : List β}
    (member : target ∈ tail) :
    OccursBefore head target (head :: tail) := by
  obtain ⟨earlier, later, tailShape⟩ :=
    List.append_of_mem member
  subst tail
  exact ⟨[], earlier, later, rfl⟩

/--
Every finite duplicate-free carrier has a linear extension of an acyclic
relation.
-/
private theorem existsTopologicalOrder
    (relation : Relation β)
    (nodes : List β)
    (noDuplicates : nodes.Nodup)
    (acyclic : RC11.Acyclic (Relation.TransGen relation)) :
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
            exact occursBefore_cons
              (restRespects
                sourceInRemaining targetInRemaining edge)
    termination_by current.length
    decreasing_by
      classical
      simp only [List.length_erase_of_mem minimalMember]
      exact Nat.sub_lt
        (List.length_pos_iff.mpr currentEmpty)
        (Nat.zero_lt_succ 0)
  exact build nodes noDuplicates

private theorem occursBefore_map
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items)
    (project : β → γ) :
    OccursBefore
      (project first) (project second)
      (items.map project) := by
  obtain ⟨earlier, between, later, shape⟩ := before
  refine
    ⟨earlier.map project, between.map project,
      later.map project, ?_⟩
  simp [shape]

private theorem occursBefore_filterMap
    {first second : β}
    {items : List β}
    {project : β → Option γ}
    {firstOutput secondOutput : γ}
    (before : OccursBefore first second items)
    (firstProjects : project first = some firstOutput)
    (secondProjects : project second = some secondOutput) :
    OccursBefore firstOutput secondOutput
      (items.filterMap project) := by
  obtain ⟨earlier, between, later, shape⟩ := before
  refine
    ⟨earlier.filterMap project,
      between.filterMap project,
      later.filterMap project, ?_⟩
  simp [shape, firstProjects, secondProjects]

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
          simpa [List.idxOf_cons, headBeqFirst,
            headBeqSecond] using
              Nat.add_lt_add_right tailOrder 1

private theorem nodup_of_map_nodup
    {items : List β}
    {project : β → γ}
    (projectedNodup : (items.map project).Nodup) :
    items.Nodup := by
  induction items with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp projectedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        exact parts.1
          (List.mem_map.mpr ⟨head, headMember, rfl⟩)
      · exact inductionHypothesis parts.2

/--
Declarative client-order acyclicity yields the exact internal scheduling
certificate used by the refinement modules.
-/
theorem existsClientCompatibleOrder
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate)
    (acyclic : ClientOrderAcyclic candidate) :
    Nonempty (ClientCompatibleOrder candidate) := by
  classical
  have atomsNodup : candidate.atoms.Nodup :=
    nodup_of_map_nodup valid.atomIdsNodup
  obtain ⟨schedule, carrierPermutation, respects⟩ :=
    existsTopologicalOrder
      (ClientOrderEdge candidate)
      candidate.atoms atomsNodup acyclic
  have scheduledIdsNodup :
      (schedule.map RC11.Atom.id).Nodup :=
    (carrierPermutation.map RC11.Atom.id).nodup
      valid.atomIdsNodup
  have idBefore_of_edge
      {source target : RC11.Atom α}
      (sourceMember : source ∈ candidate.atoms)
      (targetMember : target ∈ candidate.atoms)
      (edge : ClientOrderEdge candidate source target) :
      RC11.IdBefore source.id target.id
        (schedule.map RC11.Atom.id) := by
    have before :=
      respects sourceMember targetMember edge
    refine
      ⟨List.mem_map.mpr
          ⟨source, carrierPermutation.mem_iff.mp sourceMember, rfl⟩,
        List.mem_map.mpr
          ⟨target, carrierPermutation.mem_iff.mp targetMember, rfl⟩,
        ?_⟩
    exact occursBefore_idxOf_lt scheduledIdsNodup
      (occursBefore_map before RC11.Atom.id)
  refine ⟨{
    schedule :=
      schedule
    exactAtoms :=
      carrierPermutation.symm
    programOrder := ?_
    extendedCoherence := ?_
    realTime := ?_
  }⟩
  · intro source target edge
    exact idBefore_of_edge edge.1 edge.2.1
      ⟨edge.1, edge.2.1, Or.inl edge⟩
  · intro source target edge
    have endpoints : source ∈ candidate.atoms ∧
        target ∈ candidate.atoms := by
      induction edge with
      | readsFrom readsFrom =>
          exact ⟨readsFrom.1, readsFrom.2.1⟩
      | modificationOrder modificationOrder =>
          exact ⟨modificationOrder.1,
            modificationOrder.2.1⟩
      | readsBefore readsBefore =>
          obtain ⟨origin, readsFrom,
            modificationOrder, different⟩ := readsBefore
          exact ⟨readsFrom.2.1,
            modificationOrder.2.1⟩
      | transitive first second firstClosed secondClosed =>
          exact ⟨firstClosed.1, secondClosed.2⟩
    exact idBefore_of_edge endpoints.1 endpoints.2
      ⟨endpoints.1, endpoints.2, Or.inr (Or.inl edge)⟩
  · intro first second firstMember secondMember realTime
    obtain ⟨source, sourceMember, sourceProjects⟩ :=
      List.mem_filterMap.mp firstMember
    obtain ⟨target, targetMember, targetProjects⟩ :=
      List.mem_filterMap.mp secondMember
    have sourceCarrier :
        source ∈ candidate.atoms :=
      carrierPermutation.mem_iff.mpr sourceMember
    have targetCarrier :
        target ∈ candidate.atoms :=
      carrierPermutation.mem_iff.mpr targetMember
    have before :=
      respects sourceCarrier targetCarrier
        ⟨sourceCarrier, targetCarrier,
          Or.inr (Or.inr
            ⟨first, second, sourceProjects,
              targetProjects, realTime⟩)⟩
    exact occursBefore_filterMap
      before sourceProjects targetProjects

/-- Choose the derived finite client-compatible order. -/
noncomputable def clientCompatibleOrder
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate)
    (acyclic : ClientOrderAcyclic candidate) :
    ClientCompatibleOrder candidate :=
  Classical.choice
    (existsClientCompatibleOrder valid acyclic)

end DerivedOrder

namespace DeclarativeExecution

/--
Forget only that the internal order was topologically derived, exposing the
existing bridge package without adding any semantic premise.
-/
noncomputable def toSupportedExecution
    (execution : DeclarativeExecution α) :
    SupportedExecution α where
  candidate :=
    execution.candidate
  rc11 :=
    execution.rc11
  client :=
    execution.client
  order :=
    DerivedOrder.clientCompatibleOrder
      execution.rc11 execution.clientOrderAcyclic

private theorem empty_clientOrderEdge_false
    (payload : NodeId → α)
    {source target : RC11.Atom α} :
    ¬ ClientOrderEdge
        (RC11.Candidate.empty payload) source target := by
  intro edge
  let supported := SupportedExecution.empty payload
  have sourceIsInitial :
      source = (.initial : RC11.Atom α) := by
    simpa [RC11.Candidate.empty,
      RC11.Candidate.atoms,
      RC11.Candidate.nonInitialAtoms] using edge.1
  have targetIsInitial :
      target = (.initial : RC11.Atom α) := by
    simpa [RC11.Candidate.empty,
      RC11.Candidate.atoms,
      RC11.Candidate.nonInitialAtoms] using edge.2.1
  subst source
  subst target
  rcases edge.2.2 with programOrder | coherenceOrRealTime
  · have ordered :=
      supported.order.programOrder programOrder
    exact (Nat.lt_irrefl _) ordered.2.2
  · rcases coherenceOrRealTime with
      extendedCoherence | realTime
    · have ordered :=
        supported.order.extendedCoherence
          extendedCoherence
      exact (Nat.lt_irrefl _) ordered.2.2
    · obtain ⟨first, second, sourceCommit,
          targetCommit, clientEdge⟩ := realTime
      simp [RC11.Atom.commitOperation?] at sourceCommit

/-- The declarative semantic execution type is inhabited. -/
def empty
    (payload : NodeId → α) :
    DeclarativeExecution α := by
  let supported := SupportedExecution.empty payload
  exact {
    candidate :=
      supported.candidate
    rc11 :=
      supported.rc11
    client :=
      supported.client
    clientOrderAcyclic := by
      intro atom cycle
      have noPath :
          ∀ {source target : RC11.Atom α},
            ¬ Relation.TransGen
              (ClientOrderEdge
                (RC11.Candidate.empty payload))
              source target := by
        intro source target path
        induction path with
        | single edge =>
            exact empty_clientOrderEdge_false payload edge
        | tail path edge inductionHypothesis =>
            exact inductionHypothesis
      exact noPath cycle
  }

end DeclarativeExecution

end WeakMemory.TreiberC11V1
