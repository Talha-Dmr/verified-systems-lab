import WeakMemory.TreiberC11V1InfiniteWitnessPrefix

namespace WeakMemory.TreiberC11V1

/-!
# Fairness of the concrete infinite Treiber witness

This module proves the temporal assumptions for the concrete push-only
execution.  The finite RC11 carrier is constructed in
`TreiberC11V1InfiniteWitnessPrefix`.
-/

namespace InfiniteWitness

private theorem source_phase_cases (time : Nat) :
    time % 5 = 0 ∨
      time % 5 = 1 ∨
      time % 5 = 2 ∨
      time % 5 = 3 ∨
      time % 5 = 4 := by
  omega

/-- Every source atomic event has the expected phase and dense identifier. -/
theorem source_atomic_id_shape
    (time : Nat)
    (atomic : AtomicOccurrence Unit)
    (atTime :
      source.event time = .atomic atomic) :
    (time % 5 = 1 ∧
        atomic.id = 2 * (time / 5) + 1) ∨
      (time % 5 = 3 ∧
        atomic.id = 2 * (time / 5) + 2) := by
  rcases source_phase_cases time with
      phase | phase | phase | phase | phase
  · simp [source, event, phase] at atTime
  · left
    refine ⟨phase, ?_⟩
    simp [source, event, phase] at atTime
    subst atomic
    rfl
  · simp [source, event, phase] at atTime
  · right
    refine ⟨phase, ?_⟩
    simp [source, event, phase] at atTime
    subst atomic
    rfl
  · simp [source, event, phase] at atTime

/--
Dense atomic identifiers respect source time.  This connects the finite RC11
numbering to the position-indexed infinite memory graph.
-/
theorem source_atomic_time_le_of_id_le
    {firstTime secondTime : Nat}
    {first second : AtomicOccurrence Unit}
    (firstAt :
      source.event firstTime = .atomic first)
    (secondAt :
      source.event secondTime = .atomic second)
    (ordered : first.id ≤ second.id) :
    firstTime ≤ secondTime := by
  have firstDivision := Nat.mod_add_div firstTime 5
  have secondDivision := Nat.mod_add_div secondTime 5
  rcases source_atomic_id_shape firstTime first firstAt with
      ⟨firstPhase, firstId⟩ |
      ⟨firstPhase, firstId⟩
  · rcases source_atomic_id_shape secondTime second secondAt with
        ⟨secondPhase, secondId⟩ |
        ⟨secondPhase, secondId⟩
    · have numericOrder :
          2 * (firstTime / 5) + 1 ≤
            2 * (secondTime / 5) + 1 := by
        calc
          _ = first.id := firstId.symm
          _ ≤ second.id := ordered
          _ = _ := secondId
      omega
    · have numericOrder :
          2 * (firstTime / 5) + 1 ≤
            2 * (secondTime / 5) + 2 := by
        calc
          _ = first.id := firstId.symm
          _ ≤ second.id := ordered
          _ = _ := secondId
      omega
  · rcases source_atomic_id_shape secondTime second secondAt with
        ⟨secondPhase, secondId⟩ |
        ⟨secondPhase, secondId⟩
    · have numericOrder :
          2 * (firstTime / 5) + 2 ≤
            2 * (secondTime / 5) + 1 := by
        calc
          _ = first.id := firstId.symm
          _ ≤ second.id := ordered
          _ = _ := secondId
      omega
    · have numericOrder :
          2 * (firstTime / 5) + 2 ≤
            2 * (secondTime / 5) + 2 := by
        calc
          _ = first.id := firstId.symm
          _ ≤ second.id := ordered
          _ = _ := secondId
      omega

/-- Strict atomic-identifier order gives strict source-time order. -/
theorem source_atomic_time_lt_of_id_lt
    {firstTime secondTime : Nat}
    {first second : AtomicOccurrence Unit}
    (firstAt :
      source.event firstTime = .atomic first)
    (secondAt :
      source.event secondTime = .atomic second)
    (ordered : first.id < second.id) :
    firstTime < secondTime := by
  have firstDivision := Nat.mod_add_div firstTime 5
  have secondDivision := Nat.mod_add_div secondTime 5
  rcases source_atomic_id_shape firstTime first firstAt with
      ⟨firstPhase, firstId⟩ |
      ⟨firstPhase, firstId⟩
  · rcases source_atomic_id_shape secondTime second secondAt with
        ⟨secondPhase, secondId⟩ |
        ⟨secondPhase, secondId⟩
    · have numericOrder :
          2 * (firstTime / 5) + 1 <
            2 * (secondTime / 5) + 1 := by
        calc
          _ = first.id := firstId.symm
          _ < second.id := ordered
          _ = _ := secondId
      omega
    · have numericOrder :
          2 * (firstTime / 5) + 1 <
            2 * (secondTime / 5) + 2 := by
        calc
          _ = first.id := firstId.symm
          _ < second.id := ordered
          _ = _ := secondId
      omega
  · rcases source_atomic_id_shape secondTime second secondAt with
        ⟨secondPhase, secondId⟩ |
        ⟨secondPhase, secondId⟩
    · have numericOrder :
          2 * (firstTime / 5) + 2 <
            2 * (secondTime / 5) + 1 := by
        calc
          _ = first.id := firstId.symm
          _ < second.id := ordered
          _ = _ := secondId
      omega
    · have numericOrder :
          2 * (firstTime / 5) + 2 <
            2 * (secondTime / 5) + 2 := by
        calc
          _ = first.id := firstId.symm
          _ < second.id := ordered
          _ = _ := secondId
      omega

/--
If a concrete read's source precedes a write in modification order, the read
identifier is no later than that write identifier.  Equality is precisely the
RMW self-edge later excluded from `fr`.
-/
theorem readSource_target_le_of_modificationOrder
    {target sourceId write : EventId}
    (readsFrom : readSource target = some sourceId)
    (ordered : modificationOrder sourceId write) :
    target ≤ write := by
  cases target with
  | zero =>
      simp [readSource] at readsFrom
  | succ index =>
      have sourceExact :
          sourceId = writeId (index / 2) := by
        exact (Option.some.inj readsFrom).symm
      obtain ⟨firstGeneration, secondGeneration,
          firstId, secondId, generationOrder⟩ := ordered
      have indexDivision := Nat.mod_add_div index 2
      have indexRemainder : index % 2 < 2 :=
        Nat.mod_lt index (by decide)
      have firstGenerationExact :
          firstGeneration = index / 2 := by
        apply writeId_injective
        rw [← firstId, sourceExact]
      have indexBeforeNextGeneration :
          index + 1 ≤ writeId (index / 2 + 1) := by
        simp only [writeId]
        omega
      have nextGenerationBefore :
          index / 2 + 1 ≤ secondGeneration := by
        omega
      calc
        index + 1 ≤ writeId (index / 2 + 1) :=
          indexBeforeNextGeneration
        _ ≤ writeId secondGeneration := by
          exact
            Nat.mul_le_mul_left 2 nextGenerationBefore
        _ = write := secondId.symm

/-- Every concrete source atomic occurrence has a positive identifier. -/
theorem source_atomic_id_pos
    {time : Nat}
    {atomic : AtomicOccurrence Unit}
    (atTime :
      source.event time = .atomic atomic) :
    0 < atomic.id := by
  rcases source_atomic_id_shape time atomic atTime with
      ⟨_, atomicId⟩ | ⟨_, atomicId⟩
  · rw [atomicId]
    exact Nat.add_pos_right _ (by decide)
  · rw [atomicId]
    exact Nat.add_pos_right _ (by decide)

/-- A non-initial graph position necessarily represents one source atomic. -/
theorem graphEventId?_succ_shape
    {time : Nat}
    {eventId : EventId}
    (atPosition :
      execution.graphEventId? (time + 1) =
        some eventId) :
    ∃ atomic : AtomicOccurrence Unit,
      source.event time = .atomic atomic ∧
        atomic.id = eventId := by
  cases eventAt : source.event time <;>
    simp [InfiniteRC11Execution.graphEventId?,
      execution, eventAt] at atPosition
  rename_i atomic
  exact ⟨atomic, rfl, atPosition⟩

/--
Numeric identifier order in the concrete graph respects source-position
order.  Position zero is the initializer and position `time + 1` represents
the transition at source time `time`.
-/
theorem graph_position_le_of_id_le
    {firstPosition secondPosition : Nat}
    {firstId secondId : EventId}
    (firstAt :
      execution.graphEventId? firstPosition =
        some firstId)
    (secondAt :
      execution.graphEventId? secondPosition =
        some secondId)
    (ordered : firstId ≤ secondId) :
    firstPosition ≤ secondPosition := by
  cases firstPosition with
  | zero =>
      exact Nat.zero_le secondPosition
  | succ firstTime =>
      obtain ⟨firstAtomic, firstEvent, firstIdExact⟩ :=
        graphEventId?_succ_shape firstAt
      cases secondPosition with
      | zero =>
          have secondIdExact : secondId = 0 := by
            simpa [InfiniteRC11Execution.graphEventId?,
              execution] using secondAt.symm
          rw [secondIdExact] at ordered
          rw [← firstIdExact] at ordered
          exact
            (Nat.not_le_of_gt
              (source_atomic_id_pos firstEvent)
              ordered).elim
      | succ secondTime =>
          obtain ⟨secondAtomic, secondEvent, secondIdExact⟩ :=
            graphEventId?_succ_shape secondAt
          apply Nat.succ_le_succ
          apply source_atomic_time_le_of_id_le
            firstEvent secondEvent
          rw [firstIdExact, secondIdExact]
          exact ordered

/-- Concrete modification-order edges point forward in graph positions. -/
theorem execution_modificationOrderAt_position_lt
    {firstPosition secondPosition : Nat}
    (edge :
      execution.ModificationOrderAt
        firstPosition secondPosition) :
    firstPosition < secondPosition := by
  obtain ⟨firstId, secondId, firstAt, secondAt, ordered⟩ :=
    edge
  have idOrder : firstId < secondId := by
    exact modificationOrder_id_lt ordered
  have positionOrder :
      firstPosition ≤ secondPosition :=
    graph_position_le_of_id_le
      firstAt secondAt (Nat.le_of_lt idOrder)
  apply Nat.lt_of_le_of_ne positionOrder
  intro samePosition
  subst secondPosition
  have sameId : firstId = secondId :=
    Option.some.inj (firstAt.symm.trans secondAt)
  exact (Nat.ne_of_lt idOrder) sameId

/-- Concrete from-read edges point forward in graph positions. -/
theorem execution_fromReadAt_position_lt
    {readPosition writePosition : Nat}
    (edge :
      execution.FromReadAt
        readPosition writePosition) :
    readPosition < writePosition := by
  obtain ⟨readId, sourceId, writeId,
      readAt, writeAt, readsFrom, ordered, different⟩ :=
    edge
  have idOrder : readId ≤ writeId :=
    readSource_target_le_of_modificationOrder
      readsFrom ordered
  have positionOrder :
      readPosition ≤ writePosition :=
    graph_position_le_of_id_le
      readAt writeAt idOrder
  exact Nat.lt_of_le_of_ne positionOrder different

/-- The concrete position-indexed modification order and from-read are finite. -/
theorem execution_memoryFair :
    execution.MemoryFair := by
  constructor
  · intro target
    refine ⟨target, ?_⟩
    intro sourcePosition edge
    exact execution_modificationOrderAt_position_lt edge
  · intro target
    refine ⟨target, ?_⟩
    intro readPosition edge
    exact execution_fromReadAt_position_lt edge

/-- The concrete execution inherits weak scheduling fairness from its source. -/
theorem execution_threadFair :
    execution.source.WeakThreadFair := by
  simpa [execution] using source_threadFair

/--
Primitive justice holds because every suffix already contains a successful
weak CAS, so no all-failure stable suffix can satisfy the justice premise.
-/
theorem execution_weakCASJustice :
    execution.WeakCASJustice := by
  intro thread start noSuccess _
  obtain ⟨time, afterStart, successful⟩ :=
    source_successfulCAS_often start
  have executionSuccessful :
      (execution.source.event time).IsSuccessfulCAS := by
    simpa [execution] using successful
  exact
    (noSuccess time afterStart executionSuccessful).elim

/-- Pending push demand recurs arbitrarily late in the concrete execution. -/
theorem execution_recurringPushPopDemand :
    execution.RecurringPushPopDemand := by
  simpa [InfiniteRC11Execution.RecurringPushPopDemand,
    execution] using source_pushDemand_often

/--
The final fair-RC11 theorem applies to the concrete coherent infinite
execution, yielding verified finite-prefix linearizability and unbounded
method responses.
-/
theorem execution_linearizableLongRun :
    execution.LinearizableLongRunGuarantees :=
  execution.linearizableLongRun_of_fairness
    execution_recurringPushPopDemand
    execution_threadFair
    execution_memoryFair
    execution_weakCASJustice

end InfiniteWitness

end WeakMemory.TreiberC11V1
