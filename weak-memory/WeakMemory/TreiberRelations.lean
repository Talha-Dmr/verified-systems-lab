import WeakMemory.TreiberGeneratedConsistency

namespace WeakMemory.TreiberRC11

/-!
# Constructing reads-from and modification order

This module represents the two single-location atomic relations by finite,
proof-carrying data:

* `writeTail` lists every non-initial write in modification order;
* `sourceId` chooses one write identifier for every read;
* successful RMW events certify that their chosen source is adjacent in the
  modification order.

The logical initializer has identifier zero and is placed at the front of the
write order by definition.  The resulting graph uses the carrier and program
order already constructed by `EventGraph.Skeleton`.  All eleven fields of
`RemainingWellFormedRelations` are then theorems of this representation.

RC11 coherence is intentionally not addressed here.  It requires a separate
consistency certificate for the relations constructed below.
-/

/--
Strict occurrence order for two identifiers in a finite duplicate-free list.

Membership is included in the definition so relation closure is available
without separate lookup assumptions.
-/
def IdBefore
    (first second : EventId)
    (order : List EventId) : Prop :=
  first ∈ order ∧
    second ∈ order ∧
    order.idxOf first < order.idxOf second

namespace IdBefore

theorem first_mem
    {first second : EventId}
    {order : List EventId}
    (before : IdBefore first second order) :
    first ∈ order :=
  before.1

theorem second_mem
    {first second : EventId}
    {order : List EventId}
    (before : IdBefore first second order) :
    second ∈ order :=
  before.2.1

theorem irreflexive
    (eventId : EventId)
    (order : List EventId) :
    ¬ IdBefore eventId eventId order := by
  intro before
  exact (Nat.lt_irrefl (order.idxOf eventId)) before.2.2

theorem transitive
    {first middle last : EventId}
    {order : List EventId}
    (firstBefore : IdBefore first middle order)
    (secondBefore : IdBefore middle last order) :
    IdBefore first last order :=
  ⟨firstBefore.1, secondBefore.2.1,
    Nat.lt_trans firstBefore.2.2 secondBefore.2.2⟩

/-- The head of a list precedes every different member of its tail. -/
theorem head
    {head later : EventId}
    {tail : List EventId}
    (different : head ≠ later)
    (member : later ∈ tail) :
    IdBefore head later (head :: tail) := by
  refine ⟨by simp, by simp [member], ?_⟩
  simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
    if_neg different]
  exact Nat.zero_lt_succ _

/-- A strict order in a tail is preserved when a fresh head is added. -/
theorem cons
    {first second head : EventId}
    {tail : List EventId}
    (headFresh : head ∉ tail)
    (before : IdBefore first second tail) :
    IdBefore first second (head :: tail) := by
  have headNeFirst : head ≠ first := by
    intro same
    subst first
    exact headFresh before.first_mem
  have headNeSecond : head ≠ second := by
    intro same
    subst second
    exact headFresh before.second_mem
  simp only [IdBefore, List.mem_cons]
  refine ⟨Or.inr before.first_mem, Or.inr before.second_mem, ?_⟩
  simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
    if_neg headNeFirst, if_neg headNeSecond]
  exact Nat.add_lt_add_right before.2.2 1

/-- Distinct members of a duplicate-free list are strictly comparable. -/
theorem total
    {first second : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (firstMember : first ∈ order)
    (secondMember : second ∈ order)
    (different : first ≠ second) :
    IdBefore first second order ∨
      IdBefore second first order := by
  induction order with
  | nil =>
      simp at firstMember
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp noDuplicates).1
      have tailNodup := (List.nodup_cons.mp noDuplicates).2
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with firstIsHead | firstInTail
      · subst first
        rcases secondMember with secondIsHead | secondInTail
        · exact (different secondIsHead.symm).elim
        · exact Or.inl (IdBefore.head different secondInTail)
      · rcases secondMember with secondIsHead | secondInTail
        · subst second
          exact Or.inr
            (IdBefore.head (Ne.symm different) firstInTail)
        · rcases inductionHypothesis tailNodup
              firstInTail secondInTail with
            firstBefore | secondBefore
          · exact Or.inl (IdBefore.cons headFresh firstBefore)
          · exact Or.inr (IdBefore.cons headFresh secondBefore)

end IdBefore

/--
Two identifiers are adjacent when the first precedes the second and no
identifier occurs strictly between them.
-/
def IdAdjacent
    (first second : EventId)
    (order : List EventId) : Prop :=
  IdBefore first second order ∧
    ∀ middle,
      ¬ (IdBefore first middle order ∧
        IdBefore middle second order)

namespace IdAdjacent

theorem before
    {first second : EventId}
    {order : List EventId}
    (adjacent : IdAdjacent first second order) :
    IdBefore first second order :=
  adjacent.1

theorem noBetween
    {first second middle : EventId}
    {order : List EventId}
    (adjacent : IdAdjacent first second order) :
    ¬ (IdBefore first middle order ∧
      IdBefore middle second order) :=
  adjacent.2 middle

end IdAdjacent

/--
Finite relation data for the atomic head location of one source skeleton.

`sourceSpec` is total exactly at graph reads and simultaneously enforces value
agreement.  Event identifiers are used as the external representation;
injectivity on the skeleton carrier turns the identifier map into functional
reads-from.
-/
structure AtomicRelationData
    (skeleton : EventGraph.Skeleton α) where
  /-- Every non-initial write identifier, in modification order. -/
  writeTail : List EventId
  writeTailNodup :
    writeTail.Nodup
  writeTailExact :
    ∀ eventId,
      eventId ∈ writeTail ↔
        ∃ event,
          event ∈ skeleton.events ∧
          event.id = eventId ∧
          event.IsWrite ∧
          ¬ event.IsInitial
  /-- The chosen reads-from source identifier for each target identifier. -/
  sourceId :
    EventId → Option EventId
  sourceSpec :
    ∀ target,
      target ∈ skeleton.events →
      match target.readValue with
      | none =>
          sourceId target.id = none
      | some value =>
          ∃ source,
            source ∈ skeleton.events ∧
              source.writtenValue = some value ∧
              sourceId target.id = some source.id
  /-- Every successful RMW reads the immediately preceding modification. -/
  rmwAdjacent :
    ∀ {source rmw},
      source ∈ skeleton.events →
      rmw ∈ skeleton.events →
      sourceId rmw.id = some source.id →
      rmw.IsRMW →
      IdAdjacent source.id rmw.id (0 :: writeTail)

namespace AtomicRelationData

/-- Initializer identifier followed by all non-initial writes. -/
def writeOrder
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    List EventId :=
  0 :: data.writeTail

/-- The membership-guarded graph of the read-source function. -/
def readsFrom
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    Relation (Event α) :=
  fun source target =>
    source ∈ skeleton.events ∧
      target ∈ skeleton.events ∧
      data.sourceId target.id = some source.id

/-- Strict list order on the exact finite write carrier. -/
def modificationOrder
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    Relation (Event α) :=
  fun source target =>
    source ∈ skeleton.events ∧
      target ∈ skeleton.events ∧
      IdBefore source.id target.id data.writeOrder

/-- The canonical graph determined by one relation-data certificate. -/
def graph
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    Graph α :=
  skeleton.toGraph data.readsFrom data.modificationOrder

@[simp] theorem graph_events
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    data.graph.events = skeleton.events :=
  rfl

@[simp] theorem graph_programOrder
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    data.graph.programOrder = skeleton.programOrder :=
  rfl

@[simp] theorem graph_readsFrom
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    data.graph.readsFrom = data.readsFrom :=
  rfl

@[simp] theorem graph_modificationOrder
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    data.graph.modificationOrder = data.modificationOrder :=
  rfl

/-- Identifier zero cannot occur among the non-initial writes. -/
theorem zero_not_mem_writeTail
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    0 ∉ data.writeTail := by
  intro zeroMember
  obtain ⟨event, eventMember, eventId, _, notInitial⟩ :=
    (data.writeTailExact 0).mp zeroMember
  have sameEvent :
      event =
        (EventGraph.Skeleton.initialEvent : Event α) :=
    skeleton.uniqueIds
      eventMember
      (by simp [EventGraph.Skeleton.events])
      (by simpa [EventGraph.Skeleton.initialEvent] using eventId)
  apply notInitial
  rw [sameEvent]
  trivial

/-- The complete modification-order carrier has no duplicate identifiers. -/
theorem writeOrderNodup
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    data.writeOrder.Nodup := by
  exact List.nodup_cons.mpr
    ⟨data.zero_not_mem_writeTail, data.writeTailNodup⟩

/-- Any initial member of a skeleton is its reserved identifier-zero event. -/
theorem initial_eq_initialEvent
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    {event : Event α}
    (eventMember : event ∈ skeleton.events)
    (isInitial : event.IsInitial) :
    event =
      (EventGraph.Skeleton.initialEvent : Event α) := by
  obtain ⟨chosen, chosenMember, chosenInitial, unique⟩ :=
    skeleton.initialExistsUnique
  have eventIsChosen :=
    unique event eventMember isInitial
  have reservedIsChosen :=
    unique
      (EventGraph.Skeleton.initialEvent : Event α)
      (by simp [EventGraph.Skeleton.events])
      (by trivial)
  exact eventIsChosen.trans reservedIsChosen.symm

/-- Every skeleton event whose identifier occurs in the write order writes. -/
theorem isWrite_of_id_mem_writeOrder
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {event : Event α}
    (eventMember : event ∈ skeleton.events)
    (idMember : event.id ∈ data.writeOrder) :
    event.IsWrite := by
  change event.id ∈ 0 :: data.writeTail at idMember
  simp only [List.mem_cons] at idMember
  rcases idMember with eventIdZero | inTail
  · have sameEvent :
        event =
          (EventGraph.Skeleton.initialEvent : Event α) :=
      skeleton.uniqueIds
        eventMember
        (by simp [EventGraph.Skeleton.events])
        (by simpa [EventGraph.Skeleton.initialEvent] using
          eventIdZero)
    subst event
    exact ⟨none, rfl⟩
  · obtain ⟨write, writeMember, writeId, writeWrites, _⟩ :=
      (data.writeTailExact event.id).mp inTail
    have sameEvent : event = write :=
      skeleton.uniqueIds eventMember writeMember writeId.symm
    simpa [sameEvent] using writeWrites

/-- Every write in the skeleton occurs in the constructed write order. -/
theorem id_mem_writeOrder_of_isWrite
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {event : Event α}
    (eventMember : event ∈ skeleton.events)
    (isWrite : event.IsWrite) :
    event.id ∈ data.writeOrder := by
  by_cases isInitial : event.IsInitial
  · have sameEvent :=
      initial_eq_initialEvent eventMember isInitial
    subst event
    simp [writeOrder, EventGraph.Skeleton.initialEvent]
  · have inTail : event.id ∈ data.writeTail :=
      (data.writeTailExact event.id).mpr
        ⟨event, eventMember, rfl, isWrite, isInitial⟩
    simp [writeOrder, inTail]

/-- Constructed reads-from edges are closed over the canonical carrier. -/
theorem readsFromClosed
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.readsFrom source target) :
    source ∈ data.graph.events ∧
      target ∈ data.graph.events := by
  change data.readsFrom source target at edge
  exact ⟨edge.1, edge.2.1⟩

/-- Constructed modification-order edges are closed over the carrier. -/
theorem modificationOrderClosed
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.modificationOrder source target) :
    source ∈ data.graph.events ∧
      target ∈ data.graph.events := by
  change data.modificationOrder source target at edge
  exact ⟨edge.1, edge.2.1⟩

/-- The read-source specification gives equal written and observed values. -/
theorem readsFromValues
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.readsFrom source target) :
    ∃ value,
      source.writtenValue = some value ∧
        target.readValue = some value := by
  change data.readsFrom source target at edge
  obtain ⟨sourceMember, targetMember, chosenSource⟩ := edge
  have sourceDescription :=
    data.sourceSpec target targetMember
  cases readShape : target.readValue with
  | none =>
      rw [readShape] at sourceDescription
      rw [sourceDescription] at chosenSource
      contradiction
  | some value =>
      rw [readShape] at sourceDescription
      obtain ⟨actual, actualMember, actualWrites, actualChosen⟩ :=
        sourceDescription
      have sameId : source.id = actual.id :=
        Option.some.inj
          (chosenSource.symm.trans actualChosen)
      have sameSource : source = actual :=
        skeleton.uniqueIds sourceMember actualMember sameId
      exact ⟨value,
        by simpa [sameSource] using actualWrites,
        rfl⟩

/-- A function on target identifiers makes constructed reads-from functional. -/
theorem readsFromFunctional
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {firstSource secondSource target : Event α}
    (firstEdge :
      data.graph.readsFrom firstSource target)
    (secondEdge :
      data.graph.readsFrom secondSource target) :
    firstSource = secondSource := by
  change data.readsFrom firstSource target at firstEdge
  change data.readsFrom secondSource target at secondEdge
  have sameId : firstSource.id = secondSource.id :=
    Option.some.inj
      (firstEdge.2.2.symm.trans secondEdge.2.2)
  exact skeleton.uniqueIds
    firstEdge.1 secondEdge.1 sameId

/-- Every read receives the source selected by `sourceSpec`. -/
theorem everyReadHasSource
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {target : Event α}
    (targetMember : target ∈ data.graph.events)
    (targetReads : target.IsRead) :
    ∃ source,
      data.graph.readsFrom source target := by
  obtain ⟨value, readShape⟩ := targetReads
  have sourceDescription :=
    data.sourceSpec target targetMember
  rw [readShape] at sourceDescription
  obtain ⟨source, sourceMember, _, chosenSource⟩ :=
    sourceDescription
  refine ⟨source, ?_⟩
  change data.readsFrom source target
  exact ⟨sourceMember, targetMember, chosenSource⟩

/-- Constructed modification order only relates writes. -/
theorem modificationOrderWrites
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.modificationOrder source target) :
    source.IsWrite ∧ target.IsWrite := by
  change data.modificationOrder source target at edge
  exact ⟨
    data.isWrite_of_id_mem_writeOrder
      edge.1 edge.2.2.first_mem,
    data.isWrite_of_id_mem_writeOrder
      edge.2.1 edge.2.2.second_mem⟩

/-- Strict identifier order makes modification order irreflexive. -/
theorem modificationOrderIrreflexive
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (event : Event α) :
    ¬ data.graph.modificationOrder event event := by
  intro edge
  change data.modificationOrder event event at edge
  exact IdBefore.irreflexive event.id data.writeOrder
    edge.2.2

/-- Strict identifier order makes modification order transitive. -/
theorem modificationOrderTransitive
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {first middle last : Event α}
    (firstEdge :
      data.graph.modificationOrder first middle)
    (secondEdge :
      data.graph.modificationOrder middle last) :
    data.graph.modificationOrder first last := by
  change data.modificationOrder first middle at firstEdge
  change data.modificationOrder middle last at secondEdge
  change data.modificationOrder first last
  exact ⟨firstEdge.1, secondEdge.2.1,
    IdBefore.transitive firstEdge.2.2 secondEdge.2.2⟩

/-- The exact duplicate-free write list gives a total order on writes. -/
theorem modificationOrderTotal
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {left right : Event α}
    (leftMember : left ∈ data.graph.events)
    (rightMember : right ∈ data.graph.events)
    (leftWrites : left.IsWrite)
    (rightWrites : right.IsWrite)
    (different : left ≠ right) :
    data.graph.modificationOrder left right ∨
      data.graph.modificationOrder right left := by
  have leftIdMember :
      left.id ∈ data.writeOrder :=
    data.id_mem_writeOrder_of_isWrite
      leftMember leftWrites
  have rightIdMember :
      right.id ∈ data.writeOrder :=
    data.id_mem_writeOrder_of_isWrite
      rightMember rightWrites
  have differentIds : left.id ≠ right.id := by
    intro sameId
    exact different
      (skeleton.uniqueIds
        leftMember rightMember sameId)
  rcases IdBefore.total data.writeOrderNodup
      leftIdMember rightIdMember differentIds with
    leftBefore | rightBefore
  · exact Or.inl ⟨leftMember, rightMember, leftBefore⟩
  · exact Or.inr ⟨rightMember, leftMember, rightBefore⟩

/-- The reserved initializer is definitionally first in modification order. -/
theorem initialPrecedesWrites
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {initial write : Event α}
    (initialMember : initial ∈ data.graph.events)
    (isInitial : initial.IsInitial)
    (writeMember : write ∈ data.graph.events)
    (writeWrites : write.IsWrite)
    (writeNotInitial : ¬ write.IsInitial) :
    data.graph.modificationOrder initial write := by
  have initialShape :=
    initial_eq_initialEvent initialMember isInitial
  have writeInTail : write.id ∈ data.writeTail :=
    (data.writeTailExact write.id).mpr
      ⟨write, writeMember, rfl,
        writeWrites, writeNotInitial⟩
  have differentId : (0 : EventId) ≠ write.id := by
    intro writeIdZero
    have writeShape :
        write =
          (EventGraph.Skeleton.initialEvent : Event α) :=
      skeleton.uniqueIds
        writeMember
        (by simp [EventGraph.Skeleton.events])
        (by simpa [EventGraph.Skeleton.initialEvent] using
          writeIdZero.symm)
    apply writeNotInitial
    rw [writeShape]
    trivial
  change data.modificationOrder initial write
  refine ⟨initialMember, writeMember, ?_⟩
  rw [initialShape]
  exact IdBefore.head differentId writeInTail

/--
The adjacency certificate makes every successful RMW read its immediate
modification-order predecessor.
-/
theorem rmwReadsImmediatePredecessor
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source rmw : Event α}
    (readsFrom : data.graph.readsFrom source rmw)
    (isRMW : rmw.IsRMW) :
    data.graph.modificationOrder source rmw ∧
      ∀ middle,
        middle ∈ data.graph.events →
        middle.IsWrite →
        ¬ (data.graph.modificationOrder source middle ∧
          data.graph.modificationOrder middle rmw) := by
  change data.readsFrom source rmw at readsFrom
  have adjacent :
      IdAdjacent source.id rmw.id data.writeOrder := by
    exact data.rmwAdjacent
      readsFrom.1 readsFrom.2.1
      readsFrom.2.2 isRMW
  constructor
  · exact ⟨readsFrom.1, readsFrom.2.1,
      adjacent.before⟩
  · intro middle middleMember middleWrites
    rintro ⟨sourceBeforeMiddle, middleBeforeRmw⟩
    change data.modificationOrder source middle at sourceBeforeMiddle
    change data.modificationOrder middle rmw at middleBeforeRmw
    exact adjacent.noBetween
      ⟨sourceBeforeMiddle.2.2,
        middleBeforeRmw.2.2⟩

/-- Bundle all eleven relation fields derived from the finite representation. -/
theorem toRemainingWellFormedRelations
    {α : Type}
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    RemainingWellFormedRelations data.graph where
  readsFromClosed edge :=
    data.readsFromClosed edge
  modificationOrderClosed edge :=
    data.modificationOrderClosed edge
  readsFromValues edge :=
    data.readsFromValues edge
  readsFromFunctional firstEdge secondEdge :=
    data.readsFromFunctional firstEdge secondEdge
  everyReadHasSource targetMember targetReads :=
    data.everyReadHasSource targetMember targetReads
  modificationOrderWrites edge :=
    data.modificationOrderWrites edge
  modificationOrderIrreflexive event :=
    data.modificationOrderIrreflexive event
  modificationOrderTransitive firstEdge secondEdge :=
    data.modificationOrderTransitive firstEdge secondEdge
  modificationOrderTotal leftMember rightMember
      leftWrites rightWrites different :=
    data.modificationOrderTotal
      leftMember rightMember leftWrites rightWrites different
  initialPrecedesWrites initialMember isInitial
      writeMember writeWrites writeNotInitial :=
    data.initialPrecedesWrites
      initialMember isInitial writeMember
      writeWrites writeNotInitial
  rmwReadsImmediatePredecessor readsFrom isRMW :=
    data.rmwReadsImmediatePredecessor readsFrom isRMW

end AtomicRelationData

end WeakMemory.TreiberRC11
