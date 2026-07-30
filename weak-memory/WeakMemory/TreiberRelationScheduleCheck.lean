import WeakMemory.TreiberOrderFromSchedule

namespace WeakMemory.TreiberRC11

/-!
# Executable checking of canonical relation schedules

The checker in this module ranges only over the finite canonical event
carrier.  Reads-before is recognized from the finite `sourceId` function and
`writeOrder`, so no decision procedure for an existential relation over the
ambient event type is required.
-/

namespace RelationScheduleCheck

/-- Generic strict occurrence order used by the executable list routines. -/
private def OccursBefore
    (first second : β)
    (items : List β) : Prop :=
  ∃ earlier between later,
    items = earlier ++ first :: between ++ second :: later

/-- Executable strict occurrence order in a finite list. -/
def before
    [DecidableEq β]
    (first second : β) :
    List β → Bool
  | [] =>
      false
  | item :: rest =>
      (decide (item = first) &&
          rest.any fun later => decide (later = second)) ||
        before first second rest

private theorem logicalBefore_cons_iff
    {first second item : β}
    {rest : List β} :
    OccursBefore first second (item :: rest) ↔
      (item = first ∧ second ∈ rest) ∨
        OccursBefore first second rest := by
  constructor
  · rintro ⟨earlier, between, later, shape⟩
    cases earlier with
    | nil =>
        change
          item :: rest =
            first :: between ++ second :: later
          at shape
        have itemShape := (List.cons.inj shape).1
        have restShape := (List.cons.inj shape).2
        exact Or.inl ⟨itemShape, by
          rw [restShape]
          simp⟩
    | cons headItem remaining =>
        change
          item :: rest =
            headItem ::
              remaining ++ first :: between ++ second :: later
          at shape
        have restShape := (List.cons.inj shape).2
        exact Or.inr
          ⟨remaining, between, later, restShape⟩
  · rintro (⟨rfl, secondMember⟩ | beforeRest)
    · obtain ⟨between, later, restShape⟩ :=
        List.append_of_mem secondMember
      exact ⟨[], between, later, by
        simp [restShape]⟩
    · obtain ⟨earlier, between, later, restShape⟩ :=
        beforeRest
      exact ⟨item :: earlier, between, later, by
        simp [restShape]⟩

/-- Boolean occurrence order is exact. -/
theorem before_eq_true_iff
    [DecidableEq β]
    (first second : β)
    (items : List β) :
    before first second items = true ↔
      OccursBefore first second items := by
  induction items with
  | nil =>
      simp [before, OccursBefore]
  | cons item rest inductionHypothesis =>
      rw [logicalBefore_cons_iff]
      simp [before, List.any_eq_true, inductionHypothesis]

/-- Executable duplicate-freedom for a finite list. -/
def nodup
    [DecidableEq β] :
    List β → Bool
  | [] =>
      true
  | item :: rest =>
      !decide (item ∈ rest) && nodup rest

/-- The finite duplicate check is exact. -/
theorem nodup_eq_true_iff
    [DecidableEq β]
    (items : List β) :
    nodup items = true ↔ items.Nodup := by
  induction items with
  | nil =>
      simp [nodup]
  | cons item rest inductionHypothesis =>
      simp [nodup, inductionHypothesis,
        List.nodup_cons]

/-- Both finite lists have exactly the same members. -/
def covers
    [DecidableEq β]
    (carrier schedule : List β) :
    Bool :=
  (carrier.all fun item => decide (item ∈ schedule)) &&
    (schedule.all fun item => decide (item ∈ carrier))

/-- The finite two-inclusion check is exact coverage. -/
theorem covers_eq_true_iff
    [DecidableEq β]
    (carrier schedule : List β) :
    covers carrier schedule = true ↔
      ∀ item, item ∈ carrier ↔ item ∈ schedule := by
  simp only [covers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨forward, reverse⟩ item
    exact ⟨forward item, reverse item⟩
  · intro same
    exact ⟨fun item member => (same item).mp member,
      fun item member => (same item).mpr member⟩

/--
Check that every selected finite primitive edge occurs in schedule order.
-/
def edgesOrdered
    [DecidableEq β]
    (carrier schedule : List β)
    (edge : β → β → Bool) :
    Bool :=
  carrier.all fun source =>
    carrier.all fun target =>
      if edge source target then
        before source target schedule
      else
        true

/-- A passing pair check orders every selected primitive edge. -/
theorem edgesOrdered_sound
    [DecidableEq β]
    {carrier schedule : List β}
    {edge : β → β → Bool}
    (checked :
      edgesOrdered carrier schedule edge = true)
    {source target : β}
    (sourceMember : source ∈ carrier)
    (targetMember : target ∈ carrier)
    (isEdge : edge source target = true) :
    OccursBefore source target schedule := by
  simp only [edgesOrdered, List.all_eq_true] at checked
  have pairChecked :=
    checked source sourceMember target targetMember
  simp [isEdge, before_eq_true_iff] at pairChecked
  exact pairChecked

/-- Every logically ordered selected edge makes the finite pair check pass. -/
theorem edgesOrdered_complete
    [DecidableEq β]
    {carrier schedule : List β}
    {edge : β → β → Bool}
    (ordered :
      ∀ {source target},
        source ∈ carrier →
        target ∈ carrier →
        edge source target = true →
        OccursBefore source target schedule) :
    edgesOrdered carrier schedule edge = true := by
  simp only [edgesOrdered, List.all_eq_true]
  intro source sourceMember target targetMember
  by_cases isEdge : edge source target = true
  · simp [isEdge, before_eq_true_iff,
      ordered sourceMember targetMember isEdge]
  · have isNotEdge : edge source target = false :=
      Bool.of_not_eq_true isEdge
    simp [isNotEdge]

/-- Finite program-order edge recognition on carrier members. -/
def programOrderEdge
    (source target : Event α) :
    Bool :=
  match source.thread?, target.thread? with
  | some sourceThread, some targetThread =>
      decide (sourceThread = targetThread) &&
        decide (source.id < target.id)
  | _, _ =>
      false

/-- The program-order Boolean recognizes the non-membership part exactly. -/
theorem programOrderEdge_eq_true_iff
    (source target : Event α) :
    programOrderEdge source target = true ↔
      ∃ thread,
        source.thread? = some thread ∧
          target.thread? = some thread ∧
          source.id < target.id := by
  cases sourceThread : source.thread? with
  | none =>
      simp [programOrderEdge, sourceThread]
  | some sourceOwner =>
      cases targetThread : target.thread? with
      | none =>
          simp [programOrderEdge, sourceThread, targetThread]
      | some targetOwner =>
          simp only [programOrderEdge, sourceThread, targetThread,
            decide_eq_true_eq, Bool.and_eq_true]
          constructor
          · rintro ⟨sameOwner, idOrder⟩
            subst targetOwner
            exact ⟨sourceOwner, rfl, rfl, idOrder⟩
          · rintro ⟨thread, sourceShape, targetShape,
                idOrder⟩
            have sourceEquals :
                sourceOwner = thread :=
              Option.some.inj
                sourceShape
            have targetEquals :
                targetOwner = thread :=
              Option.some.inj
                targetShape
            exact ⟨sourceEquals.trans targetEquals.symm,
              idOrder⟩

/-- Executable form of finite identifier order. -/
def idBefore
    (first second : EventId)
    (order : List EventId) :
    Bool :=
  decide (first ∈ order) &&
    decide (second ∈ order) &&
    decide (order.idxOf first < order.idxOf second)

/-- Identifier-order checking is exact. -/
theorem idBefore_eq_true_iff
    (first second : EventId)
    (order : List EventId) :
    idBefore first second order = true ↔
      IdBefore first second order := by
  simp only [idBefore, Bool.and_eq_true,
    decide_eq_true_eq, IdBefore]
  constructor
  · rintro ⟨⟨firstMember, secondMember⟩, orderShape⟩
    exact ⟨firstMember, secondMember, orderShape⟩
  · rintro ⟨firstMember, secondMember, orderShape⟩
    exact ⟨⟨firstMember, secondMember⟩, orderShape⟩

/-- Finite reads-from edge recognition for canonical relation data. -/
def readsFromEdge
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (source target : Event α) :
    Bool :=
  decide (data.sourceId target.id = some source.id)

/-- Finite modification-order edge recognition. -/
def modificationOrderEdge
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (source target : Event α) :
    Bool :=
  idBefore source.id target.id data.writeOrder

/--
Finite reads-before recognition.

The selected source identifier and the finite write order replace the
existential source event in `Graph.ReadsBefore`.
-/
def readsBeforeEdge
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (read laterWrite : Event α) :
    Bool :=
  match data.sourceId read.id with
  | none =>
      false
  | some sourceId =>
      idBefore sourceId laterWrite.id data.writeOrder &&
        decide (read ≠ laterWrite)

/-- On carrier members, finite reads-before recognition is exact. -/
theorem readsBeforeEdge_eq_true_iff
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {read laterWrite : Event α}
    (readMember : read ∈ skeleton.events)
    (laterMember : laterWrite ∈ skeleton.events) :
    readsBeforeEdge data read laterWrite = true ↔
      data.graph.ReadsBefore read laterWrite := by
  constructor
  · intro checked
    cases readSource : data.sourceId read.id with
    | none =>
        simp [readsBeforeEdge, readSource] at checked
    | some sourceId =>
        have checkedParts :
            IdBefore sourceId laterWrite.id data.writeOrder ∧
              read ≠ laterWrite := by
          simpa [readsBeforeEdge, readSource,
            idBefore_eq_true_iff] using checked
        have sourceDescription :=
          data.sourceSpec read readMember
        cases readShape : read.readValue with
        | none =>
            rw [readShape] at sourceDescription
            rw [sourceDescription] at readSource
            contradiction
        | some value =>
            rw [readShape] at sourceDescription
            obtain ⟨source, sourceMember, sourceWrites,
                chosenSource⟩ :=
              sourceDescription
            have sourceIdShape :
                source.id = sourceId :=
              Option.some.inj
                (chosenSource.symm.trans readSource)
            refine ⟨source, ?_, ?_, checkedParts.2⟩
            · change data.readsFrom source read
              exact ⟨sourceMember, readMember, chosenSource⟩
            · change data.modificationOrder source laterWrite
              exact ⟨sourceMember, laterMember, by
                simpa [sourceIdShape] using checkedParts.1⟩
  · rintro ⟨source, readsFrom, modificationOrder,
        different⟩
    change data.readsFrom source read at readsFrom
    change data.modificationOrder source laterWrite at modificationOrder
    simp [readsBeforeEdge, readsFrom.2.2,
      modificationOrder.2.2, different,
      idBefore_eq_true_iff]

/-- An inductive presentation of strict finite occurrence order. -/
private inductive ListPrecedes
    (first second : β) :
    List β → Prop where
  | head {rest : List β} :
      second ∈ rest →
      ListPrecedes first second (first :: rest)
  | tail {item : β} {rest : List β} :
      ListPrecedes first second rest →
      ListPrecedes first second (item :: rest)

namespace ListPrecedes

private theorem second_mem
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    second ∈ items := by
  induction precedes with
  | head member =>
      exact List.mem_cons_of_mem _ member
  | tail _ inductionHypothesis =>
      exact List.mem_cons_of_mem _ inductionHypothesis

private theorem ofOccursBefore
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items) :
    ListPrecedes first second items := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  induction earlier with
  | nil =>
      apply ListPrecedes.head
      simp
  | cons item rest inductionHypothesis =>
      exact ListPrecedes.tail inductionHypothesis

private theorem toOccursBefore
    {first second : β}
    {items : List β}
    (precedes : ListPrecedes first second items) :
    OccursBefore first second items := by
  induction precedes with
  | @head rest member =>
      obtain ⟨between, later, shape⟩ :=
        List.append_of_mem member
      exact ⟨[], between, later, by simp [shape]⟩
  | @tail item rest later inductionHypothesis =>
      obtain ⟨earlier, between, trailing, shape⟩ :=
        inductionHypothesis
      exact ⟨item :: earlier, between, trailing, by
        simp [shape]⟩

/-- Strict occurrence order is transitive in a duplicate-free list. -/
private theorem trans
    {first middle last : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (firstBeforeMiddle :
      ListPrecedes first middle items)
    (middleBeforeLast :
      ListPrecedes middle last items) :
    ListPrecedes first last items := by
  induction firstBeforeMiddle with
  | @head rest middleMember =>
      cases middleBeforeLast with
      | head lastMember =>
          exact ListPrecedes.head lastMember
      | tail later =>
          exact ListPrecedes.head later.second_mem
  | @tail item rest earlier inductionHypothesis =>
      cases middleBeforeLast with
      | head lastMember =>
          exact
            ((List.nodup_cons.mp noDuplicates).1
              earlier.second_mem).elim
      | tail later =>
          exact ListPrecedes.tail
            (inductionHypothesis
              (List.nodup_cons.mp noDuplicates).2 later)

end ListPrecedes

/-- Decomposition-based schedule order is transitively composable. -/
private theorem logicalBefore_trans
    {first middle last : Event α}
    {schedule : List (Event α)}
    (noDuplicates : schedule.Nodup)
    (firstBeforeMiddle : Before first middle schedule)
    (middleBeforeLast : Before middle last schedule) :
    Before first last schedule := by
  change OccursBefore first middle schedule at firstBeforeMiddle
  change OccursBefore middle last schedule at middleBeforeLast
  change OccursBefore first last schedule
  exact
    (ListPrecedes.ofOccursBefore firstBeforeMiddle
      |>.trans noDuplicates
        (ListPrecedes.ofOccursBefore
          middleBeforeLast)).toOccursBefore

/--
Finite primitive-edge certificate for one canonical relation schedule.

Extended coherence is intentionally absent: it is derived below from these
three primitive relations and reads-before.
-/
structure PrimitiveEdgeScheduleCertificate
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (schedule : List (Event α)) : Prop where
  covers :
    ∀ event,
      event ∈ data.graph.events ↔ event ∈ schedule
  noDuplicates :
    schedule.Nodup
  programOrder :
    ∀ {source target},
      data.graph.programOrder source target →
      Before source target schedule
  readsFrom :
    ∀ {source target},
      data.graph.readsFrom source target →
      Before source target schedule
  modificationOrder :
    ∀ {source target},
      data.graph.modificationOrder source target →
      Before source target schedule
  readsBefore :
    ∀ {source target},
      data.graph.ReadsBefore source target →
      Before source target schedule

namespace PrimitiveEdgeScheduleCertificate

/-- Primitive-edge order induces order for the full extended coherence. -/
theorem extendedCoherence
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (certificate :
      PrimitiveEdgeScheduleCertificate data schedule)
    {source target : Event α}
    (edge :
      data.graph.ExtendedCoherence source target) :
    Before source target schedule := by
  induction edge with
  | readsFrom primitive =>
      exact certificate.readsFrom primitive
  | modificationOrder primitive =>
      exact certificate.modificationOrder primitive
  | readsBefore primitive =>
      exact certificate.readsBefore primitive
  | transitive first second firstBefore secondBefore =>
      exact logicalBefore_trans certificate.noDuplicates
        firstBefore secondBefore

/-- Forget the primitive presentation and obtain the standard schedule proof. -/
theorem toRespectsGraph
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (certificate :
      PrimitiveEdgeScheduleCertificate data schedule) :
    RespectsGraph data.graph schedule where
  covers :=
    certificate.covers
  noDuplicates :=
    certificate.noDuplicates
  programOrder edge :=
    certificate.programOrder edge
  extendedCoherence edge :=
    certificate.extendedCoherence edge

end PrimitiveEdgeScheduleCertificate

/-- Execute every finite primitive schedule check. -/
def check
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (schedule : List (Event α)) :
    Bool :=
  covers skeleton.events schedule &&
    (nodup schedule &&
      (edgesOrdered skeleton.events schedule programOrderEdge &&
        (edgesOrdered skeleton.events schedule
            (readsFromEdge data) &&
          (edgesOrdered skeleton.events schedule
              (modificationOrderEdge data) &&
            edgesOrdered skeleton.events schedule
              (readsBeforeEdge data)))))

/-- A passing finite checker constructs the primitive schedule certificate. -/
theorem check_sound_primitive
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (checked : check data schedule = true) :
    PrimitiveEdgeScheduleCertificate data schedule := by
  simp only [check, Bool.and_eq_true] at checked
  rcases checked with ⟨coverageChecked, duplicateChecked,
    programOrderChecked, readsFromChecked,
    modificationOrderChecked, readsBeforeChecked⟩
  refine {
    covers := ?_
    noDuplicates := ?_
    programOrder := ?_
    readsFrom := ?_
    modificationOrder := ?_
    readsBefore := ?_
  }
  · simpa using
      (covers_eq_true_iff skeleton.events schedule).mp
        coverageChecked
  · exact (nodup_eq_true_iff schedule).mp
      duplicateChecked
  · intro source target edge
    change skeleton.programOrder source target at edge
    change OccursBefore source target schedule
    exact edgesOrdered_sound programOrderChecked
      edge.1 edge.2.1
      ((programOrderEdge_eq_true_iff source target).mpr
        edge.2.2)
  · intro source target edge
    change data.readsFrom source target at edge
    change OccursBefore source target schedule
    exact edgesOrdered_sound readsFromChecked
      edge.1 edge.2.1
      (by simp [readsFromEdge, edge.2.2])
  · intro source target edge
    change data.modificationOrder source target at edge
    change OccursBefore source target schedule
    exact edgesOrdered_sound modificationOrderChecked
      edge.1 edge.2.1
      ((idBefore_eq_true_iff
        source.id target.id data.writeOrder).mpr
          edge.2.2)
  · intro read laterWrite edge
    obtain ⟨source, readsFrom, modificationOrder,
        different⟩ := edge
    have readMember : read ∈ skeleton.events := by
      change data.readsFrom source read at readsFrom
      exact readsFrom.2.1
    have laterMember : laterWrite ∈ skeleton.events := by
      change data.modificationOrder source laterWrite at modificationOrder
      exact modificationOrder.2.1
    change OccursBefore read laterWrite schedule
    apply edgesOrdered_sound readsBeforeChecked
      readMember laterMember
    apply (readsBeforeEdge_eq_true_iff data
      readMember laterMember).mpr
    exact ⟨source, readsFrom, modificationOrder,
      different⟩

/-- Checker soundness for the standard graph-respecting schedule predicate. -/
theorem check_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (checked : check data schedule = true) :
    RespectsGraph data.graph schedule :=
  (check_sound_primitive checked).toRespectsGraph

/-- Every primitive certificate makes all finite Boolean checks pass. -/
theorem check_complete_primitive
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (certificate :
      PrimitiveEdgeScheduleCertificate data schedule) :
    check data schedule = true := by
  have coverageChecked :
      covers skeleton.events schedule = true :=
    (covers_eq_true_iff skeleton.events schedule).mpr
      certificate.covers
  have duplicateChecked :
      nodup schedule = true :=
    (nodup_eq_true_iff schedule).mpr
      certificate.noDuplicates
  have programOrderChecked :
      edgesOrdered skeleton.events schedule
        programOrderEdge = true := by
    apply edgesOrdered_complete
    intro source target sourceMember targetMember
        selected
    have description :=
      (programOrderEdge_eq_true_iff source target).mp
        selected
    have edge :
        data.graph.programOrder source target := by
      change skeleton.programOrder source target
      exact ⟨sourceMember, targetMember, description⟩
    change OccursBefore source target schedule
    exact certificate.programOrder edge
  have readsFromChecked :
      edgesOrdered skeleton.events schedule
        (readsFromEdge data) = true := by
    apply edgesOrdered_complete
    intro source target sourceMember targetMember
        selected
    have sourceShape :
        data.sourceId target.id = some source.id := by
      simpa [readsFromEdge] using selected
    have edge : data.graph.readsFrom source target := by
      change data.readsFrom source target
      exact ⟨sourceMember, targetMember, sourceShape⟩
    change OccursBefore source target schedule
    exact certificate.readsFrom edge
  have modificationOrderChecked :
      edgesOrdered skeleton.events schedule
        (modificationOrderEdge data) = true := by
    apply edgesOrdered_complete
    intro source target sourceMember targetMember
        selected
    have idOrder :
        IdBefore source.id target.id data.writeOrder :=
      (idBefore_eq_true_iff
        source.id target.id data.writeOrder).mp selected
    have edge :
        data.graph.modificationOrder source target := by
      change data.modificationOrder source target
      exact ⟨sourceMember, targetMember, idOrder⟩
    change OccursBefore source target schedule
    exact certificate.modificationOrder edge
  have readsBeforeChecked :
      edgesOrdered skeleton.events schedule
        (readsBeforeEdge data) = true := by
    apply edgesOrdered_complete
    intro read laterWrite readMember laterMember
        selected
    have edge : data.graph.ReadsBefore read laterWrite :=
      (readsBeforeEdge_eq_true_iff data
        readMember laterMember).mp selected
    change OccursBefore read laterWrite schedule
    exact certificate.readsBefore edge
  simp only [check, Bool.and_eq_true]
  exact ⟨coverageChecked, duplicateChecked,
    programOrderChecked, readsFromChecked,
    modificationOrderChecked, readsBeforeChecked⟩

/-- The finite checker is exact for primitive-edge schedule certificates. -/
theorem check_eq_true_iff_primitive
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (schedule : List (Event α)) :
    check data schedule = true ↔
      PrimitiveEdgeScheduleCertificate data schedule :=
  ⟨check_sound_primitive, check_complete_primitive⟩

/-- A standard respecting schedule contains the primitive certificate. -/
theorem primitive_of_respectsGraph
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    {schedule : List (Event α)}
    (respects : RespectsGraph data.graph schedule) :
    PrimitiveEdgeScheduleCertificate data schedule where
  covers :=
    respects.covers
  noDuplicates :=
    respects.noDuplicates
  programOrder edge :=
    respects.programOrder edge
  readsFrom edge :=
    respects.extendedCoherence
      (.readsFrom edge)
  modificationOrder edge :=
    respects.extendedCoherence
      (.modificationOrder edge)
  readsBefore edge :=
    respects.extendedCoherence
      (.readsBefore edge)

/-- The finite checker is exact for the standard graph schedule predicate. -/
theorem check_eq_true_iff
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (schedule : List (Event α)) :
    check data schedule = true ↔
      RespectsGraph data.graph schedule := by
  constructor
  · exact check_sound
  · intro respects
    exact check_complete_primitive
      (primitive_of_respectsGraph respects)

/--
Executable decidability of canonical graph-schedule validity, obtained only
from the finite carrier checker.
-/
def decideRespectsGraph
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (schedule : List (Event α)) :
    Decidable (RespectsGraph data.graph schedule) :=
  if checked : check data schedule = true then
    isTrue ((check_eq_true_iff data schedule).mp checked)
  else
    isFalse fun respects =>
      checked ((check_eq_true_iff data schedule).mpr respects)

end RelationScheduleCheck

end WeakMemory.TreiberRC11
