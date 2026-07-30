import WeakMemory.TreiberC11V1RC11
import WeakMemory.TreiberC11V1SourceFrontend
import WeakMemory.TreiberRelationDataCheck
import WeakMemory.TreiberRelationScheduleCheck

namespace WeakMemory.TreiberC11V1.RelationFrontend

/-!
# Relation refinement for the independent Treiber C11-v1 semantics

This module is the bounded relation bridge between the independent
`TreiberC11V1.RC11` carrier and the existing checked single-head relation
representation.  The generic `Projection` contract contains only carrier and
accessor preservation facts.  It does not assume validator acceptance.

A source-frontend-specific module can instantiate `Projection` for its
projected `EventGraph.Skeleton`; all RF/MO construction, serialization,
checker acceptance, schedule checking, and consistency results below then
follow without adding a trust assumption.
-/

namespace Independent

abbrev Atom := RC11.Atom
abbrev Candidate := RC11.Candidate

end Independent

/-- Encode the independent source pointer as the target graph pointer value. -/
def pointerValue : Ptr → Option TreiberRA.NodeId
  | .null => none
  | .node node => some node

/-- The independent and target finite source lookups have identical data semantics. -/
theorem sourceFor_eq_target
    (entries : List (EventId × EventId)) :
    RC11.sourceFor entries =
      TreiberRC11.RelationDataCheck.sourceFor entries := by
  funext target
  induction entries with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨candidateTarget, candidateSource⟩
      simp only [RC11.sourceFor,
        TreiberRC11.RelationDataCheck.sourceFor]
      by_cases same : candidateTarget = target
      · simp [same]
      · simp [same, inductionHypothesis]

private def AtomBefore
    (first second : RC11.Atom α)
    (schedule : List (RC11.Atom α)) : Prop :=
  ∃ earlier between later,
    schedule =
      earlier ++ first :: between ++ second :: later

private theorem atomBefore_of_idBefore
    {schedule : List (RC11.Atom α)}
    {source target : RC11.Atom α}
    (idsNodup :
      (schedule.map RC11.Atom.id).Nodup)
    (sourceMember : source ∈ schedule)
    (targetMember : target ∈ schedule)
    (ordered :
      RC11.IdBefore source.id target.id
        (schedule.map RC11.Atom.id)) :
    AtomBefore source target schedule := by
  induction schedule with
  | nil =>
      simp at sourceMember
  | cons head tail inductionHypothesis =>
      have uniqueParts :=
        List.nodup_cons.mp idsNodup
      simp only [List.mem_cons] at sourceMember targetMember
      rcases sourceMember with sourceIsHead | sourceInTail
      · subst source
        rcases targetMember with targetIsHead | targetInTail
        · subst target
          exact (Nat.lt_irrefl _ ordered.2.2).elim
        · obtain ⟨between, later, tailShape⟩ :=
            List.append_of_mem targetInTail
          exact ⟨[], between, later, by
            simp [tailShape]⟩
      · rcases targetMember with targetIsHead | targetInTail
        · subst target
          have headNeSource :
              head.id ≠ source.id := by
            intro same
            apply uniqueParts.1
            exact List.mem_map.mpr
              ⟨source, sourceInTail, same.symm⟩
          have headBeqSource :
              (head.id == source.id) = false :=
            beq_eq_false_iff_ne.mpr headNeSource
          have impossible : False := by
            have orderShape := ordered.2.2
            simp [List.idxOf_cons, headBeqSource] at orderShape
          exact impossible.elim
        · have headNeSource :
              head.id ≠ source.id := by
            intro same
            apply uniqueParts.1
            exact List.mem_map.mpr
              ⟨source, sourceInTail, same.symm⟩
          have headNeTarget :
              head.id ≠ target.id := by
            intro same
            apply uniqueParts.1
            exact List.mem_map.mpr
              ⟨target, targetInTail, same.symm⟩
          have headBeqSource :
              (head.id == source.id) = false :=
            beq_eq_false_iff_ne.mpr headNeSource
          have headBeqTarget :
              (head.id == target.id) = false :=
            beq_eq_false_iff_ne.mpr headNeTarget
          have tailOrder :
              RC11.IdBefore source.id target.id
                (tail.map RC11.Atom.id) := by
            refine ⟨
              List.mem_map.mpr
                ⟨source, sourceInTail, rfl⟩,
              List.mem_map.mpr
                ⟨target, targetInTail, rfl⟩,
              ?_⟩
            have orderShape := ordered.2.2
            simpa [List.idxOf_cons, headBeqSource,
              headBeqTarget] using orderShape
          obtain ⟨earlier, between, later, tailShape⟩ :=
            inductionHypothesis uniqueParts.2
              sourceInTail targetInTail tailOrder
          exact ⟨head :: earlier, between, later, by
            simp [tailShape]⟩

private theorem AtomBefore.map
    {schedule : List (RC11.Atom α)}
    {source target : RC11.Atom α}
    {mapEvent :
      RC11.Atom α → TreiberRC11.Event α}
    (before : AtomBefore source target schedule) :
    TreiberRC11.Before
      (mapEvent source)
      (mapEvent target)
      (schedule.map mapEvent) := by
  obtain ⟨earlier, between, later, scheduleShape⟩ :=
    before
  subst schedule
  exact
    ⟨earlier.map mapEvent,
      between.map mapEvent,
      later.map mapEvent, by simp⟩

/--
Facts required of a projection from independent atoms to one target skeleton.

Exact list equality retains occurrence order as well as carrier membership.
The remaining fields state preservation of the observations used by the
single-location relation proof.
-/
structure Projection
    (candidate : RC11.Candidate α)
    (skeleton : TreiberRC11.EventGraph.Skeleton α) where
  toEvent :
    RC11.Atom α → TreiberRC11.Event α
  events :
    candidate.atoms.map toEvent =
      skeleton.events
  id_eq :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).id = atom.id
  thread_eq :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).thread? = atom.thread?
  order_eq :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).order = atom.order
  readValue_eq :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).readValue =
          atom.readValue.map pointerValue
  writtenValue_eq :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).writtenValue =
          atom.writtenValue.map pointerValue
  isRMW_iff :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).IsRMW ↔ atom.IsRMW
  isInitial_iff :
    ∀ (atom) (_ : atom ∈ candidate.atoms),
        (toEvent atom).IsInitial ↔ atom.IsInitial
  injectiveOn :
    ∀ {left right},
      left ∈ candidate.atoms →
      right ∈ candidate.atoms →
      toEvent left = toEvent right →
      left = right
  programOrder_iff :
    ∀ {source target},
      source ∈ candidate.atoms →
      target ∈ candidate.atoms →
      (skeleton.programOrder (toEvent source) (toEvent target) ↔
        RC11.PO candidate source target)

namespace Projection

theorem toEvent_mem
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    {atom : RC11.Atom α}
    (member : atom ∈ candidate.atoms) :
    projection.toEvent atom ∈ skeleton.events := by
  rw [← projection.events]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

theorem exists_atom_of_mem
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    {event : TreiberRC11.Event α}
    (member : event ∈ skeleton.events) :
    ∃ atom,
      atom ∈ candidate.atoms ∧
        projection.toEvent atom = event := by
  rw [← projection.events] at member
  obtain ⟨atom, atomMember, projects⟩ :=
    List.mem_map.mp member
  exact ⟨atom, atomMember, projects⟩

theorem isRead_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    {atom : RC11.Atom α}
    (member : atom ∈ candidate.atoms) :
    (projection.toEvent atom).IsRead ↔ atom.IsRead := by
  unfold TreiberRC11.Event.IsRead RC11.Atom.IsRead
  rw [projection.readValue_eq atom member]
  cases shape : atom.readValue with
  | none =>
      simp
  | some value =>
      simp

theorem isWrite_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    {atom : RC11.Atom α}
    (member : atom ∈ candidate.atoms) :
    (projection.toEvent atom).IsWrite ↔ atom.IsWrite := by
  unfold TreiberRC11.Event.IsWrite RC11.Atom.IsWrite
  rw [projection.writtenValue_eq atom member]
  cases shape : atom.writtenValue with
  | none =>
      simp
  | some value =>
      simp

/--
Construct the target relation-data certificate directly from an independent
valid candidate.  No raw checker fact appears among its inputs.
-/
def toAtomicRelationData
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.AtomicRelationData skeleton where
  writeTail :=
    candidate.modificationOrder
  writeTailNodup :=
    valid.writeTailNodup
  writeTailExact := by
    intro eventId
    rw [valid.writeTailExact eventId]
    constructor
    · rintro ⟨atom, atomMember, atomId, atomWrites,
          atomNotInitial⟩
      refine
        ⟨projection.toEvent atom,
          projection.toEvent_mem atomMember,
          ?_, ?_, ?_⟩
      · exact (projection.id_eq atom atomMember).trans atomId
      · exact
          (projection.isWrite_iff atomMember).mpr atomWrites
      · intro targetInitial
        have initialPreserved :
            (projection.toEvent atom).IsInitial ↔
              atom.IsInitial :=
          Projection.isInitial_iff
            projection atom atomMember
        exact atomNotInitial
          (initialPreserved.mp targetInitial)
    · rintro ⟨event, eventMember, eventIdShape,
          eventWrites, eventNotInitial⟩
      obtain ⟨atom, atomMember, projectionShape⟩ :=
        projection.exists_atom_of_mem eventMember
      subst event
      refine ⟨atom, atomMember, ?_, ?_, ?_⟩
      · exact (projection.id_eq atom atomMember).symm.trans
          eventIdShape
      · exact
          (projection.isWrite_iff atomMember).mp eventWrites
      · intro atomInitial
        have initialPreserved :
            (projection.toEvent atom).IsInitial ↔
              atom.IsInitial :=
          Projection.isInitial_iff
            projection atom atomMember
        exact eventNotInitial
          (initialPreserved.mpr atomInitial)
  sourceId :=
    candidate.sourceId
  sourceSpec := by
    intro target targetMember
    obtain ⟨atom, atomMember, projectionShape⟩ :=
      projection.exists_atom_of_mem targetMember
    subst target
    have independentSpec :=
      valid.sourceSpec atom atomMember
    rw [projection.readValue_eq atom atomMember]
    cases readShape : atom.readValue with
    | none =>
        simpa [readShape, projection.id_eq atom atomMember]
          using independentSpec
    | some value =>
        rw [readShape] at independentSpec
        obtain ⟨source, sourceMember, sourceWrites,
          sourceChosen⟩ := independentSpec
        refine
          ⟨projection.toEvent source,
            projection.toEvent_mem sourceMember,
            ?_, ?_⟩
        · rw [projection.writtenValue_eq source sourceMember,
            sourceWrites]
          rfl
        · simpa [projection.id_eq atom atomMember,
            projection.id_eq source sourceMember]
            using sourceChosen
  rmwAdjacent := by
    intro source rmw sourceMember rmwMember
        sourceChosen rmwShape
    obtain ⟨sourceAtom, sourceAtomMember,
        sourceProjection⟩ :=
      projection.exists_atom_of_mem sourceMember
    obtain ⟨rmwAtom, rmwAtomMember, rmwProjection⟩ :=
      projection.exists_atom_of_mem rmwMember
    subst source
    subst rmw
    have independentChosen :
        candidate.sourceId rmwAtom.id =
          some sourceAtom.id := by
      simpa [projection.id_eq rmwAtom rmwAtomMember,
        projection.id_eq sourceAtom sourceAtomMember]
        using sourceChosen
    have independentRMW :
        rmwAtom.IsRMW :=
      (Projection.isRMW_iff
        projection rmwAtom rmwAtomMember).mp rmwShape
    have adjacent :=
      valid.rmwAdjacent
        sourceAtomMember rmwAtomMember
        independentChosen independentRMW
    simpa [TreiberRC11.IdAdjacent, TreiberRC11.IdBefore,
      RC11.IdAdjacent, RC11.IdBefore,
      TreiberRC11.AtomicRelationData.writeOrder,
      RC11.Candidate.writeOrder,
      projection.id_eq sourceAtom sourceAtomMember,
      projection.id_eq rmwAtom rmwAtomMember]
      using adjacent

/-- Program order is reflected exactly on projected carrier atoms. -/
theorem graphProgramOrder_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.programOrder
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.PO candidate source target := by
  change
    skeleton.programOrder
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.PO candidate source target
  exact projection.programOrder_iff
    sourceMember targetMember

/-- Reads-from is reflected exactly on projected carrier atoms. -/
theorem readsFrom_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.readsFrom
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.RF candidate source target := by
  change
    (projection.toEvent source ∈ skeleton.events ∧
      projection.toEvent target ∈ skeleton.events ∧
      candidate.sourceId (projection.toEvent target).id =
        some (projection.toEvent source).id) ↔
      (source ∈ candidate.atoms ∧
        target ∈ candidate.atoms ∧
        candidate.sourceId target.id = some source.id)
  rw [projection.id_eq source sourceMember,
    projection.id_eq target targetMember]
  simp [projection.toEvent_mem sourceMember,
    projection.toEvent_mem targetMember,
    sourceMember, targetMember]

/-- Modification order is reflected exactly on projected carrier atoms. -/
theorem modificationOrder_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.modificationOrder
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.MO candidate source target := by
  change
    (projection.toEvent source ∈ skeleton.events ∧
      projection.toEvent target ∈ skeleton.events ∧
      TreiberRC11.IdBefore
        (projection.toEvent source).id
        (projection.toEvent target).id
        (0 :: candidate.modificationOrder)) ↔
      (source ∈ candidate.atoms ∧
        target ∈ candidate.atoms ∧
        RC11.IdBefore source.id target.id
          candidate.writeOrder)
  rw [projection.id_eq source sourceMember,
    projection.id_eq target targetMember]
  simp only [TreiberRC11.IdBefore, RC11.IdBefore,
    RC11.Candidate.writeOrder]
  simp [projection.toEvent_mem sourceMember,
    projection.toEvent_mem targetMember,
    sourceMember, targetMember]

/-- Reads-before is reflected exactly on projected carrier atoms. -/
theorem readsBefore_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {read laterWrite : RC11.Atom α}
    (readMember : read ∈ candidate.atoms)
    (laterMember : laterWrite ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.ReadsBefore
        (projection.toEvent read)
        (projection.toEvent laterWrite) ↔
      RC11.RB candidate read laterWrite := by
  constructor
  · rintro ⟨sourceEvent, readsFrom, modificationOrder,
        different⟩
    have sourceMember :
        sourceEvent ∈ skeleton.events :=
      (projection.toAtomicRelationData valid
        |>.readsFromClosed readsFrom).1
    obtain ⟨source, sourceAtomMember, sourceShape⟩ :=
      projection.exists_atom_of_mem sourceMember
    subst sourceEvent
    refine ⟨source, ?_, ?_, ?_⟩
    · exact
        (projection.readsFrom_iff valid
          sourceAtomMember readMember).mp readsFrom
    · exact
        (projection.modificationOrder_iff valid
          sourceAtomMember laterMember).mp modificationOrder
    · intro same
      subst laterWrite
      exact different rfl
  · rintro ⟨source, readsFrom, modificationOrder,
        different⟩
    have sourceMember := readsFrom.1
    refine
      ⟨projection.toEvent source,
        (projection.readsFrom_iff valid
          sourceMember readMember).mpr readsFrom,
        (projection.modificationOrder_iff valid
          sourceMember laterMember).mpr modificationOrder,
        ?_⟩
    intro sameProjection
    exact different
      (projection.injectiveOn
        readMember laterMember sameProjection)

/-- Independent extended-coherence paths map to target graph paths. -/
theorem eco_preserved
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (edge : RC11.ECO candidate source target) :
    (projection.toAtomicRelationData valid).graph.ExtendedCoherence
      (projection.toEvent source)
      (projection.toEvent target) := by
  induction edge with
  | readsFrom readsFrom =>
      exact .readsFrom
        ((projection.readsFrom_iff valid
          readsFrom.1 readsFrom.2.1).mpr readsFrom)
  | modificationOrder modificationOrder =>
      exact .modificationOrder
        ((projection.modificationOrder_iff valid
          modificationOrder.1
          modificationOrder.2.1).mpr
            modificationOrder)
  | readsBefore readsBefore =>
      obtain ⟨origin, readsFrom, modificationOrder,
        different⟩ := readsBefore
      exact .readsBefore
        ((projection.readsBefore_iff valid
          readsFrom.2.1
          modificationOrder.2.1).mpr
            ⟨origin, readsFrom, modificationOrder,
              different⟩)
  | transitive first second firstMapped secondMapped =>
      exact .transitive firstMapped secondMapped

/--
Every target extended-coherence path has an independent preimage on the exact
projected carrier.
-/
theorem eco_has_preimage
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {sourceEvent targetEvent : TreiberRC11.Event α}
    (edge :
      (projection.toAtomicRelationData valid).graph.ExtendedCoherence
        sourceEvent targetEvent) :
    ∃ source target,
      source ∈ candidate.atoms ∧
        target ∈ candidate.atoms ∧
        projection.toEvent source = sourceEvent ∧
        projection.toEvent target = targetEvent ∧
        RC11.ECO candidate source target := by
  let data :=
    projection.toAtomicRelationData valid
  induction edge with
  | @readsFrom sourceEvent targetEvent readsFrom =>
      have endpoints :=
        data.readsFromClosed readsFrom
      obtain ⟨source, sourceMember, sourceShape⟩ :=
        projection.exists_atom_of_mem endpoints.1
      obtain ⟨target, targetMember, targetShape⟩ :=
        projection.exists_atom_of_mem endpoints.2
      subst sourceEvent
      subst targetEvent
      exact
        ⟨source, target, sourceMember, targetMember,
          rfl, rfl,
          .readsFrom
            ((projection.readsFrom_iff valid
              sourceMember targetMember).mp readsFrom)⟩
  | @modificationOrder sourceEvent targetEvent modificationOrder =>
      have endpoints :=
        data.modificationOrderClosed modificationOrder
      obtain ⟨source, sourceMember, sourceShape⟩ :=
        projection.exists_atom_of_mem endpoints.1
      obtain ⟨target, targetMember, targetShape⟩ :=
        projection.exists_atom_of_mem endpoints.2
      subst sourceEvent
      subst targetEvent
      exact
        ⟨source, target, sourceMember, targetMember,
          rfl, rfl,
          .modificationOrder
            ((projection.modificationOrder_iff valid
              sourceMember targetMember).mp
                modificationOrder)⟩
  | @readsBefore readEvent laterEvent readsBefore =>
      obtain ⟨originEvent, readsFrom,
          modificationOrder, different⟩ :=
        readsBefore
      have readMember :=
        (data.readsFromClosed readsFrom).2
      have laterMember :=
        (data.modificationOrderClosed modificationOrder).2
      obtain ⟨read, readAtomMember, readShape⟩ :=
        projection.exists_atom_of_mem readMember
      obtain ⟨later, laterAtomMember, laterShape⟩ :=
        projection.exists_atom_of_mem laterMember
      subst readEvent
      subst laterEvent
      exact
        ⟨read, later, readAtomMember, laterAtomMember,
          rfl, rfl,
          .readsBefore
            ((projection.readsBefore_iff valid
              readAtomMember laterAtomMember).mp
                ⟨originEvent, readsFrom,
                  modificationOrder, different⟩)⟩
  | @transitive firstEvent middleEvent lastEvent
      firstEdge secondEdge firstPreimage secondPreimage =>
      obtain
        ⟨first, firstMiddle, firstMember,
          firstMiddleMember, firstShape,
          firstMiddleShape, firstIndependent⟩ :=
        firstPreimage
      obtain
        ⟨secondMiddle, last, secondMiddleMember,
          lastMember, secondMiddleShape,
          lastShape, secondIndependent⟩ :=
        secondPreimage
      have sameMiddle :
          firstMiddle = secondMiddle :=
        projection.injectiveOn
          firstMiddleMember secondMiddleMember
          (firstMiddleShape.trans
            secondMiddleShape.symm)
      subst secondMiddle
      exact
        ⟨first, last, firstMember, lastMember,
          firstShape, lastShape,
          .transitive firstIndependent
            secondIndependent⟩

/-- Extended coherence is preserved and reflected on projected atoms. -/
theorem eco_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.ExtendedCoherence
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.ECO candidate source target := by
  constructor
  · intro edge
    obtain
      ⟨sourcePreimage, targetPreimage,
        sourcePreimageMember, targetPreimageMember,
        sourceShape, targetShape, independent⟩ :=
      projection.eco_has_preimage valid edge
    have sourceExact :
        sourcePreimage = source :=
      projection.injectiveOn sourcePreimageMember
        sourceMember sourceShape
    have targetExact :
        targetPreimage = target :=
      projection.injectiveOn targetPreimageMember
        targetMember targetShape
    simpa [sourceExact, targetExact] using independent
  · exact projection.eco_preserved valid

/-- All target relation well-formedness fields are constructed from the bridge. -/
theorem remainingWellFormed
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.RemainingWellFormedRelations
      (projection.toAtomicRelationData valid).graph :=
  (projection.toAtomicRelationData valid)
    |>.toRemainingWellFormedRelations

/-- Map the independent client-compatible atom order to target events. -/
def targetSchedule
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (order : ClientCompatibleOrder candidate) :
    List (TreiberRC11.Event α) :=
  order.schedule.map projection.toEvent

private theorem before_in_targetSchedule
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms)
    (ordered :
      RC11.IdBefore source.id target.id
        (order.schedule.map RC11.Atom.id)) :
    TreiberRC11.Before
      (projection.toEvent source)
      (projection.toEvent target)
      (projection.targetSchedule order) := by
  have scheduledIdsNodup :
      (order.schedule.map RC11.Atom.id).Nodup :=
    order.exactAtomIds.symm.nodup
      valid.atomIdsNodup
  have sourceScheduled :
      source ∈ order.schedule :=
    order.exactAtoms.mem_iff.mpr sourceMember
  have targetScheduled :
      target ∈ order.schedule :=
    order.exactAtoms.mem_iff.mpr targetMember
  exact
    (atomBefore_of_idBefore
      scheduledIdsNodup sourceScheduled
      targetScheduled ordered).map

/--
The independent compatible order constructs the exact primitive target
schedule certificate.
-/
theorem primitiveScheduleCertificate
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.RelationScheduleCheck.PrimitiveEdgeScheduleCertificate
      (projection.toAtomicRelationData valid)
      (projection.targetSchedule order) := by
  let data :=
    projection.toAtomicRelationData valid
  have schedulePerm :
      (projection.targetSchedule order).Perm
        skeleton.events := by
    change
      (order.schedule.map projection.toEvent).Perm
        skeleton.events
    rw [← projection.events]
    exact order.exactAtoms.map projection.toEvent
  refine {
    covers := ?_
    noDuplicates := ?_
    programOrder := ?_
    readsFrom := ?_
    modificationOrder := ?_
    readsBefore := ?_
  }
  · intro event
    exact schedulePerm.mem_iff.symm
  · exact schedulePerm.symm.nodup
      skeleton.noDuplicateEvents
  · intro source target edge
    have endpoints :
        source ∈ skeleton.events ∧
          target ∈ skeleton.events :=
      ⟨edge.1, edge.2.1⟩
    obtain ⟨sourceAtom, sourceMember, sourceShape⟩ :=
      projection.exists_atom_of_mem endpoints.1
    obtain ⟨targetAtom, targetMember, targetShape⟩ :=
      projection.exists_atom_of_mem endpoints.2
    subst source
    subst target
    have independentEdge :
        RC11.PO candidate sourceAtom targetAtom :=
      (projection.graphProgramOrder_iff valid
        sourceMember targetMember).mp edge
    exact projection.before_in_targetSchedule
      valid order sourceMember targetMember
      (order.programOrder independentEdge)
  · intro source target edge
    have endpoints :=
      data.readsFromClosed edge
    obtain ⟨sourceAtom, sourceMember, sourceShape⟩ :=
      projection.exists_atom_of_mem endpoints.1
    obtain ⟨targetAtom, targetMember, targetShape⟩ :=
      projection.exists_atom_of_mem endpoints.2
    subst source
    subst target
    have independentEdge :
        RC11.RF candidate sourceAtom targetAtom :=
      (projection.readsFrom_iff valid
        sourceMember targetMember).mp edge
    exact projection.before_in_targetSchedule
      valid order sourceMember targetMember
      (order.extendedCoherence
        (.readsFrom independentEdge))
  · intro source target edge
    have endpoints :=
      data.modificationOrderClosed edge
    obtain ⟨sourceAtom, sourceMember, sourceShape⟩ :=
      projection.exists_atom_of_mem endpoints.1
    obtain ⟨targetAtom, targetMember, targetShape⟩ :=
      projection.exists_atom_of_mem endpoints.2
    subst source
    subst target
    have independentEdge :
        RC11.MO candidate sourceAtom targetAtom :=
      (projection.modificationOrder_iff valid
        sourceMember targetMember).mp edge
    exact projection.before_in_targetSchedule
      valid order sourceMember targetMember
      (order.extendedCoherence
        (.modificationOrder independentEdge))
  · intro read laterWrite edge
    obtain ⟨source, readsFrom, modificationOrder,
        different⟩ := edge
    have readMember :
        read ∈ skeleton.events :=
      (data.readsFromClosed readsFrom).2
    have laterMember :
        laterWrite ∈ skeleton.events :=
      (data.modificationOrderClosed modificationOrder).2
    obtain ⟨readAtom, readAtomMember, readShape⟩ :=
      projection.exists_atom_of_mem readMember
    obtain ⟨laterAtom, laterAtomMember, laterShape⟩ :=
      projection.exists_atom_of_mem laterMember
    subst read
    subst laterWrite
    have independentEdge :
        RC11.RB candidate readAtom laterAtom :=
      (projection.readsBefore_iff valid
        readAtomMember laterAtomMember).mp
          ⟨source, readsFrom, modificationOrder,
            different⟩
    exact projection.before_in_targetSchedule
      valid order readAtomMember laterAtomMember
      (order.extendedCoherence
        (.readsBefore independentEdge))

/-- The mapped independent order respects target PO and all target ECO paths. -/
theorem scheduleRespectsGraph
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.RespectsGraph
      (projection.toAtomicRelationData valid).graph
      (projection.targetSchedule order) :=
  (projection.primitiveScheduleCertificate valid order)
    |>.toRespectsGraph

/-- The finite target schedule checker accepts the mapped independent order. -/
theorem relationScheduleChecked
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.RelationScheduleCheck.check
        (projection.toAtomicRelationData valid)
        (projection.targetSchedule order) = true :=
  TreiberRC11.RelationScheduleCheck.check_complete_primitive
    (projection.primitiveScheduleCertificate valid order)

/--
The mapped schedule supplies the common numeric rank used by the target
relation model.
-/
def orderWitness
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.RC11OrderWitness
      (projection.toAtomicRelationData valid) :=
  (projection.scheduleRespectsGraph valid order)
    |>.toRC11OrderWitness

/--
The constructed target relation fields and mapped rank satisfy the complete
remaining-consistency interface.
-/
theorem remainingConsistency
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.RemainingConsistency
      (projection.toAtomicRelationData valid).graph :=
  (projection.toAtomicRelationData valid)
    |>.toRemainingConsistency
      (projection.orderWitness valid order)

/--
The generated target carrier, its exact program order, and the constructed
relation certificate form a well-formed target graph.
-/
theorem wellFormed
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.WellFormed
      (projection.toAtomicRelationData valid).graph := by
  let data :=
    projection.toAtomicRelationData valid
  let remaining :=
    projection.remainingConsistency valid order
  exact {
    noDuplicateEvents :=
      skeleton.noDuplicateEvents
    uniqueIds :=
      skeleton.uniqueIds
    programOrderClosed :=
      skeleton.programOrderClosed
        data.readsFrom data.modificationOrder
    programOrderSameThread :=
      skeleton.programOrderSameThread
        data.readsFrom data.modificationOrder
    programOrderIrreflexive :=
      skeleton.programOrderIrreflexive
        data.readsFrom data.modificationOrder
    programOrderTransitive :=
      skeleton.programOrderTransitive
        data.readsFrom data.modificationOrder
    readsFromClosed :=
      remaining.readsFromClosed
    modificationOrderClosed :=
      remaining.modificationOrderClosed
    readsFromValues :=
      remaining.readsFromValues
    readsFromFunctional :=
      remaining.readsFromFunctional
    everyReadHasSource :=
      remaining.everyReadHasSource
    modificationOrderWrites :=
      remaining.modificationOrderWrites
    modificationOrderIrreflexive :=
      remaining.modificationOrderIrreflexive
    modificationOrderTransitive :=
      remaining.modificationOrderTransitive
    modificationOrderTotal :=
      remaining.modificationOrderTotal
    initialExistsUnique :=
      skeleton.initialExistsUnique
    initialPrecedesWrites :=
      remaining.initialPrecedesWrites
    rmwReadsImmediatePredecessor :=
      remaining.rmwReadsImmediatePredecessor
    happensBeforeAcyclic :=
      TreiberRC11.happensBeforeAcyclic_of_coherent
        remaining.coherence
  }

/--
The exact mapped schedule therefore yields full target RC11 core
consistency; no target consistency premise is imported into the bridge.
-/
theorem coreConsistent
    [DecidableEq α]
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    (order : ClientCompatibleOrder candidate) :
    TreiberRC11.CoreConsistent
      (projection.toAtomicRelationData valid).graph := by
  let wellFormed :=
    projection.wellFormed valid order
  let remaining :=
    projection.remainingConsistency valid order
  have orderAcyclic :
      (projection.toAtomicRelationData valid).graph.OrderAcyclic :=
    TreiberRC11.orderAcyclic_of_wellFormed_coherent
      wellFormed remaining.coherence
  exact {
    toWellFormed :=
      wellFormed
    noThinAir :=
      TreiberRC11.noThinAir_of_orderAcyclic
        orderAcyclic
    coherence :=
      remaining.coherence
  }

/-- Canonical raw target data emitted from the constructed certificate. -/
def toRawRelationData
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.RelationDataCheck.RawRelationData :=
  TreiberRC11.RelationDataCheck.serialize
    (projection.toAtomicRelationData valid)

/--
Target relation serialization is exactly the independent canonical
read-source list.
-/
theorem serialize_readSources_eq_canonical
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    (projection.toRawRelationData valid).readSources =
      candidate.canonicalReadSources := by
  change
    skeleton.events.filterMap
        (fun target =>
          (candidate.sourceId target.id).map fun sourceId =>
            (target.id, sourceId)) =
      candidate.atoms.filterMap
        (fun target =>
          (candidate.sourceId target.id).map fun sourceId =>
            (target.id, sourceId))
  rw [← projection.events]
  have filtered :
      ∀ (atoms : List (RC11.Atom α)),
        (∀ atom, atom ∈ atoms → atom ∈ candidate.atoms) →
          (atoms.map projection.toEvent).filterMap
              (fun target =>
                (candidate.sourceId target.id).map
                  fun sourceId => (target.id, sourceId)) =
            atoms.filterMap
              (fun target =>
                (candidate.sourceId target.id).map
                  fun sourceId => (target.id, sourceId)) := by
    intro atoms subset
    induction atoms with
    | nil =>
        rfl
    | cons atom rest inductionHypothesis =>
        have atomMember :
            atom ∈ candidate.atoms :=
          subset atom (by simp)
        have restSubset :
            ∀ item,
              item ∈ rest →
                item ∈ candidate.atoms := by
          intro item member
          exact subset item (by simp [member])
        simp only [List.map_cons, List.filterMap_cons]
        rw [projection.id_eq atom atomMember,
          inductionHypothesis restSubset]
  exact filtered candidate.atoms
    (fun atom member => member)

/-- Canonical independent inputs are retained exactly by target serialization. -/
theorem toRawRelationData_readSources
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    (projection.toRawRelationData valid).readSources =
      candidate.readSources := by
  rw [projection.serialize_readSources_eq_canonical valid]
  exact valid.readSourcesCanonical.symm

@[simp] theorem toRawRelationData_writeTail
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    (projection.toRawRelationData valid).writeTail =
      candidate.modificationOrder :=
  rfl

/-- The translated relation certificate is canonical in the target sense. -/
theorem atomicRelationData_canonical
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.RelationDataCheck.Canonical
      (projection.toAtomicRelationData valid) := by
  unfold TreiberRC11.RelationDataCheck.Canonical
  change
    candidate.sourceId =
      TreiberRC11.RelationDataCheck.sourceFor
        (projection.toRawRelationData valid).readSources
  rw [projection.toRawRelationData_readSources valid]
  unfold RC11.Candidate.sourceId
  exact sourceFor_eq_target candidate.readSources

/-- The exact target serialization passes the finite relation validator. -/
theorem validate_toRawRelationData
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.RelationDataCheck.validate
        skeleton
        (projection.toRawRelationData valid) = true :=
  TreiberRC11.RelationDataCheck.validate_serialize
    (projection.toAtomicRelationData valid)

/-- Checker acceptance retains an exact returned certificate. -/
theorem check?_toRawRelationData
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    ∃ checked : TreiberRC11.AtomicRelationData skeleton,
      TreiberRC11.RelationDataCheck.check?
          skeleton
          (projection.toRawRelationData valid) =
        some checked :=
  TreiberRC11.RelationDataCheck.check?_serialize
    (projection.toAtomicRelationData valid)

/-- Canonicality strengthens acceptance to exact certificate equality. -/
theorem check?_toRawRelationData_eq_some
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.RelationDataCheck.check?
        skeleton
        (projection.toRawRelationData valid) =
      some (projection.toAtomicRelationData valid) :=
  TreiberRC11.RelationDataCheck.check?_serialize_eq_some
    (projection.toAtomicRelationData valid)
    (projection.atomicRelationData_canonical valid)

end Projection

end WeakMemory.TreiberC11V1.RelationFrontend

namespace WeakMemory.TreiberC11V1.SupportedExecution

open RelationFrontend

/-!
## Concrete supported-execution endpoint

The source frontend proves every field of the generic relation projection
from the independent source run and canonical identifiers.  The definitions
below expose the resulting target relation data without asking downstream
modules to reassemble that contract.
-/

/-- The canonical atom-to-event projection for one supported execution. -/
def relationProjection
    (execution : SupportedExecution α) :
    RelationFrontend.Projection
      execution.candidate
      execution.toControlledSource.skeleton where
  toEvent :=
    RC11.Atom.toTarget
  events :=
    execution.atoms_toTarget_eq_events
  id_eq := by
    intro atom member
    exact RC11.Atom.toTarget_id atom
  thread_eq := by
    intro atom member
    exact RC11.Atom.toTarget_thread? atom
  order_eq := by
    intro atom member
    exact RC11.Atom.toTarget_order atom
  readValue_eq := by
    intro atom member
    change
      atom.toTarget.readValue =
        atom.readValue.map Ptr.toTarget
    exact execution.atom_toTarget_readValue atom member
  writtenValue_eq := by
    intro atom member
    change
      atom.toTarget.writtenValue =
        atom.writtenValue.map Ptr.toTarget
    exact RC11.Atom.toTarget_writtenValue atom
  isRMW_iff := by
    intro atom member
    exact RC11.Atom.toTarget_isRMW atom
  isInitial_iff := by
    intro atom member
    exact RC11.Atom.toTarget_isInitial atom
  injectiveOn := by
    intro left right leftMember rightMember sameEvent
    exact execution.atom_toTarget_injectiveOn
      leftMember rightMember sameEvent
  programOrder_iff := by
    intro source target sourceMember targetMember
    exact execution.programOrder_toTarget_iff
      sourceMember targetMember

/-- Canonical target relation data translated from independent RF/MO data. -/
def relationData
    (execution : SupportedExecution α) :
    TreiberRC11.AtomicRelationData
      execution.toControlledSource.skeleton :=
  execution.relationProjection.toAtomicRelationData
    execution.rc11

/-- Exact finite target RF/MO serialization. -/
def rawRelationData
    (execution : SupportedExecution α) :
    TreiberRC11.RelationDataCheck.RawRelationData :=
  execution.relationProjection.toRawRelationData
    execution.rc11

/-- The independent compatible order mapped to target graph events. -/
def relationSchedule
    (execution : SupportedExecution α) :
    List (TreiberRC11.Event α) :=
  execution.relationProjection.targetSchedule
    execution.order

@[simp] theorem relationData_writeTail
    (execution : SupportedExecution α) :
    execution.relationData.writeTail =
      execution.candidate.modificationOrder :=
  rfl

@[simp] theorem relationData_sourceId
    (execution : SupportedExecution α) :
    execution.relationData.sourceId =
      execution.candidate.sourceId :=
  rfl

@[simp] theorem rawRelationData_writeTail
    (execution : SupportedExecution α) :
    execution.rawRelationData.writeTail =
      execution.candidate.modificationOrder :=
  execution.relationProjection.toRawRelationData_writeTail
    execution.rc11

@[simp] theorem rawRelationData_readSources
    (execution : SupportedExecution α) :
    execution.rawRelationData.readSources =
      execution.candidate.readSources :=
  execution.relationProjection.toRawRelationData_readSources
    execution.rc11

/-- Target program order is exactly independent program order. -/
theorem relationData_programOrder_iff
    (execution : SupportedExecution α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ execution.candidate.atoms)
    (targetMember :
      target ∈ execution.candidate.atoms) :
    execution.relationData.graph.programOrder
        source.toTarget target.toTarget ↔
      RC11.PO execution.candidate source target :=
  execution.relationProjection.graphProgramOrder_iff
    execution.rc11 sourceMember targetMember

/-- Target reads-from is exactly independent reads-from. -/
theorem relationData_readsFrom_iff
    (execution : SupportedExecution α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ execution.candidate.atoms)
    (targetMember :
      target ∈ execution.candidate.atoms) :
    execution.relationData.graph.readsFrom
        source.toTarget target.toTarget ↔
      RC11.RF execution.candidate source target :=
  execution.relationProjection.readsFrom_iff
    execution.rc11 sourceMember targetMember

/-- Target modification order is exactly independent modification order. -/
theorem relationData_modificationOrder_iff
    (execution : SupportedExecution α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ execution.candidate.atoms)
    (targetMember :
      target ∈ execution.candidate.atoms) :
    execution.relationData.graph.modificationOrder
        source.toTarget target.toTarget ↔
      RC11.MO execution.candidate source target :=
  execution.relationProjection.modificationOrder_iff
    execution.rc11 sourceMember targetMember

/-- Target reads-before is exactly independent reads-before. -/
theorem relationData_readsBefore_iff
    (execution : SupportedExecution α)
    {read laterWrite : RC11.Atom α}
    (readMember :
      read ∈ execution.candidate.atoms)
    (laterMember :
      laterWrite ∈ execution.candidate.atoms) :
    execution.relationData.graph.ReadsBefore
        read.toTarget laterWrite.toTarget ↔
      RC11.RB execution.candidate read laterWrite :=
  execution.relationProjection.readsBefore_iff
    execution.rc11 readMember laterMember

/-- Target extended coherence is exactly independent extended coherence. -/
theorem relationData_extendedCoherence_iff
    (execution : SupportedExecution α)
    {source target : RC11.Atom α}
    (sourceMember :
      source ∈ execution.candidate.atoms)
    (targetMember :
      target ∈ execution.candidate.atoms) :
    execution.relationData.graph.ExtendedCoherence
        source.toTarget target.toTarget ↔
      RC11.ECO execution.candidate source target :=
  execution.relationProjection.eco_iff
    execution.rc11 sourceMember targetMember

/-- The finite relation validator accepts the exact serialized input. -/
theorem validate_rawRelationData
    (execution : SupportedExecution α) :
    TreiberRC11.RelationDataCheck.validate
        execution.toControlledSource.skeleton
        execution.rawRelationData = true :=
  execution.relationProjection.validate_toRawRelationData
    execution.rc11

/--
The relation checker reconstructs exactly the translated certificate, not
merely an extensionally related witness.
-/
theorem check?_rawRelationData_eq_some
    (execution : SupportedExecution α) :
    TreiberRC11.RelationDataCheck.check?
        execution.toControlledSource.skeleton
        execution.rawRelationData =
      some execution.relationData :=
  execution.relationProjection.check?_toRawRelationData_eq_some
    execution.rc11

/-- The mapped independent order respects target program and coherence order. -/
theorem relationSchedule_respectsGraph
    [DecidableEq α]
    (execution : SupportedExecution α) :
    TreiberRC11.RespectsGraph
      execution.relationData.graph
      execution.relationSchedule :=
  execution.relationProjection.scheduleRespectsGraph
    execution.rc11 execution.order

/-- The executable target schedule checker accepts the exact mapped order. -/
theorem check_relationSchedule
    [DecidableEq α]
    (execution : SupportedExecution α) :
    TreiberRC11.RelationScheduleCheck.check
        execution.relationData
        execution.relationSchedule = true :=
  execution.relationProjection.relationScheduleChecked
    execution.rc11 execution.order

/-- The translated target relation graph is fully RC11-core consistent. -/
theorem relationData_coreConsistent
    [DecidableEq α]
    (execution : SupportedExecution α) :
    TreiberRC11.CoreConsistent
      execution.relationData.graph :=
  execution.relationProjection.coreConsistent
    execution.rc11 execution.order

end WeakMemory.TreiberC11V1.SupportedExecution
