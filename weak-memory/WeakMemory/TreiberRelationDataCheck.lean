import WeakMemory.TreiberRelations

namespace WeakMemory.TreiberRC11

/-!
# Executable checking of finite reads-from and modification-order data

The raw format in this module contains only finite data:

* `writeTail` is the proposed modification order after initializer `0`;
* `readSources` contains `(targetId, sourceId)` entries.

The checker enumerates only `EventGraph.Skeleton.events`, the supplied write
list, and the supplied association list.  It does not decide a predicate by
ranging over the ambient (infinite) identifier or event types.

It relies only on the guarantees already proved for a generated `Skeleton`:
the carrier is finite, its identifiers are unique, and initializer `0` is
present.  Passing this checker establishes relation well-formedness; it does
not by itself establish RC11 coherence or consistency.
-/

namespace RelationDataCheck

/-- Untrusted finite input for the two atomic-head relations. -/
structure RawRelationData where
  /-- Proposed non-initial writes in modification order. -/
  writeTail : List EventId
  /-- Proposed `(read target, write source)` identifier associations. -/
  readSources : List (EventId × EventId)
  deriving Repr, DecidableEq

/-- First source associated with a target identifier, if present. -/
def sourceFor :
    List (EventId × EventId) → EventId → Option EventId
  | [], _ =>
      none
  | (candidateTarget, candidateSource) :: rest, target =>
      if candidateTarget = target then
        some candidateSource
      else
        sourceFor rest target

private theorem sourceFor_eq_some_mem
    {entries : List (EventId × EventId)}
    {target source : EventId}
    (found : sourceFor entries target = some source) :
    (target, source) ∈ entries := by
  induction entries with
  | nil =>
      simp [sourceFor] at found
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨candidateTarget, candidateSource⟩
      by_cases sameTarget : candidateTarget = target
      · simp [sourceFor, sameTarget] at found
        subst candidateTarget
        subst candidateSource
        simp
      · have inRest :
            (target, source) ∈ rest :=
          inductionHypothesis (by
            simpa [sourceFor, sameTarget] using found)
        exact List.mem_cons_of_mem _ inRest

private theorem sourceFor_eq_none_iff
    (entries : List (EventId × EventId))
    (target : EventId) :
    sourceFor entries target = none ↔
      target ∉ entries.map Prod.fst := by
  induction entries with
  | nil =>
      simp [sourceFor]
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨candidateTarget, candidateSource⟩
      by_cases sameTarget : candidateTarget = target
      · subst candidateTarget
        simp [sourceFor]
      · have reverseTarget : target ≠ candidateTarget :=
          Ne.symm sameTarget
        simp [sourceFor, sameTarget, reverseTarget,
          inductionHypothesis]

private theorem sourceFor_eq_some_of_mem
    {entries : List (EventId × EventId)}
    {target source : EventId}
    (targetIdsNodup : (entries.map Prod.fst).Nodup)
    (member : (target, source) ∈ entries) :
    sourceFor entries target = some source := by
  induction entries with
  | nil =>
      simp at member
  | cons entry rest inductionHypothesis =>
      rcases entry with
        ⟨candidateTarget, candidateSource⟩
      have uniqueParts :=
        List.nodup_cons.mp targetIdsNodup
      simp only [List.mem_cons] at member
      rcases member with sameEntry | inRest
      · cases sameEntry
        simp [sourceFor]
      · have targetInRest :
            target ∈ rest.map Prod.fst :=
          List.mem_map.mpr
            ⟨(target, source), inRest, rfl⟩
        have differentTarget :
            candidateTarget ≠ target := by
          intro sameTarget
          subst candidateTarget
          exact uniqueParts.1 targetInRest
        simpa [sourceFor, differentTarget] using
          inductionHypothesis uniqueParts.2 inRest

/-- Boolean duplicate-freedom over an explicitly supplied finite list. -/
private def nodup
    [DecidableEq β] :
    List β → Bool
  | [] =>
      true
  | item :: rest =>
      !decide (item ∈ rest) && nodup rest

private theorem nodup_eq_true_iff
    [DecidableEq β]
    (items : List β) :
    nodup items = true ↔ items.Nodup := by
  induction items with
  | nil =>
      simp [nodup]
  | cons item rest inductionHypothesis =>
      simp [nodup, inductionHypothesis, List.nodup_cons]

/-- Boolean equality of the member sets of two finite lists. -/
private def covers
    [DecidableEq β]
    (expected supplied : List β) :
    Bool :=
  (expected.all fun item => decide (item ∈ supplied)) &&
    (supplied.all fun item => decide (item ∈ expected))

private theorem covers_eq_true_iff
    [DecidableEq β]
    (expected supplied : List β) :
    covers expected supplied = true ↔
      ∀ item, item ∈ expected ↔ item ∈ supplied := by
  simp only [covers, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨forward, reverse⟩ item
    exact ⟨forward item, reverse item⟩
  · intro sameMembers
    exact
      ⟨fun item member => (sameMembers item).mp member,
        fun item member => (sameMembers item).mpr member⟩

private def isRead (event : Event α) : Bool :=
  event.readValue.isSome

private theorem isRead_eq_true_iff
    (event : Event α) :
    isRead event = true ↔ event.IsRead := by
  cases readShape : event.readValue <;>
    simp [isRead, Event.IsRead, readShape]

private def isWrite (event : Event α) : Bool :=
  event.writtenValue.isSome

private theorem isWrite_eq_true_iff
    (event : Event α) :
    isWrite event = true ↔ event.IsWrite := by
  cases writeShape : event.writtenValue <;>
    simp [isWrite, Event.IsWrite, writeShape]

private def isInitial : Event α → Bool
  | ⟨_, .initial⟩ =>
      true
  | ⟨_, .algorithm _⟩ =>
      false

private theorem isInitial_eq_true_iff
    (event : Event α) :
    isInitial event = true ↔ event.IsInitial := by
  rcases event with ⟨eventId, kind⟩
  cases kind <;> simp [isInitial, Event.IsInitial]

private def isNonInitialWrite (event : Event α) : Bool :=
  isWrite event && !isInitial event

private theorem isNonInitialWrite_eq_true_iff
    (event : Event α) :
    isNonInitialWrite event = true ↔
      event.IsWrite ∧ ¬ event.IsInitial := by
  simp only [isNonInitialWrite, Bool.and_eq_true]
  rw [isWrite_eq_true_iff]
  constructor
  · rintro ⟨writes, notInitial⟩
    exact ⟨writes, by
      intro initial
      have initialTrue :=
        (isInitial_eq_true_iff event).mpr initial
      rw [initialTrue] at notInitial
      contradiction⟩
  · rintro ⟨writes, notInitial⟩
    refine ⟨writes, ?_⟩
    cases initialShape : isInitial event with
    | false =>
        rfl
    | true =>
        exact (notInitial
          ((isInitial_eq_true_iff event).mp initialShape)).elim

private def isRMW : Event α → Bool
  | ⟨_, .algorithm (.pushSuccess ..)⟩ =>
      true
  | ⟨_, .algorithm (.popSuccess ..)⟩ =>
      true
  | _ =>
      false

private theorem isRMW_eq_true_iff
    (event : Event α) :
    isRMW event = true ↔ event.IsRMW := by
  rcases event with ⟨eventId, kind⟩
  cases kind with
  | initial =>
      simp [isRMW, Event.IsRMW]
  | algorithm action =>
      cases action <;> simp [isRMW, Event.IsRMW]

/-- Identifiers of the events selected by a finite Boolean predicate. -/
private def selectedIds
    (select : Event α → Bool) :
    List (Event α) → List EventId
  | [] =>
      []
  | event :: rest =>
      if select event then
        event.id :: selectedIds select rest
      else
        selectedIds select rest

private theorem mem_selectedIds_iff
    (select : Event α → Bool)
    (events : List (Event α))
    (eventId : EventId) :
    eventId ∈ selectedIds select events ↔
      ∃ event,
        event ∈ events ∧
          event.id = eventId ∧
          select event = true := by
  induction events with
  | nil =>
      simp [selectedIds]
  | cons event rest inductionHypothesis =>
      cases selected : select event with
      | false =>
          simp [selectedIds, selected, inductionHypothesis]
      | true =>
          constructor
          · intro member
            simp only [selectedIds, selected, if_true,
              List.mem_cons] at member
            rcases member with headId | tailMember
            · exact
                ⟨event, by simp, headId.symm, selected⟩
            · obtain
                ⟨actual, actualMember, actualId,
                  actualSelected⟩ :=
                inductionHypothesis.mp tailMember
              exact
                ⟨actual, by simp [actualMember],
                  actualId, actualSelected⟩
          · rintro
              ⟨actual, actualMember, actualId,
                actualSelected⟩
            simp only [List.mem_cons] at actualMember
            simp only [selectedIds, selected, if_true,
              List.mem_cons]
            rcases actualMember with sameEvent | inRest
            · subst actual
              exact Or.inl actualId.symm
            · exact Or.inr
                (inductionHypothesis.mpr
                  ⟨actual, inRest, actualId,
                    actualSelected⟩)

private def nonInitialWriteIds
    (skeleton : EventGraph.Skeleton α) :
    List EventId :=
  selectedIds isNonInitialWrite skeleton.events

private theorem mem_nonInitialWriteIds_iff
    (skeleton : EventGraph.Skeleton α)
    (eventId : EventId) :
    eventId ∈ nonInitialWriteIds skeleton ↔
      ∃ event,
        event ∈ skeleton.events ∧
          event.id = eventId ∧
          event.IsWrite ∧
          ¬ event.IsInitial := by
  rw [nonInitialWriteIds,
    mem_selectedIds_iff]
  constructor
  · rintro ⟨event, member, sameId, selected⟩
    exact ⟨event, member, sameId,
      (isNonInitialWrite_eq_true_iff event).mp selected⟩
  · rintro ⟨event, member, sameId, writes, notInitial⟩
    exact ⟨event, member, sameId,
      (isNonInitialWrite_eq_true_iff event).mpr
        ⟨writes, notInitial⟩⟩

private def readIds
    (skeleton : EventGraph.Skeleton α) :
    List EventId :=
  selectedIds isRead skeleton.events

private theorem mem_readIds_iff
    (skeleton : EventGraph.Skeleton α)
    (eventId : EventId) :
    eventId ∈ readIds skeleton ↔
      ∃ event,
        event ∈ skeleton.events ∧
          event.id = eventId ∧
          event.IsRead := by
  rw [readIds, mem_selectedIds_iff]
  constructor
  · rintro ⟨event, member, sameId, selected⟩
    exact ⟨event, member, sameId,
      (isRead_eq_true_iff event).mp selected⟩
  · rintro ⟨event, member, sameId, reads⟩
    exact ⟨event, member, sameId,
      (isRead_eq_true_iff event).mpr reads⟩

private theorem member_id_mem_readIds_iff
    (skeleton : EventGraph.Skeleton α)
    {event : Event α}
    (member : event ∈ skeleton.events) :
    event.id ∈ readIds skeleton ↔ event.IsRead := by
  constructor
  · intro idMember
    obtain ⟨actual, actualMember, sameId, actualReads⟩ :=
      (mem_readIds_iff skeleton event.id).mp idMember
    have sameEvent :
        actual = event :=
      skeleton.uniqueIds actualMember member sameId
    simpa [sameEvent] using actualReads
  · intro reads
    exact (mem_readIds_iff skeleton event.id).mpr
      ⟨event, member, rfl, reads⟩

/-- Find a carrier event by identifier without comparing payloads. -/
private def findEvent?
    (eventId : EventId) :
    List (Event α) → Option (Event α)
  | [] =>
      none
  | event :: rest =>
      if event.id = eventId then
        some event
      else
        findEvent? eventId rest

private theorem findEvent?_eq_some_sound
    {events : List (Event α)}
    {eventId : EventId}
    {event : Event α}
    (found : findEvent? eventId events = some event) :
    event ∈ events ∧ event.id = eventId := by
  induction events with
  | nil =>
      simp [findEvent?] at found
  | cons head rest inductionHypothesis =>
      by_cases sameId : head.id = eventId
      · simp [findEvent?, sameId] at found
        subst event
        exact ⟨by simp, sameId⟩
      · have inRest :=
          inductionHypothesis (by
            simpa [findEvent?, sameId] using found)
        exact ⟨List.mem_cons_of_mem _ inRest.1, inRest.2⟩

private theorem findEvent?_isSome_of_mem
    {events : List (Event α)}
    {event : Event α}
    (member : event ∈ events) :
    ∃ actual,
      findEvent? event.id events = some actual := by
  induction events with
  | nil =>
      simp at member
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with sameEvent | inRest
      · subst head
        exact ⟨event, by simp [findEvent?]⟩
      · by_cases sameId : head.id = event.id
        · exact ⟨head, by simp [findEvent?, sameId]⟩
        · obtain ⟨actual, found⟩ :=
            inductionHypothesis inRest
          exact
            ⟨actual, by
              simpa [findEvent?, sameId] using found⟩

private theorem findEvent?_member
    (skeleton : EventGraph.Skeleton α)
    {event : Event α}
    (member : event ∈ skeleton.events) :
    findEvent? event.id skeleton.events = some event := by
  obtain ⟨actual, found⟩ :=
    findEvent?_isSome_of_mem member
  have actualInfo :=
    findEvent?_eq_some_sound found
  have sameEvent :
      actual = event :=
    skeleton.uniqueIds
      actualInfo.1 member actualInfo.2
  simpa [sameEvent] using found

/-- Executable `IdBefore` over one explicitly supplied finite order. -/
private def before
    (first second : EventId)
    (order : List EventId) :
    Bool :=
  decide (first ∈ order) &&
    (decide (second ∈ order) &&
      decide (order.idxOf first < order.idxOf second))

private theorem before_eq_true_iff
    (first second : EventId)
    (order : List EventId) :
    before first second order = true ↔
      IdBefore first second order := by
  simp [before, IdBefore]

/--
Finite adjacency check.  The no-between test enumerates only identifiers in
the supplied order; membership in `IdBefore` makes that finite enumeration
logically complete.
-/
private def adjacent
    (first second : EventId)
    (order : List EventId) :
    Bool :=
  before first second order &&
    order.all fun middle =>
      !(before first middle order &&
        before middle second order)

private theorem adjacent_eq_true_iff
    {first second : EventId}
    {order : List EventId}
    :
    adjacent first second order = true ↔
      IdAdjacent first second order := by
  constructor
  · intro checked
    have components :
        before first second order = true ∧
          order.all (fun middle =>
            !(before first middle order &&
              before middle second order)) = true := by
      simpa only [adjacent, Bool.and_eq_true] using checked
    have firstBefore :
        IdBefore first second order :=
      (before_eq_true_iff first second order).mp
        components.1
    have everyMiddle :=
      (List.all_eq_true.mp components.2)
    refine ⟨firstBefore, ?_⟩
    intro middle between
    have middleMember :
        middle ∈ order :=
      between.1.2.1
    have firstPart :
        before first middle order = true :=
      (before_eq_true_iff first middle order).mpr
        between.1
    have secondPart :
        before middle second order = true :=
      (before_eq_true_iff middle second order).mpr
        between.2
    have rejected :=
      everyMiddle middle middleMember
    simp [firstPart, secondPart] at rejected
  · intro logical
    unfold adjacent
    rw [Bool.and_eq_true]
    refine
      ⟨(before_eq_true_iff first second order).mpr
          logical.1,
        ?_⟩
    apply List.all_eq_true.mpr
    intro middle middleMember
    have notBoth :
        (before first middle order &&
            before middle second order) ≠
          true := by
      intro bothChecked
      have both :
          before first middle order = true ∧
            before middle second order = true := by
        simpa only [Bool.and_eq_true] using bothChecked
      exact logical.2 middle
        ⟨(before_eq_true_iff first middle order).mp
            both.1,
          (before_eq_true_iff middle second order).mp
            both.2⟩
    cases combined :
        (before first middle order &&
          before middle second order) with
    | false =>
        rfl
    | true =>
        exact (notBoth combined).elim

/-- Check one raw read-source association against the finite carrier. -/
private def associationValid
    (skeleton : EventGraph.Skeleton α)
    (writeTail : List EventId) :
    EventId × EventId → Bool
  | (targetId, sourceId) =>
      match findEvent? targetId skeleton.events,
          findEvent? sourceId skeleton.events with
      | some target, some source =>
          match target.readValue with
          | none =>
              false
          | some value =>
              decide (source.writtenValue = some value) &&
                if isRMW target then
                  adjacent sourceId targetId (0 :: writeTail)
                else
                  true
      | _, _ =>
          false

private theorem associationValid_sound
    (skeleton : EventGraph.Skeleton α)
    (writeTail : List EventId)
    {targetId sourceId : EventId}
    (checked :
      associationValid skeleton writeTail
        (targetId, sourceId) = true) :
    ∃ target source value,
      target ∈ skeleton.events ∧
        target.id = targetId ∧
        source ∈ skeleton.events ∧
        source.id = sourceId ∧
        target.readValue = some value ∧
        source.writtenValue = some value ∧
        (target.IsRMW →
          IdAdjacent source.id target.id (0 :: writeTail)) := by
  unfold associationValid at checked
  cases targetFound :
      findEvent? targetId skeleton.events with
  | none =>
      simp [targetFound] at checked
  | some target =>
      cases sourceFound :
          findEvent? sourceId skeleton.events with
      | none =>
          simp [targetFound, sourceFound] at checked
      | some source =>
          cases readShape : target.readValue with
          | none =>
              simp [targetFound, sourceFound, readShape] at checked
          | some value =>
              simp only [targetFound, sourceFound, readShape,
                Bool.and_eq_true, decide_eq_true_eq] at checked
              rcases checked with
                ⟨sourceWrites, adjacencyCheck⟩
              have targetInfo :=
                findEvent?_eq_some_sound targetFound
              have sourceInfo :=
                findEvent?_eq_some_sound sourceFound
              refine
                ⟨target, source, value,
                  targetInfo.1, targetInfo.2,
                  sourceInfo.1, sourceInfo.2,
                  readShape, sourceWrites, ?_⟩
              intro targetRMW
              have targetRMWCheck :
                  isRMW target = true :=
                (isRMW_eq_true_iff target).mpr targetRMW
              simp [targetRMWCheck] at adjacencyCheck
              have logicalAdjacency :=
                adjacent_eq_true_iff.mp adjacencyCheck
              simpa [targetInfo.2, sourceInfo.2] using
                logicalAdjacency

/--
Run every raw check using only the finite skeleton carrier and finite input
lists.
-/
def validate
    (skeleton : EventGraph.Skeleton α)
    (raw : RawRelationData) :
    Bool :=
  nodup raw.writeTail &&
    (covers (nonInitialWriteIds skeleton) raw.writeTail &&
      (nodup (raw.readSources.map Prod.fst) &&
        (covers (readIds skeleton)
            (raw.readSources.map Prod.fst) &&
          raw.readSources.all
            (associationValid skeleton raw.writeTail))))

private def toAtomicRelationData
    (skeleton : EventGraph.Skeleton α)
    (raw : RawRelationData)
    (checked : validate skeleton raw = true) :
    AtomicRelationData skeleton := by
  have checks :
      nodup raw.writeTail = true ∧
        covers (nonInitialWriteIds skeleton) raw.writeTail = true ∧
        nodup (raw.readSources.map Prod.fst) = true ∧
        covers (readIds skeleton)
          (raw.readSources.map Prod.fst) = true ∧
        raw.readSources.all
          (associationValid skeleton raw.writeTail) = true := by
    simpa only [validate, Bool.and_eq_true] using checked
  have writeTailUnique :=
    checks.1
  have writeTailCoverage :=
    checks.2.1
  have targetCoverage :=
    checks.2.2.2.1
  have associationsChecked :=
    checks.2.2.2.2
  have writeTailNodup :
      raw.writeTail.Nodup :=
    (nodup_eq_true_iff raw.writeTail).mp writeTailUnique
  have writesCovered :
      ∀ eventId,
        eventId ∈ nonInitialWriteIds skeleton ↔
          eventId ∈ raw.writeTail :=
    (covers_eq_true_iff
      (nonInitialWriteIds skeleton)
      raw.writeTail).mp writeTailCoverage
  have targetsCovered :
      ∀ eventId,
        eventId ∈ readIds skeleton ↔
          eventId ∈ raw.readSources.map Prod.fst :=
    (covers_eq_true_iff
      (readIds skeleton)
      (raw.readSources.map Prod.fst)).mp targetCoverage
  have everyAssociationChecked :
      ∀ entry ∈ raw.readSources,
        associationValid skeleton raw.writeTail entry = true := by
    simpa only [List.all_eq_true] using associationsChecked
  refine
    { writeTail := raw.writeTail
      writeTailNodup := writeTailNodup
      writeTailExact := ?_
      sourceId := sourceFor raw.readSources
      sourceSpec := ?_
      rmwAdjacent := ?_ }
  · intro eventId
    rw [← writesCovered eventId]
    exact mem_nonInitialWriteIds_iff skeleton eventId
  · intro target targetMember
    cases readShape : target.readValue with
    | none =>
        apply (sourceFor_eq_none_iff
          raw.readSources target.id).mpr
        intro targetListed
        have targetReadId :
            target.id ∈ readIds skeleton :=
          (targetsCovered target.id).mpr targetListed
        have targetReads :
            target.IsRead :=
          (member_id_mem_readIds_iff
            skeleton targetMember).mp targetReadId
        obtain ⟨value, reads⟩ := targetReads
        rw [readShape] at reads
        contradiction
    | some value =>
        have targetReads :
            target.IsRead :=
          ⟨value, readShape⟩
        have targetReadId :
            target.id ∈ readIds skeleton :=
          (member_id_mem_readIds_iff
            skeleton targetMember).mpr targetReads
        have targetListed :
            target.id ∈ raw.readSources.map Prod.fst :=
          (targetsCovered target.id).mp targetReadId
        cases chosen :
            sourceFor raw.readSources target.id with
        | none =>
            have notListed :=
              (sourceFor_eq_none_iff
                raw.readSources target.id).mp chosen
            exact (notListed targetListed).elim
        | some sourceId =>
            have associationMember :
                (target.id, sourceId) ∈ raw.readSources :=
              sourceFor_eq_some_mem chosen
            have associationDescription :=
              associationValid_sound skeleton raw.writeTail
                (everyAssociationChecked
                  (target.id, sourceId) associationMember)
            obtain
              ⟨actualTarget, source, actualValue,
                actualTargetMember, actualTargetId,
                sourceMember, sourceIdShape,
                actualTargetReads, sourceWrites, _⟩ :=
              associationDescription
            have sameTarget :
                actualTarget = target :=
              skeleton.uniqueIds
                actualTargetMember targetMember actualTargetId
            subst actualTarget
            have sameValue :
                actualValue = value :=
              Option.some.inj
                (actualTargetReads.symm.trans readShape)
            subst actualValue
            exact
              ⟨source, sourceMember, sourceWrites, by
                rw [sourceIdShape]⟩
  · intro source rmw sourceMember rmwMember chosen rmwShape
    have associationMember :
        (rmw.id, source.id) ∈ raw.readSources :=
      sourceFor_eq_some_mem chosen
    obtain
      ⟨actualTarget, actualSource, value,
        actualTargetMember, actualTargetId,
        actualSourceMember, actualSourceId,
        _, _, adjacency⟩ :=
      associationValid_sound skeleton raw.writeTail
        (everyAssociationChecked
          (rmw.id, source.id) associationMember)
    have sameTarget :
        actualTarget = rmw :=
      skeleton.uniqueIds
        actualTargetMember rmwMember actualTargetId
    have sameSource :
        actualSource = source :=
      skeleton.uniqueIds
        actualSourceMember sourceMember actualSourceId
    subst actualTarget
    subst actualSource
    exact adjacency rmwShape

/--
Validate raw finite relation data and, on success, return the certified
canonical relation data.
-/
def check?
    (skeleton : EventGraph.Skeleton α)
    (raw : RawRelationData) :
    Option (AtomicRelationData skeleton) :=
  if checked : validate skeleton raw = true then
    some (toAtomicRelationData skeleton raw checked)
  else
    none

/--
Every returned certificate uses exactly the raw write list and executable
read-source lookup.
-/
theorem check?_sound
    (skeleton : EventGraph.Skeleton α)
    (raw : RawRelationData)
    {data : AtomicRelationData skeleton}
    (accepted : check? skeleton raw = some data) :
    validate skeleton raw = true ∧
      data.writeTail = raw.writeTail ∧
      data.sourceId = sourceFor raw.readSources ∧
      (raw.readSources.map Prod.fst).Nodup := by
  unfold check? at accepted
  split at accepted
  next checked =>
    simp only [Option.some.injEq] at accepted
    subst data
    refine ⟨checked, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · have checks :
          nodup raw.writeTail = true ∧
            covers (nonInitialWriteIds skeleton)
              raw.writeTail = true ∧
            nodup (raw.readSources.map Prod.fst) = true ∧
            covers (readIds skeleton)
              (raw.readSources.map Prod.fst) = true ∧
            raw.readSources.all
              (associationValid skeleton raw.writeTail) = true := by
        simpa only [validate, Bool.and_eq_true] using checked
      exact
        (nodup_eq_true_iff
          (raw.readSources.map Prod.fst)).mp
          checks.2.2.1
  next rejected =>
    contradiction

/-- The optional conversion succeeds exactly when the finite validator does. -/
theorem check?_isSome_iff
    (skeleton : EventGraph.Skeleton α)
    (raw : RawRelationData) :
    (check? skeleton raw).isSome = true ↔
      validate skeleton raw = true := by
  by_cases checked : validate skeleton raw = true <;>
    simp [check?, checked]

/-- One canonical finite association emitted for a carrier event. -/
private def serializedSource?
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (target : Event α) :
    Option (EventId × EventId) :=
  (data.sourceId target.id).map fun sourceId =>
    (target.id, sourceId)

/--
Canonical raw serialization of existing relation data.

The source list is obtained by a single `filterMap` over the finite carrier;
no source is chosen classically because `AtomicRelationData.sourceId` already
contains the selected identifier.
-/
def serialize
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    RawRelationData where
  writeTail :=
    data.writeTail
  readSources :=
    skeleton.events.filterMap (serializedSource? data)

/--
Canonical relation data has no arbitrary `sourceId` values outside the finite
serialized read carrier.  Its total function is exactly the lookup induced by
its own serialization.

`writeTail` needs no extra condition: `AtomicRelationData.writeTailExact`
already fixes its finite carrier, while list order is intentionally semantic.
-/
def Canonical
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    Prop :=
  data.sourceId =
    sourceFor (serialize data).readSources

private theorem mem_serialize_targetIds_iff
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (eventId : EventId) :
    eventId ∈ (serialize data).readSources.map Prod.fst ↔
      ∃ target,
        target ∈ skeleton.events ∧
          target.id = eventId ∧
          target.IsRead := by
  constructor
  · intro targetIdMember
    obtain ⟨entry, entryMember, entryId⟩ :=
      List.mem_map.mp targetIdMember
    obtain ⟨target, targetMember, selected⟩ :=
      List.mem_filterMap.mp entryMember
    cases chosen : data.sourceId target.id with
    | none =>
        simp [serializedSource?, chosen] at selected
    | some sourceId =>
        simp [serializedSource?, chosen] at selected
        subst entry
        have targetReads :
            target.IsRead := by
          have description :=
            data.sourceSpec target targetMember
          cases readShape : target.readValue with
          | none =>
              rw [readShape] at description
              rw [description] at chosen
              contradiction
          | some value =>
              exact ⟨value, readShape⟩
        exact
          ⟨target, targetMember, by simpa using entryId,
            targetReads⟩
  · rintro ⟨target, targetMember, sameId, targetReads⟩
    obtain ⟨value, readShape⟩ :=
      targetReads
    have description :=
      data.sourceSpec target targetMember
    rw [readShape] at description
    obtain ⟨source, sourceMember, sourceWrites, chosen⟩ :=
      description
    apply List.mem_map.mpr
    refine ⟨(target.id, source.id), ?_, sameId⟩
    apply List.mem_filterMap.mpr
    exact
      ⟨target, targetMember, by
        simp [serializedSource?, chosen]⟩

private theorem serialize_targetIds_nodup
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    (serialize data).readSources.map Prod.fst |>.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  change
    (skeleton.events.filterMap
      (serializedSource? data)).Pairwise
        (fun first second =>
          first.1 ≠ second.1)
  apply List.Pairwise.filterMap
    (R := fun first second : Event α =>
      first.id < second.id)
  · intro first second idsIncrease
      firstEntry firstSelected secondEntry secondSelected
    cases firstChosen : data.sourceId first.id with
    | none =>
        simp [serializedSource?, firstChosen] at firstSelected
    | some firstSource =>
        simp [serializedSource?, firstChosen] at firstSelected
        subst firstEntry
        cases secondChosen : data.sourceId second.id with
        | none =>
            simp [serializedSource?, secondChosen] at secondSelected
        | some secondSource =>
            simp [serializedSource?, secondChosen] at secondSelected
            subst secondEntry
            exact Nat.ne_of_lt idsIncrease
  · exact skeleton.events_pairwise_id_lt

/--
Serialization preserves the selected source identifier at every carrier
event.  Values of `sourceId` outside the carrier are intentionally irrelevant
to the generated execution graph.
-/
theorem sourceFor_serialize_of_mem
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {target : Event α}
    (targetMember : target ∈ skeleton.events) :
    sourceFor (serialize data).readSources target.id =
      data.sourceId target.id := by
  cases chosen : data.sourceId target.id with
  | none =>
      apply (sourceFor_eq_none_iff
        (serialize data).readSources target.id).mpr
      intro targetIdMember
      obtain
        ⟨actual, actualMember, actualId, actualReads⟩ :=
        (mem_serialize_targetIds_iff
          data target.id).mp targetIdMember
      have sameTarget :
          actual = target :=
        skeleton.uniqueIds
          actualMember targetMember actualId
      subst actual
      obtain ⟨value, readShape⟩ :=
        actualReads
      have description :=
        data.sourceSpec target targetMember
      rw [readShape] at description
      obtain ⟨source, sourceMember, sourceWrites,
        actualChosen⟩ :=
        description
      rw [chosen] at actualChosen
      contradiction
  | some sourceId =>
      apply sourceFor_eq_some_of_mem
        (serialize_targetIds_nodup data)
      apply List.mem_filterMap.mpr
      exact
        ⟨target, targetMember, by
          simp [serializedSource?, chosen]⟩

private theorem serializedSource_filterMap_eq
    {skeleton : EventGraph.Skeleton α}
    {left right : AtomicRelationData skeleton}
    (events : List (Event α)) :
    (∀ target,
      target ∈ events →
        left.sourceId target.id =
          right.sourceId target.id) →
      events.filterMap (serializedSource? left) =
        events.filterMap (serializedSource? right) := by
  induction events with
  | nil =>
      intro same
      rfl
  | cons target rest inductionHypothesis =>
      intro same
      have headSame :
          serializedSource? left target =
            serializedSource? right target := by
        unfold serializedSource?
        exact congrArg
          (fun selected =>
            selected.map fun sourceId =>
              (target.id, sourceId))
          (same target (by simp))
      have restSame :
          ∀ event,
            event ∈ rest →
              left.sourceId event.id =
                right.sourceId event.id := by
        intro event member
        exact same event (by simp [member])
      simp only [List.filterMap_cons, headSame,
        inductionHypothesis restSame]

private theorem serializedReadSources_eq_of_sourceId_eq
    {skeleton : EventGraph.Skeleton α}
    {left right : AtomicRelationData skeleton}
    (same :
      ∀ target,
        target ∈ skeleton.events →
          left.sourceId target.id =
            right.sourceId target.id) :
    (serialize left).readSources =
      (serialize right).readSources := by
  change
    skeleton.events.filterMap (serializedSource? left) =
      skeleton.events.filterMap (serializedSource? right)
  exact serializedSource_filterMap_eq
    skeleton.events same

private theorem atomicRelationData_ext
    {skeleton : EventGraph.Skeleton α}
    {left right : AtomicRelationData skeleton}
    (writeTail :
      left.writeTail = right.writeTail)
    (sourceId :
      left.sourceId = right.sourceId) :
    left = right := by
  rcases left with
    ⟨leftTail, leftNodup, leftExact,
      leftSource, leftSpec, leftAdjacent⟩
  rcases right with
    ⟨rightTail, rightNodup, rightExact,
      rightSource, rightSpec, rightAdjacent⟩
  simp only at writeTail sourceId
  subst rightTail
  subst rightSource
  rfl

private theorem serialize_associationValid
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {entry : EventId × EventId}
    (member : entry ∈ (serialize data).readSources) :
    associationValid skeleton data.writeTail entry = true := by
  obtain ⟨target, targetMember, selected⟩ :=
    List.mem_filterMap.mp member
  cases chosen : data.sourceId target.id with
  | none =>
      simp [serializedSource?, chosen] at selected
  | some sourceId =>
      simp [serializedSource?, chosen] at selected
      subst entry
      have description :=
        data.sourceSpec target targetMember
      cases readShape : target.readValue with
      | none =>
          rw [readShape] at description
          rw [description] at chosen
          contradiction
      | some value =>
          rw [readShape] at description
          obtain
            ⟨source, sourceMember, sourceWrites,
              actualChosen⟩ :=
            description
          have sameSourceId :
              sourceId = source.id :=
            Option.some.inj
              (chosen.symm.trans actualChosen)
          subst sourceId
          have targetFound :=
            findEvent?_member skeleton targetMember
          have sourceFound :=
            findEvent?_member skeleton sourceMember
          simp only [associationValid]
          simp only [targetFound, sourceFound]
          rw [readShape]
          cases rmwCheck : isRMW target with
          | false =>
              simp [sourceWrites]
          | true =>
              have targetRMW :
                  target.IsRMW :=
                (isRMW_eq_true_iff target).mp rmwCheck
              have logicalAdjacency :
                  IdAdjacent source.id target.id
                    (0 :: data.writeTail) :=
                data.rmwAdjacent
                  sourceMember targetMember actualChosen
                  targetRMW
              have adjacencyChecked :
                  adjacent source.id target.id
                      (0 :: data.writeTail) =
                    true :=
                adjacent_eq_true_iff.mpr logicalAdjacency
              simp [sourceWrites, adjacencyChecked]

/--
Every existing canonical relation-data value has an accepted finite raw
serialization.
-/
theorem validate_serialize
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    validate skeleton (serialize data) = true := by
  unfold validate
  rw [Bool.and_eq_true]
  refine
    ⟨(nodup_eq_true_iff data.writeTail).mpr
        data.writeTailNodup,
      ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · apply
      (covers_eq_true_iff
        (nonInitialWriteIds skeleton)
        data.writeTail).mpr
    intro eventId
    exact
      (mem_nonInitialWriteIds_iff skeleton eventId).trans
        (data.writeTailExact eventId).symm
  · rw [Bool.and_eq_true]
    refine
      ⟨(nodup_eq_true_iff
          ((serialize data).readSources.map Prod.fst)).mpr
          (serialize_targetIds_nodup data),
        ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply
        (covers_eq_true_iff
          (readIds skeleton)
          ((serialize data).readSources.map Prod.fst)).mpr
      intro eventId
      exact
        (mem_readIds_iff skeleton eventId).trans
          (mem_serialize_targetIds_iff data eventId).symm
    · apply List.all_eq_true.mpr
      intro entry member
      exact serialize_associationValid data member

/-- Canonical serialization makes the optional conversion succeed. -/
theorem check?_serialize_isSome
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    (check? skeleton (serialize data)).isSome = true :=
  (check?_isSome_iff skeleton (serialize data)).mpr
    (validate_serialize data)

/-- Canonical serialization produces an `AtomicRelationData` certificate. -/
theorem check?_serialize
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) :
    ∃ checked : AtomicRelationData skeleton,
      check? skeleton (serialize data) = some checked := by
  have accepted :=
    check?_serialize_isSome data
  cases result :
      check? skeleton (serialize data) with
  | none =>
      simp [result] at accepted
  | some checked =>
      exact ⟨checked, rfl⟩

/--
Any certificate reconstructed from canonical serialization preserves the
original write order and every carrier-relevant reads-from choice.
-/
theorem check?_serialize_preserves
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {checked : AtomicRelationData skeleton}
    (accepted :
      check? skeleton (serialize data) = some checked) :
    checked.writeTail = data.writeTail ∧
      ∀ target,
        target ∈ skeleton.events →
        checked.sourceId target.id =
          data.sourceId target.id := by
  have sound :=
    check?_sound skeleton (serialize data) accepted
  refine ⟨?_, ?_⟩
  · simpa [serialize] using sound.2.1
  · intro target targetMember
    rw [sound.2.2.1]
    exact sourceFor_serialize_of_mem data targetMember

/--
Every certificate reconstructed from a serialized input is canonical: its
total `sourceId` function is exactly its own finite serialized lookup.
-/
theorem check?_serialize_result_canonical
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {checked : AtomicRelationData skeleton}
    (accepted :
      check? skeleton (serialize data) = some checked) :
    Canonical checked := by
  have sound :=
    check?_sound skeleton (serialize data) accepted
  have preserved :=
    check?_serialize_preserves data accepted
  have sameReadSources :
      (serialize checked).readSources =
        (serialize data).readSources :=
    serializedReadSources_eq_of_sourceId_eq
      preserved.2
  unfold Canonical
  rw [sameReadSources]
  exact sound.2.2.1

/--
Canonical relation data is an exact fixed point of finite serialization and
checking, including all proof fields by structure extensionality and proof
irrelevance.
-/
theorem check?_serialize_eq_some
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (canonical : Canonical data) :
    check? skeleton (serialize data) = some data := by
  obtain ⟨checked, accepted⟩ :=
    check?_serialize data
  have sound :=
    check?_sound skeleton (serialize data) accepted
  have sameWriteTail :
      checked.writeTail = data.writeTail := by
    simpa [serialize] using sound.2.1
  have sameSourceId :
      checked.sourceId = data.sourceId :=
    sound.2.2.1.trans canonical.symm
  have sameData :
      checked = data :=
    atomicRelationData_ext sameWriteTail sameSourceId
  simpa [sameData] using accepted

end RelationDataCheck

end WeakMemory.TreiberRC11
