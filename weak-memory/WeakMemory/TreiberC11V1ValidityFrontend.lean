import WeakMemory.TreiberC11V1RelationFrontend

namespace WeakMemory.TreiberC11V1.RelationFrontend

/-!
# Independent RC11 validity refinement

This module transports the semantic consistency conditions of the independent
`TreiberC11V1.RC11` model to the target graph.  In particular, target
`CoreConsistent` is derived from independent no-thin-air and coherence; it
does not use `ClientCompatibleOrder` or a preselected relation schedule.
-/

namespace Projection

private theorem independentReleaseSequence_members
    {candidate : RC11.Candidate α}
    {head source : RC11.Atom α}
    (sequence : RC11.ReleaseSequence candidate head source) :
    head ∈ candidate.atoms ∧ source ∈ candidate.atoms := by
  induction sequence with
  | head member =>
      exact ⟨member, member⟩
  | rmw previousSequence immediate isRMW inductionHypothesis =>
      exact ⟨inductionHypothesis.1, immediate.2.1⟩

private theorem exists_write_atom_of_id_mem_writeOrder
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate)
    {eventId : EventId}
    (member : eventId ∈ candidate.writeOrder) :
    ∃ atom,
      atom ∈ candidate.atoms ∧
        atom.id = eventId ∧
        atom.IsWrite := by
  change eventId ∈ 0 :: candidate.modificationOrder at member
  simp only [List.mem_cons] at member
  rcases member with eventIdZero | inTail
  · subst eventId
    exact
      ⟨.initial,
        by simp [RC11.Candidate.atoms],
        rfl,
        ⟨.null, rfl⟩⟩
  · obtain ⟨atom, atomMember, atomId, atomWrites, _⟩ :=
      (valid.writeTailExact eventId).mp inTail
    exact ⟨atom, atomMember, atomId, atomWrites⟩

/--
Immediate modification is preserved and reflected by the exact carrier and
modification-order projection.
-/
theorem immediateModification_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.ImmediateModification
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.ImmediateMO candidate source target := by
  let data := projection.toAtomicRelationData valid
  constructor
  · intro immediate
    have independentOrder :
        RC11.MO candidate source target :=
      (projection.modificationOrder_iff valid
        sourceMember targetMember).mp immediate.2.2.1
    have targetWrites :=
      data.modificationOrderWrites immediate.2.2.1
    refine
      ⟨sourceMember, targetMember,
        (projection.isWrite_iff sourceMember).mp targetWrites.1,
        (projection.isWrite_iff targetMember).mp targetWrites.2,
        independentOrder.2.2, ?_⟩
    intro middle between
    obtain ⟨middleAtom, middleMember, middleId, middleWrites⟩ :=
      exists_write_atom_of_id_mem_writeOrder
        valid between.1.2.1
    have sourceBeforeMiddle :
        RC11.MO candidate source middleAtom :=
      ⟨sourceMember, middleMember, by
        simpa [middleId] using between.1⟩
    have middleBeforeTarget :
        RC11.MO candidate middleAtom target :=
      ⟨middleMember, targetMember, by
        simpa [middleId] using between.2⟩
    exact immediate.2.2.2
      (projection.toEvent middleAtom)
      (projection.toEvent_mem middleMember)
      ((projection.isWrite_iff middleMember).mpr middleWrites)
      ⟨
        (projection.modificationOrder_iff valid
          sourceMember middleMember).mpr sourceBeforeMiddle,
        (projection.modificationOrder_iff valid
          middleMember targetMember).mpr middleBeforeTarget⟩
  · intro immediate
    obtain
      ⟨_, _, _sourceWrites, _targetWrites, adjacent⟩ :=
      immediate
    refine
      ⟨projection.toEvent_mem sourceMember,
        projection.toEvent_mem targetMember,
        (projection.modificationOrder_iff valid
          sourceMember targetMember).mpr
            ⟨sourceMember, targetMember, adjacent.1⟩,
        ?_⟩
    intro middleEvent middleEventMember middleEventWrites
    obtain ⟨middle, middleMember, middleShape⟩ :=
      projection.exists_atom_of_mem middleEventMember
    subst middleEvent
    intro between
    have sourceBeforeMiddle :
        RC11.MO candidate source middle :=
      (projection.modificationOrder_iff valid
        sourceMember middleMember).mp between.1
    have middleBeforeTarget :
        RC11.MO candidate middle target :=
      (projection.modificationOrder_iff valid
        middleMember targetMember).mp between.2
    exact adjacent.2 middle.id
      ⟨sourceBeforeMiddle.2.2,
        middleBeforeTarget.2.2⟩

/-- Independent release sequences map to target release sequences. -/
theorem releaseSequence_preserved
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {head source : RC11.Atom α}
    (sequence : RC11.ReleaseSequence candidate head source) :
    (projection.toAtomicRelationData valid).graph.ReleaseSequence
      (projection.toEvent head)
      (projection.toEvent source) := by
  induction sequence with
  | head member =>
      exact .head (projection.toEvent_mem member)
  | @rmw previous next previousSequence immediate isRMW
      inductionHypothesis =>
      exact .rmw inductionHypothesis
        ((projection.immediateModification_iff valid
          immediate.1 immediate.2.1).mpr immediate)
        ((projection.isRMW_iff next immediate.2.1).mpr isRMW)

/--
Every target release sequence has an independent preimage on the exact
projected carrier.
-/
theorem releaseSequence_has_preimage
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {headEvent sourceEvent : TreiberRC11.Event α}
    (sequence :
      (projection.toAtomicRelationData valid).graph.ReleaseSequence
        headEvent sourceEvent) :
    ∃ head source,
      head ∈ candidate.atoms ∧
        source ∈ candidate.atoms ∧
        projection.toEvent head = headEvent ∧
        projection.toEvent source = sourceEvent ∧
        RC11.ReleaseSequence candidate head source := by
  induction sequence with
  | head member =>
      obtain ⟨atom, atomMember, atomShape⟩ :=
        projection.exists_atom_of_mem member
      exact
        ⟨atom, atom, atomMember, atomMember,
          atomShape, atomShape, .head atomMember⟩
  | @rmw previous next previousSequence immediate isRMW
      inductionHypothesis =>
      obtain
        ⟨head, previousAtom, headMember, previousMember,
          headShape, previousShape, independentSequence⟩ :=
        inductionHypothesis
      obtain ⟨nextAtom, nextMember, nextShape⟩ :=
        projection.exists_atom_of_mem immediate.2.1
      have projectedImmediate :
          (projection.toAtomicRelationData valid).graph.ImmediateModification
            (projection.toEvent previousAtom)
            (projection.toEvent nextAtom) := by
        simpa [previousShape, nextShape] using immediate
      have independentImmediate :
          RC11.ImmediateMO candidate previousAtom nextAtom :=
        (projection.immediateModification_iff valid
          previousMember nextMember).mp projectedImmediate
      have independentRMW :
          nextAtom.IsRMW := by
        apply (projection.isRMW_iff nextAtom nextMember).mp
        simpa [nextShape] using isRMW
      exact
        ⟨head, nextAtom, headMember, nextMember,
          headShape, nextShape,
          .rmw independentSequence independentImmediate
            independentRMW⟩

/-- Release sequences are exact on projected atoms. -/
theorem releaseSequence_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {head source : RC11.Atom α}
    (headMember : head ∈ candidate.atoms)
    (sourceMember : source ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.ReleaseSequence
        (projection.toEvent head)
        (projection.toEvent source) ↔
      RC11.ReleaseSequence candidate head source := by
  constructor
  · intro sequence
    obtain
      ⟨actualHead, actualSource, actualHeadMember,
        actualSourceMember, headShape, sourceShape,
        independentSequence⟩ :=
      projection.releaseSequence_has_preimage valid sequence
    have headExact :
        actualHead = head :=
      projection.injectiveOn
        actualHeadMember headMember headShape
    have sourceExact :
        actualSource = source :=
      projection.injectiveOn
        actualSourceMember sourceMember sourceShape
    simpa [headExact, sourceExact] using independentSequence
  · exact projection.releaseSequence_preserved valid

/-- Independent synchronization maps to target synchronization. -/
theorem synchronizesWith_preserved
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {release acquire : RC11.Atom α}
    (synchronizesWith : RC11.SW candidate release acquire) :
    (projection.toAtomicRelationData valid).graph.synchronizesWith
      (projection.toEvent release)
      (projection.toEvent acquire) := by
  obtain
    ⟨source, sequence, readsFrom, releaseOrder, acquireOrder⟩ :=
    synchronizesWith
  have sequenceMembers :=
    independentReleaseSequence_members sequence
  exact
    ⟨projection.toEvent source,
      projection.releaseSequence_preserved valid sequence,
      (projection.readsFrom_iff valid
        readsFrom.1 readsFrom.2.1).mpr readsFrom,
      by simpa [projection.order_eq release sequenceMembers.1]
        using releaseOrder,
      by simpa [projection.order_eq acquire readsFrom.2.1]
        using acquireOrder⟩

/--
Every target synchronizes-with edge has an independent preimage.
-/
theorem synchronizesWith_has_preimage
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {releaseEvent acquireEvent : TreiberRC11.Event α}
    (synchronizesWith :
      (projection.toAtomicRelationData valid).graph.synchronizesWith
        releaseEvent acquireEvent) :
    ∃ release acquire,
      release ∈ candidate.atoms ∧
        acquire ∈ candidate.atoms ∧
        projection.toEvent release = releaseEvent ∧
        projection.toEvent acquire = acquireEvent ∧
        RC11.SW candidate release acquire := by
  obtain
    ⟨sourceEvent, sequence, readsFrom,
      releaseOrder, acquireOrder⟩ :=
    synchronizesWith
  obtain
    ⟨release, source, releaseMember, sourceMember,
      releaseShape, sourceShape, independentSequence⟩ :=
    projection.releaseSequence_has_preimage valid sequence
  have acquireMember :
      acquireEvent ∈ skeleton.events :=
    (projection.toAtomicRelationData valid
      |>.readsFromClosed readsFrom).2
  obtain ⟨acquire, acquireAtomMember, acquireShape⟩ :=
    projection.exists_atom_of_mem acquireMember
  have projectedReadsFrom :
      (projection.toAtomicRelationData valid).graph.readsFrom
        (projection.toEvent source)
        (projection.toEvent acquire) := by
    simpa [sourceShape, acquireShape] using readsFrom
  have independentReadsFrom :
      RC11.RF candidate source acquire :=
    (projection.readsFrom_iff valid
      sourceMember acquireAtomMember).mp projectedReadsFrom
  refine
    ⟨release, acquire, releaseMember, acquireAtomMember,
      releaseShape, acquireShape,
      ⟨source, independentSequence, independentReadsFrom,
        ?_, ?_⟩⟩
  · simpa [← releaseShape,
      projection.order_eq release releaseMember] using releaseOrder
  · simpa [← acquireShape,
      projection.order_eq acquire acquireAtomMember] using acquireOrder

/-- Synchronizes-with is exact on projected atoms. -/
theorem synchronizesWith_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {release acquire : RC11.Atom α}
    (releaseMember : release ∈ candidate.atoms)
    (acquireMember : acquire ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.synchronizesWith
        (projection.toEvent release)
        (projection.toEvent acquire) ↔
      RC11.SW candidate release acquire := by
  constructor
  · intro edge
    obtain
      ⟨actualRelease, actualAcquire, actualReleaseMember,
        actualAcquireMember, releaseShape, acquireShape,
        independentEdge⟩ :=
      projection.synchronizesWith_has_preimage valid edge
    have releaseExact :
        actualRelease = release :=
      projection.injectiveOn actualReleaseMember
        releaseMember releaseShape
    have acquireExact :
        actualAcquire = acquire :=
      projection.injectiveOn actualAcquireMember
        acquireMember acquireShape
    simpa [releaseExact, acquireExact] using independentEdge
  · exact projection.synchronizesWith_preserved valid

/-- Independent happens-before maps to target happens-before. -/
theorem happensBefore_preserved
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (edge : RC11.HB candidate source target) :
    (projection.toAtomicRelationData valid).graph.HappensBefore
      (projection.toEvent source)
      (projection.toEvent target) := by
  induction edge with
  | programOrder programOrder =>
      exact .programOrder
        ((projection.graphProgramOrder_iff valid
          programOrder.1 programOrder.2.1).mpr programOrder)
  | synchronizesWith synchronizesWith =>
      exact .synchronizesWith
        (projection.synchronizesWith_preserved valid synchronizesWith)
  | transitive first second firstMapped secondMapped =>
      exact .transitive firstMapped secondMapped

/-- Every target happens-before path has an independent preimage. -/
theorem happensBefore_has_preimage
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {sourceEvent targetEvent : TreiberRC11.Event α}
    (edge :
      (projection.toAtomicRelationData valid).graph.HappensBefore
        sourceEvent targetEvent) :
    ∃ source target,
      source ∈ candidate.atoms ∧
        target ∈ candidate.atoms ∧
        projection.toEvent source = sourceEvent ∧
        projection.toEvent target = targetEvent ∧
        RC11.HB candidate source target := by
  let data := projection.toAtomicRelationData valid
  induction edge with
  | @programOrder sourceEvent targetEvent programOrder =>
      have endpoints :
          sourceEvent ∈ skeleton.events ∧
            targetEvent ∈ skeleton.events :=
        skeleton.programOrderClosed
          data.readsFrom data.modificationOrder programOrder
      obtain ⟨source, sourceMember, sourceShape⟩ :=
        projection.exists_atom_of_mem endpoints.1
      obtain ⟨target, targetMember, targetShape⟩ :=
        projection.exists_atom_of_mem endpoints.2
      subst sourceEvent
      subst targetEvent
      exact
        ⟨source, target, sourceMember, targetMember,
          rfl, rfl,
          .programOrder
            ((projection.graphProgramOrder_iff valid
              sourceMember targetMember).mp programOrder)⟩
  | @synchronizesWith sourceEvent targetEvent synchronizesWith =>
      obtain
        ⟨source, target, sourceMember, targetMember,
          sourceShape, targetShape, independentEdge⟩ :=
        projection.synchronizesWith_has_preimage
          valid synchronizesWith
      exact
        ⟨source, target, sourceMember, targetMember,
          sourceShape, targetShape,
          .synchronizesWith independentEdge⟩
  | @transitive firstEvent middleEvent lastEvent
      firstEdge secondEdge firstPreimage secondPreimage =>
      obtain
        ⟨first, firstMiddle, firstMember, firstMiddleMember,
          firstShape, firstMiddleShape, firstIndependent⟩ :=
        firstPreimage
      obtain
        ⟨secondMiddle, last, secondMiddleMember, lastMember,
          secondMiddleShape, lastShape, secondIndependent⟩ :=
        secondPreimage
      have sameMiddle :
          firstMiddle = secondMiddle :=
        projection.injectiveOn
          firstMiddleMember secondMiddleMember
          (firstMiddleShape.trans secondMiddleShape.symm)
      subst secondMiddle
      exact
        ⟨first, last, firstMember, lastMember,
          firstShape, lastShape,
          .transitive firstIndependent secondIndependent⟩

/-- Happens-before is exact on projected atoms. -/
theorem happensBefore_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.HappensBefore
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.HB candidate source target := by
  constructor
  · intro edge
    obtain
      ⟨actualSource, actualTarget, actualSourceMember,
        actualTargetMember, sourceShape, targetShape,
        independentEdge⟩ :=
      projection.happensBefore_has_preimage valid edge
    have sourceExact :
        actualSource = source :=
      projection.injectiveOn actualSourceMember
        sourceMember sourceShape
    have targetExact :
        actualTarget = target :=
      projection.injectiveOn actualTargetMember
        targetMember targetShape
    simpa [sourceExact, targetExact] using independentEdge
  · exact projection.happensBefore_preserved valid

/-- Independent causal order maps to target causal order. -/
theorem causalOrder_preserved
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (edge : RC11.CausalOrder candidate source target) :
    (projection.toAtomicRelationData valid).graph.CausalOrder
      (projection.toEvent source)
      (projection.toEvent target) := by
  induction edge with
  | programOrder programOrder =>
      exact .programOrder
        ((projection.graphProgramOrder_iff valid
          programOrder.1 programOrder.2.1).mpr programOrder)
  | readsFrom readsFrom =>
      exact .readsFrom
        ((projection.readsFrom_iff valid
          readsFrom.1 readsFrom.2.1).mpr readsFrom)
  | transitive first second firstMapped secondMapped =>
      exact .transitive firstMapped secondMapped

/-- Every target causal-order path has an independent preimage. -/
theorem causalOrder_has_preimage
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {sourceEvent targetEvent : TreiberRC11.Event α}
    (edge :
      (projection.toAtomicRelationData valid).graph.CausalOrder
        sourceEvent targetEvent) :
    ∃ source target,
      source ∈ candidate.atoms ∧
        target ∈ candidate.atoms ∧
        projection.toEvent source = sourceEvent ∧
        projection.toEvent target = targetEvent ∧
        RC11.CausalOrder candidate source target := by
  let data := projection.toAtomicRelationData valid
  induction edge with
  | @programOrder sourceEvent targetEvent programOrder =>
      have endpoints :
          sourceEvent ∈ skeleton.events ∧
            targetEvent ∈ skeleton.events :=
        skeleton.programOrderClosed
          data.readsFrom data.modificationOrder programOrder
      obtain ⟨source, sourceMember, sourceShape⟩ :=
        projection.exists_atom_of_mem endpoints.1
      obtain ⟨target, targetMember, targetShape⟩ :=
        projection.exists_atom_of_mem endpoints.2
      subst sourceEvent
      subst targetEvent
      exact
        ⟨source, target, sourceMember, targetMember,
          rfl, rfl,
          .programOrder
            ((projection.graphProgramOrder_iff valid
              sourceMember targetMember).mp programOrder)⟩
  | @readsFrom sourceEvent targetEvent readsFrom =>
      have endpoints := data.readsFromClosed readsFrom
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
  | @transitive firstEvent middleEvent lastEvent
      firstEdge secondEdge firstPreimage secondPreimage =>
      obtain
        ⟨first, firstMiddle, firstMember, firstMiddleMember,
          firstShape, firstMiddleShape, firstIndependent⟩ :=
        firstPreimage
      obtain
        ⟨secondMiddle, last, secondMiddleMember, lastMember,
          secondMiddleShape, lastShape, secondIndependent⟩ :=
        secondPreimage
      have sameMiddle :
          firstMiddle = secondMiddle :=
        projection.injectiveOn
          firstMiddleMember secondMiddleMember
          (firstMiddleShape.trans secondMiddleShape.symm)
      subst secondMiddle
      exact
        ⟨first, last, firstMember, lastMember,
          firstShape, lastShape,
          .transitive firstIndependent secondIndependent⟩

/-- Causal order is exact on projected atoms. -/
theorem causalOrder_iff
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate)
    {source target : RC11.Atom α}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms) :
    (projection.toAtomicRelationData valid).graph.CausalOrder
        (projection.toEvent source)
        (projection.toEvent target) ↔
      RC11.CausalOrder candidate source target := by
  constructor
  · intro edge
    obtain
      ⟨actualSource, actualTarget, actualSourceMember,
        actualTargetMember, sourceShape, targetShape,
        independentEdge⟩ :=
      projection.causalOrder_has_preimage valid edge
    have sourceExact :
        actualSource = source :=
      projection.injectiveOn actualSourceMember
        sourceMember sourceShape
    have targetExact :
        actualTarget = target :=
      projection.injectiveOn actualTargetMember
        targetMember targetShape
    simpa [sourceExact, targetExact] using independentEdge
  · exact projection.causalOrder_preserved valid

/-- Independent no-thin-air directly implies target no-thin-air. -/
theorem noThinAir_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.Acyclic
      (projection.toAtomicRelationData valid).graph.CausalOrder := by
  intro event cycle
  obtain
    ⟨source, target, sourceMember, targetMember,
      sourceShape, targetShape, independentCycle⟩ :=
    projection.causalOrder_has_preimage valid cycle
  have sameAtom :
      source = target :=
    projection.injectiveOn sourceMember targetMember
      (sourceShape.trans targetShape.symm)
  subst target
  exact valid.noThinAir source independentCycle

/-- Independent coherence directly implies target coherence. -/
theorem coherent_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    (projection.toAtomicRelationData valid).graph.Coherent := by
  intro sourceEvent middleEvent happensBefore
  obtain
    ⟨source, middle, sourceMember, middleMember,
      sourceShape, middleShape, independentHB⟩ :=
    projection.happensBefore_has_preimage valid happensBefore
  have independentCoherence :=
    valid.coherence independentHB
  constructor
  · intro sameEvent
    apply independentCoherence.1
    exact projection.injectiveOn sourceMember middleMember
      (sourceShape.trans (sameEvent.trans middleShape.symm))
  · intro targetECO
    obtain
      ⟨actualMiddle, actualSource,
        actualMiddleMember, actualSourceMember,
        actualMiddleShape, actualSourceShape,
        independentECO⟩ :=
      projection.eco_has_preimage valid targetECO
    have middleExact :
        actualMiddle = middle :=
      projection.injectiveOn
        actualMiddleMember middleMember
        (actualMiddleShape.trans middleShape.symm)
    have sourceExact :
        actualSource = source :=
      projection.injectiveOn
        actualSourceMember sourceMember
        (actualSourceShape.trans sourceShape.symm)
    exact independentCoherence.2
      (by simpa [middleExact, sourceExact] using independentECO)

/--
All target well-formedness fields follow from the exact relation projection
and independent coherence.  No schedule is used.
-/
theorem wellFormed_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.WellFormed
      (projection.toAtomicRelationData valid).graph := by
  let data := projection.toAtomicRelationData valid
  let remaining := projection.remainingWellFormed valid
  have coherent :
      data.graph.Coherent :=
    projection.coherent_of_rc11 valid
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
      TreiberRC11.happensBeforeAcyclic_of_coherent coherent
  }

/--
Target core consistency is a semantic consequence of independent RC11
validity, with no `ClientCompatibleOrder` or schedule premise.
-/
theorem coreConsistent_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    TreiberRC11.CoreConsistent
      (projection.toAtomicRelationData valid).graph where
  toWellFormed :=
    projection.wellFormed_of_rc11 valid
  noThinAir :=
    projection.noThinAir_of_rc11 valid
  coherence :=
    projection.coherent_of_rc11 valid

/-- Independent RC11 validity also yields target scheduling acyclicity. -/
theorem orderAcyclic_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    (projection.toAtomicRelationData valid).graph.OrderAcyclic :=
  (projection.coreConsistent_of_rc11 valid).orderAcyclic

/-- A finite respecting target schedule exists by topological sorting. -/
theorem exists_respectsGraph_of_rc11
    {candidate : RC11.Candidate α}
    {skeleton : TreiberRC11.EventGraph.Skeleton α}
    (projection : Projection candidate skeleton)
    (valid : RC11.Valid candidate) :
    ∃ schedule,
      TreiberRC11.RespectsGraph
        (projection.toAtomicRelationData valid).graph schedule :=
  TreiberRC11.exists_respectsGraph_of_orderAcyclic
    (projection.wellFormed_of_rc11 valid)
    (projection.orderAcyclic_of_rc11 valid)

end Projection

end WeakMemory.TreiberC11V1.RelationFrontend

namespace WeakMemory.TreiberC11V1.SupportedExecution

/--
The concrete projected graph is core-consistent directly from the independent
RC11 validity certificate.
-/
theorem relationData_coreConsistent_of_rc11
    (execution : SupportedExecution α) :
    TreiberRC11.CoreConsistent execution.relationData.graph :=
  execution.relationProjection.coreConsistent_of_rc11 execution.rc11

/-- The concrete projected graph has an acyclic replay-order relation. -/
theorem relationData_orderAcyclic_of_rc11
    (execution : SupportedExecution α) :
    execution.relationData.graph.OrderAcyclic :=
  execution.relationProjection.orderAcyclic_of_rc11 execution.rc11

/-- The independent validity certificate yields some respecting target schedule. -/
theorem exists_relationSchedule_of_rc11
    (execution : SupportedExecution α) :
    ∃ schedule,
      TreiberRC11.RespectsGraph execution.relationData.graph schedule :=
  execution.relationProjection.exists_respectsGraph_of_rc11 execution.rc11

end WeakMemory.TreiberC11V1.SupportedExecution
