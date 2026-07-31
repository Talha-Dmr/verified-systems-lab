import WeakMemory.MSQueueSourceHeadPrefixReadiness
import WeakMemory.MSQueueSourceReplay

namespace WeakMemory.MSQueue.Source.Structural

/-!
# The strict Head/Tail gap behind a successful dequeue

A successful dequeue Head CAS comes from a same-attempt snapshot whose Head
and Tail observations differ.  This module relates that source fact to the
canonical scheduled-record prefix.
-/

namespace AtomSchedule

/-- A final `filterMap` output comes from an exact input whose remaining
suffix emits no further outputs. -/
private theorem exists_source_of_filterMap_getLast?
    {Input Output : Type}
    {extract : Input → Option Output}
    {items : List Input}
    {value : Output}
    (last : (items.filterMap extract).getLast? = some value) :
    ∃ leading item trailing,
      items = leading ++ item :: trailing ∧
        extract item = some value ∧
        trailing.filterMap extract = [] := by
  induction items with
  | nil => simp at last
  | cons head rest inductionHypothesis =>
      cases projected : extract head with
      | none =>
          simp only [List.filterMap_cons, projected] at last
          obtain ⟨leading, item, trailing, restShape,
              itemSelected, trailingEmpty⟩ :=
            inductionHypothesis last
          exact ⟨head :: leading, item, trailing,
            by simp [restShape], itemSelected, trailingEmpty⟩
      | some output =>
          cases restShape : rest.filterMap extract with
          | nil =>
              simp [projected, restShape] at last
              subst output
              exact ⟨[], head, rest, rfl, projected, restShape⟩
          | cons next later =>
              have restLast :
                  (rest.filterMap extract).getLast? = some value := by
                simpa [projected, restShape] using last
              obtain ⟨leading, item, trailing, inputShape,
                  itemSelected, trailingEmpty⟩ :=
                inductionHypothesis restLast
              exact ⟨head :: leading, item, trailing,
                by simp [inputShape], itemSelected, trailingEmpty⟩

/-- Record order inside an exact focus prefix remains point order in the
complete atom schedule. -/
private theorem idBefore_of_recordsBefore_pair_sublist
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (focus : Record Value)
    {first second : Record Value}
    (ordered :
      [first, second].Sublist (schedule.recordsBefore focus)) :
    MultiLocationRC11.IdBefore
      first.point second.point schedule.ids := by
  have mapped :
      [first.point, second.point].Sublist
        ((schedule.recordsBefore focus).map Record.point) := by
    simpa using ordered.map Record.point
  have prefixPoints := schedule.recordsOn_take_points_sublist
    (schedule.ids.idxOf focus.point)
  have mappedPrefix :
      ((schedule.recordsBefore focus).map Record.point).Sublist
        (schedule.ids.take (schedule.ids.idxOf focus.point)) := by
    simpa [AtomSchedule.recordsBefore] using prefixPoints
  have pairInSchedule :
      [first.point, second.point].Sublist schedule.ids :=
    mapped.trans (mappedPrefix.trans (List.take_sublist _ _))
  exact MultiLocationRC11.IdBefore.of_pair_sublist
    schedule.idsNodup pairInSchedule

/-- Invert one successful Tail projection. -/
private theorem action_eq_advanceTail_of_tailMove?_eq_some
    {Value : Type}
    {record : Record Value}
    {expected desired : NodeId}
    (selected :
      Prefix.Record.tailMove? record = some (expected, desired)) :
    record.action = .advanceTail expected desired := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;>
    simp [Prefix.Record.tailMove?] at selected ⊢
  exact selected

/-- The successful Head attempt exposes its exact Tail read, the latest Tail
write seen by that read, and the Head write which was already visible before
the Tail read. -/
theorem advanceHead_snapshotOrigins
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {expected desired : NodeId}
    {dequeued : Value}
    (actionShape :
      record.action = .advanceHead expected desired dequeued) :
    ∃ tailRead source observedTail,
      expected ≠ observedTail ∧
        LatestSource schedule source tailRead ∧
        MultiLocationRC11.IdBefore
          tailRead.id record.point schedule.ids ∧
        ((source = tailInitializer dummy ∧ dummy = observedTail) ∨
          ∃ earlier previous,
            earlier ∈ structuralRecords trace ∧
              earlier.action = .advanceTail previous observedTail ∧
              earlier.pointAtom = source) ∧
        (expected = dummy ∨
          ∃ earlier previous earlierValue,
            earlier ∈ structuralRecords trace ∧
              earlier.action =
                .advanceHead previous expected earlierValue ∧
              MultiLocationRC11.IdBefore
                earlier.point tailRead.id schedule.ids) := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  have notMalformed :=
    execution.sourceWellFormed.atomic_not_malformedSuccess eventMember
  rcases occurrence with ⟨casId, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueHelpTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueFinishTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHelpTailCAS thread operation sourceExpected sourceDesired
      observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadCAS thread operation sourceExpected sourceDesired value
      observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp only [Action.advanceHead.injEq] at actionShape
          rcases actionShape with ⟨rfl, rfl, rfl⟩
          simp [AtomicAction.IsMalformedSuccess,
            AtomicAction.casView?] at notMalformed
          subst observed
          obtain ⟨headLoadId, tailLoadId, nextLoadId, validationId,
              observedTail, different, headTailPO, tailNextPO,
              nextValidationPO, validationCASPO⟩ :=
            execution.dequeueHeadSuccess_programOrder eventMember
          let headRead : MultiLocationRC11.Atom Site Ptr :=
            (⟨headLoadId,
              .dequeueHeadLoad thread operation (.node sourceExpected)⟩ :
                AtomicOccurrence Value).toRC11Atom
          let tailRead : MultiLocationRC11.Atom Site Ptr :=
            (⟨tailLoadId,
              .dequeueTailLoad thread operation (.node observedTail)⟩ :
                AtomicOccurrence Value).toRC11Atom
          obtain ⟨headSource, headRF, headOrigin⟩ :=
            headNodeRead_hasOrigin execution headTailPO.closed.1 rfl rfl
          obtain ⟨tailSource, tailRF, tailOrigin⟩ :=
            tailNodeRead_hasOrigin execution tailNextPO.closed.1 rfl rfl
          have tailReadBeforeCAS :
              MultiLocationRC11.IdBefore
                tailRead.id casId schedule.ids := by
            exact MultiLocationRC11.IdBefore.transitive
              (schedule.respectsProgramOrder tailNextPO)
              (MultiLocationRC11.IdBefore.transitive
                (schedule.respectsProgramOrder nextValidationPO)
                (schedule.respectsProgramOrder validationCASPO))
          refine ⟨tailRead, tailSource, observedTail, different,
            schedule.latestSource_of_readsFrom tailRF,
            by simpa [tailRead] using tailReadBeforeCAS,
            tailOrigin, ?_⟩
          rcases headOrigin with initializer |
              ⟨earlier, previous, earlierValue, earlierMember,
                earlierShape, earlierExact⟩
          · exact Or.inl initializer.2.symm
          · right
            refine ⟨earlier, previous, earlierValue, earlierMember,
              earlierShape, ?_⟩
            have sourceBeforeHead := schedule.readsFrom_before headRF
            rw [← earlierExact] at sourceBeforeHead
            exact MultiLocationRC11.IdBefore.transitive
              (by simpa [headRead] using sourceBeforeHead)
              (by simpa [headRead, tailRead, AtomSchedule.ids] using
                schedule.respectsProgramOrder headTailPO)

/-- Replay evidence upgrades the source-level nonempty snapshot to the exact
strict Head/Tail count gap in the canonical focus prefix. -/
theorem advanceHeadBeforeGap
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    {dequeued : Value}
    (actionShape :
      focus.action = .advanceHead expected desired dequeued)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus))
    (replayed : Replay (Chain.State.initial dummy)
      (schedule.recordsBefore focus)
      (Prefix.stateOf dummy (schedule.recordsBefore focus))) :
    (Prefix.headMoves (schedule.recordsBefore focus)).length <
      (Prefix.tailMoves (schedule.recordsBefore focus)).length := by
  let before := schedule.recordsBefore focus
  let headCount := (Prefix.headMoves before).length
  let tailCount := (Prefix.tailMoves before).length
  change headCount < tailCount
  by_cases strict : headCount < tailCount
  · exact strict
  exfalso
  have countsEqual : headCount = tailCount := by
    have headLeTail := represented.headBeforeTail
    change headCount ≤ tailCount at headLeTail
    omega
  have expectedNode :
      (Prefix.stateOf dummy before).nodes[headCount]? = some expected := by
    exact schedule.advanceHeadBefore_expectedNode
      focusMember actionShape represented
  obtain ⟨tailRead, source, observedTail, different, latest,
      tailReadBeforeFocus, tailOrigin, headOrigin⟩ :=
    schedule.advanceHead_snapshotOrigins focusMember actionShape
  rcases headOrigin with expectedRooted |
      ⟨priorHead, previousHead, priorValue, priorHeadMember,
        priorHeadShape, priorHeadBeforeRead⟩
  · have rootAt :
        (Prefix.stateOf dummy before).nodes[0]? = some dummy := rfl
    have stateNodesNodup :
        (Prefix.stateOf dummy before).nodes.Nodup := by
      simpa [Prefix.stateOf] using represented.nodesNodup
    have zeroBound :
        0 < (Prefix.stateOf dummy before).nodes.length := by
      simp [Prefix.stateOf]
    have headZero : headCount = 0 := by
      rw [expectedRooted] at expectedNode
      have zeroEqHead : 0 = headCount :=
        (List.getElem?_inj zeroBound stateNodesNodup).mp
          (rootAt.trans expectedNode.symm)
      exact zeroEqHead.symm
    have tailZero : tailCount = 0 := by omega
    rcases tailOrigin with initializer |
        ⟨priorTail, previousTail, priorTailMember,
          priorTailShape, priorTailExact⟩
    · exact different (expectedRooted.trans initializer.2)
    · have priorTailBeforeFocus :
          MultiLocationRC11.IdBefore
            priorTail.point focus.point schedule.ids := by
        have sourceBeforeRead := latest.sourceBefore
        rw [← priorTailExact] at sourceBeforeRead
        exact MultiLocationRC11.IdBefore.transitive
          (by simpa using sourceBeforeRead) tailReadBeforeFocus
      have priorTailInBefore : priorTail ∈ before :=
        (schedule.mem_recordsBefore_iff
          focusMember priorTailMember).2 priorTailBeforeFocus
      have moveMember := Prefix.tailMove_mem_of_record
        priorTailInBefore priorTailShape
      have tailPositive : 0 < tailCount := by
        change 0 < (Prefix.tailMoves before).length
        exact List.length_pos_of_mem moveMember
      omega
  · have priorHeadBeforeFocus :
        MultiLocationRC11.IdBefore
          priorHead.point focus.point schedule.ids :=
      MultiLocationRC11.IdBefore.transitive
        priorHeadBeforeRead tailReadBeforeFocus
    have priorHeadInBefore : priorHead ∈ before :=
      (schedule.mem_recordsBefore_iff
        focusMember priorHeadMember).2 priorHeadBeforeFocus
    obtain ⟨leading, trailing, beforeShape⟩ :=
      List.mem_iff_append.mp priorHeadInBefore
    have priorGap :
        (Prefix.headMoves leading).length <
          (Prefix.tailMoves leading).length := by
      apply replayed.advanceHead_prefixGap beforeShape
      exact priorHeadShape
    let priorEdge : Prefix.Edge Value :=
      ⟨previousHead, expected, priorValue⟩
    have priorHeadAt :
        (Prefix.headMoves before)[(Prefix.headMoves leading).length]? =
          some priorEdge := by
      rw [beforeShape]
      simp [Prefix.headMoves,
        (Prefix.Record.projections_of_advanceHead priorHeadShape).2.2,
        priorEdge]
    have priorIndexBound :
        (Prefix.headMoves leading).length < headCount := by
      change (Prefix.headMoves leading).length <
        (Prefix.headMoves before).length
      exact (List.getElem?_eq_some_iff.mp priorHeadAt).1
    have priorEdgeAtLinks :
        (Prefix.links before)[(Prefix.headMoves leading).length]? =
          some priorEdge := by
      rw [← List.getElem?_take_of_lt priorIndexBound]
      rw [← represented.headExact]
      exact priorHeadAt
    obtain ⟨_previousAt, expectedAt, _payloadAt⟩ :=
      represented.edgeAt_state priorEdgeAtLinks
    have stateNodesNodup :
        (Prefix.stateOf dummy before).nodes.Nodup := by
      simpa [Prefix.stateOf] using represented.nodesNodup
    have priorChildBound :
        (Prefix.headMoves leading).length + 1 <
          (Prefix.stateOf dummy before).nodes.length :=
      (List.getElem?_eq_some_iff.mp expectedAt).1
    have priorIndexShape :
        (Prefix.headMoves leading).length + 1 = headCount :=
      (List.getElem?_inj priorChildBound stateNodesNodup).mp
        (expectedAt.trans expectedNode.symm)
    have tailMovesDecomposition :
        Prefix.tailMoves before =
          Prefix.tailMoves leading ++ Prefix.tailMoves trailing := by
      rw [beforeShape]
      simp [Prefix.tailMoves,
        (Prefix.Record.projections_of_advanceHead priorHeadShape).2.1]
    have leadingTailLe :
        (Prefix.tailMoves leading).length ≤ tailCount := by
      change (Prefix.tailMoves leading).length ≤
        (Prefix.tailMoves before).length
      rw [tailMovesDecomposition]
      simp
    have leadingTailCount :
        (Prefix.tailMoves leading).length = tailCount := by
      omega
    have trailingTailEmpty : Prefix.tailMoves trailing = [] := by
      apply List.length_eq_zero_iff.mp
      have decompositionLengths := congrArg List.length tailMovesDecomposition
      simp only [List.length_append] at decompositionLengths
      omega
    have everyTailBeforeRead :
        ∀ tailRecord ∈ before,
          ∀ tailExpected tailDesired,
            tailRecord.action =
                .advanceTail tailExpected tailDesired →
              MultiLocationRC11.IdBefore
                tailRecord.point tailRead.id schedule.ids := by
      intro tailRecord tailRecordBefore tailExpected tailDesired
        tailRecordShape
      have tailRecordLocation : tailRecord ∈ leading := by
        rw [beforeShape] at tailRecordBefore
        rcases List.mem_append.mp tailRecordBefore with
          inLeading | inPriorTrailing
        · exact inLeading
        · rcases List.mem_cons.mp inPriorTrailing with
            samePrior | inTrailing
          · subst tailRecord
            simp [priorHeadShape] at tailRecordShape
          · have moveInTrailing := Prefix.tailMove_mem_of_record
              inTrailing tailRecordShape
            rw [trailingTailEmpty] at moveInTrailing
            simp at moveInTrailing
      have tailBeforePrior :
          MultiLocationRC11.IdBefore
            tailRecord.point priorHead.point schedule.ids := by
        apply schedule.idBefore_of_recordsBefore_pair_sublist focus
        change [tailRecord, priorHead].Sublist before
        obtain ⟨tailLeading, tailTrailing, leadingShape⟩ :=
          List.mem_iff_append.mp tailRecordLocation
        rw [beforeShape, leadingShape]
        simpa [List.append_assoc] using
          ((List.nil_sublist tailLeading).append
            (List.Sublist.cons_cons tailRecord
              ((List.nil_sublist tailTrailing).append
                (List.Sublist.cons_cons priorHead
                  (List.nil_sublist trailing)))))
      exact MultiLocationRC11.IdBefore.transitive
        tailBeforePrior priorHeadBeforeRead
    have finalIndexBeforeTail :
        (Prefix.headMoves leading).length < tailCount := by
      omega
    have finalLinkInTake :
        ((Prefix.links before).take tailCount)[
            (Prefix.headMoves leading).length]? = some priorEdge := by
      rw [List.getElem?_take_of_lt finalIndexBeforeTail]
      exact priorEdgeAtLinks
    have finalTailMoveAt :
        (Prefix.tailMoves before)[
            (Prefix.headMoves leading).length]? =
          some (previousHead, expected) := by
      rw [represented.tailExact]
      change
        (((Prefix.links before).take tailCount).map fun edge =>
          (edge.owner, edge.child))[
            (Prefix.headMoves leading).length]? =
          some (previousHead, expected)
      rw [List.getElem?_map, finalLinkInTake]
      rfl
    have finalIndexShape :
        tailCount - 1 = (Prefix.headMoves leading).length := by
      omega
    have expectedTailLast :
        (Prefix.tailMoves before).getLast? =
          some (previousHead, expected) := by
      rw [List.getLast?_eq_getElem?]
      change (Prefix.tailMoves before)[tailCount - 1]? = _
      rw [finalIndexShape]
      exact finalTailMoveAt
    rcases tailOrigin with initializer |
        ⟨priorTail, previousTail, priorTailMember,
          priorTailShape, priorTailExact⟩
    · have leadingTailPositive :
          0 < (Prefix.tailMoves leading).length := by
        omega
      obtain ⟨move, moveMember⟩ :=
        List.exists_mem_of_length_pos leadingTailPositive
      obtain ⟨tailRecord, tailRecordInLeading, tailRecordSelected⟩ :=
        List.mem_filterMap.mp moveMember
      rcases move with ⟨tailExpected, tailDesired⟩
      have tailRecordShape :
          tailRecord.action = .advanceTail tailExpected tailDesired :=
        action_eq_advanceTail_of_tailMove?_eq_some tailRecordSelected
      have tailRecordInBefore : tailRecord ∈ before := by
        rw [beforeShape]
        simp [tailRecordInLeading]
      have tailRecordMember : tailRecord ∈ structuralRecords trace :=
        mem_structuralRecords_of_mem_recordsOn tailRecordInBefore
      have tailRMW : tailRecord.pointAtom.IsRMW :=
        pointAtom_isRMW_of_structuralRecord tailRecordMember (by
          simp [tailRecordShape, Action.IsCAS])
      have tailWrite : tailRecord.pointAtom.IsWrite :=
        (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW tailRMW).1
      have tailNeSource : tailRecord.pointAtom ≠ source := by
        intro same
        have notInitial :=
          (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW tailRMW).2
        apply notInitial
        rw [same, initializer.1]
        trivial
      have initializerAt :
          execution.candidate.InitializerAt source.location source := by
        rw [initializer.1]
        exact tailInitializer_at execution
      have sourceSite : source.location = .tail := by
        rw [initializer.1]
        rfl
      have tailRecordAtSource :
          tailRecord.pointAtom.location = source.location := by
        calc
          tailRecord.pointAtom.location = tailRecord.action.site :=
            pointAtom_location tailRecordMember
          _ = .tail := by simp [tailRecordShape, Action.site]
          _ = source.location := sourceSite.symm
      have sourceBeforeTail :
          MultiLocationRC11.MO execution.candidate
            source tailRecord.pointAtom := by
        refine ⟨initializerAt.1,
          pointAtom_mem_candidate (execution := execution) tailRecordMember,
          ?_, tailWrite, ?_, ?_⟩
        · rw [initializer.1]
          trivial
        · exact tailRecordAtSource.symm
        · exact execution.valid.initializerFirst initializerAt
            (pointAtom_mem_candidate
              (execution := execution) tailRecordMember)
            tailRecordAtSource
            tailWrite tailNeSource
      have tailBeforeRead := everyTailBeforeRead tailRecord
        tailRecordInBefore tailExpected tailDesired tailRecordShape
      exact latest.noLaterBefore sourceBeforeTail
        (by simpa using tailBeforeRead)
    · have priorTailBeforeFocus :
          MultiLocationRC11.IdBefore
            priorTail.point focus.point schedule.ids := by
        have sourceBeforeRead := latest.sourceBefore
        rw [← priorTailExact] at sourceBeforeRead
        exact MultiLocationRC11.IdBefore.transitive
          (by simpa using sourceBeforeRead) tailReadBeforeFocus
      have priorTailInBefore : priorTail ∈ before :=
        (schedule.mem_recordsBefore_iff
          focusMember priorTailMember).2 priorTailBeforeFocus
      obtain ⟨tailLeading, tailTrailing, tailFactor⟩ :=
        List.mem_iff_append.mp priorTailInBefore
      have tailTrailingNone :
          ∀ later ∈ tailTrailing,
            Prefix.Record.tailMove? later = none := by
        intro later laterInTrailing
        by_cases selectedNone : Prefix.Record.tailMove? later = none
        · exact selectedNone
        · exfalso
          obtain ⟨laterMove, laterSelected⟩ :=
            Option.ne_none_iff_exists'.mp selectedNone
          rcases laterMove with ⟨laterExpected, laterDesired⟩
          have laterShape :
              later.action =
                .advanceTail laterExpected laterDesired :=
            action_eq_advanceTail_of_tailMove?_eq_some laterSelected
          have laterInBefore : later ∈ before := by
            rw [tailFactor]
            simp [laterInTrailing]
          have laterMember : later ∈ structuralRecords trace :=
            mem_structuralRecords_of_mem_recordsOn laterInBefore
          have priorBeforeLater :
              MultiLocationRC11.IdBefore
                priorTail.point later.point schedule.ids := by
            apply schedule.idBefore_of_recordsBefore_pair_sublist focus
            change [priorTail, later].Sublist before
            rw [tailFactor]
            exact (List.nil_sublist tailLeading).append
              (List.Sublist.cons_cons priorTail
                (List.singleton_sublist.mpr laterInTrailing))
          have laterRMW : later.pointAtom.IsRMW :=
            pointAtom_isRMW_of_structuralRecord laterMember (by
              simp [laterShape, Action.IsCAS])
          have laterWrite : later.pointAtom.IsWrite :=
            (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW laterRMW).1
          have sameLocation :
              later.pointAtom.location = tailRead.location := by
            have sourceSite : source.location = .tail := by
              rw [← priorTailExact]
              calc
                priorTail.pointAtom.location = priorTail.action.site :=
                  pointAtom_location priorTailMember
                _ = .tail := by simp [priorTailShape, Action.site]
            calc
              later.pointAtom.location = later.action.site :=
                pointAtom_location laterMember
              _ = .tail := by simp [laterShape, Action.site]
              _ = tailRead.location :=
                sourceSite.symm.trans latest.readsFrom.sameLocation
          have laterBeforeRead := everyTailBeforeRead later laterInBefore
            laterExpected laterDesired laterShape
          rcases schedule.rfSource_latest_before latest.readsFrom
              (pointAtom_mem_candidate (execution := execution) laterMember)
              laterWrite sameLocation (by simpa using laterBeforeRead) with
            same | laterBeforeSource
          · have sameAtom : later.pointAtom = priorTail.pointAtom :=
              same.trans priorTailExact.symm
            have samePoint : later.point = priorTail.point := by
              simpa using congrArg MultiLocationRC11.Atom.id sameAtom
            rw [samePoint] at priorBeforeLater
            exact MultiLocationRC11.IdBefore.irreflexive priorBeforeLater
          · have laterBeforePrior :=
              schedule.modificationOrder_before laterBeforeSource
            rw [← priorTailExact] at laterBeforePrior
            have cycle := MultiLocationRC11.IdBefore.transitive
              priorBeforeLater (by simpa using laterBeforePrior)
            exact MultiLocationRC11.IdBefore.irreflexive cycle
      have trailingMovesEmpty : Prefix.tailMoves tailTrailing = [] :=
        List.filterMap_eq_nil_iff.mpr tailTrailingNone
      have observedTailLast :
          (Prefix.tailMoves before).getLast? =
            some (previousTail, observedTail) := by
        have priorProjection :=
          (Prefix.Record.projections_of_advanceTail priorTailShape).2.1
        rw [tailFactor, Prefix.tailMoves_append]
        rw [show Prefix.tailMoves (priorTail :: tailTrailing) =
          (previousTail, observedTail) :: Prefix.tailMoves tailTrailing by
            simp [Prefix.tailMoves, priorProjection]]
        rw [trailingMovesEmpty]
        simp
      have pairEqual :
          (previousHead, expected) =
            (previousTail, observedTail) :=
        Option.some.inj (expectedTailLast.symm.trans observedTailLast)
      exact different (congrArg Prod.snd pairEqual)

/-- Replay and the source snapshot discharge the strict gap automatically,
yielding readiness and invariant preservation for a successful Head move. -/
theorem advanceHeadBeforeAppliesAndPreservesExact
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    {dequeued : Value}
    (actionShape :
      focus.action = .advanceHead expected desired dequeued)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus))
    (replayed : Replay (Chain.State.initial dummy)
      (schedule.recordsBefore focus)
      (Prefix.stateOf dummy (schedule.recordsBefore focus))) :
    focus.Applies
        (Prefix.stateOf dummy (schedule.recordsBefore focus))
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus ++ [focus])) ∧
      Prefix.Rep dummy (schedule.recordsBefore focus ++ [focus]) := by
  apply schedule.advanceHeadBeforeAppliesAndPreserves
    focusMember actionShape represented
  exact schedule.advanceHeadBeforeGap
    focusMember actionShape represented replayed

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
