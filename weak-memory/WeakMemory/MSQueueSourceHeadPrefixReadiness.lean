import WeakMemory.MSQueueSourcePrefixReadiness
import WeakMemory.MSQueueSourcePayload

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Head-advance readiness at an exact schedule prefix

This layer identifies the exact permanent edge consumed by a successful
Head CAS.  RMW atomicity makes the CAS's RF source the last earlier Head
write; the canonical prefix representation then turns that source value into
the next link index.
-/

namespace AtomSchedule

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
  have prefixPoints :=
    schedule.recordsOn_take_points_sublist
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

/-- Inversion of the Head projection used below to rule out a selected
record in a suffix. -/
private theorem action_eq_advanceHead_of_headMove?_eq_some
    {Value : Type}
    {record : Record Value}
    {edge : Prefix.Edge Value}
    (selected : Prefix.Record.headMove? record = some edge) :
    record.action =
      .advanceHead edge.owner edge.child edge.payload := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;>
    simp [Prefix.Record.headMove?] at selected ⊢
  cases selected
  simp

/-- Every earlier Head move is either the current CAS's RF source or is
modification-order earlier than that source. -/
private theorem priorHeadWrite_eq_source_or_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus prior : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {focusExpected focusDesired : NodeId}
    {focusValue : Value}
    (focusShape :
      focus.action =
        .advanceHead focusExpected focusDesired focusValue)
    (priorMember : prior ∈ structuralRecords trace)
    {expected desired : NodeId}
    {value : Value}
    (priorShape : prior.action = .advanceHead expected desired value)
    (priorBefore : prior ∈ schedule.recordsBefore focus)
    {source : MultiLocationRC11.Atom Site Ptr}
    (latest : LatestSource schedule source focus.pointAtom) :
    prior.pointAtom = source ∨
      MultiLocationRC11.MO execution.candidate prior.pointAtom source := by
  have priorRMW : prior.pointAtom.IsRMW :=
    pointAtom_isRMW_of_structuralRecord priorMember (by
      simp [priorShape, Action.IsCAS])
  have priorWrite : prior.pointAtom.IsWrite :=
    (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW priorRMW).1
  have sameLocation :
      prior.pointAtom.location = focus.pointAtom.location := by
    calc
      prior.pointAtom.location = prior.action.site :=
        pointAtom_location priorMember
      _ = .head := by simp [priorShape, Action.site]
      _ = focus.pointAtom.location := by
        simpa [focusShape, Action.site] using
          (pointAtom_location focusMember).symm
  apply schedule.rfSource_latest_before latest.readsFrom
    (pointAtom_mem_candidate (execution := execution) priorMember)
    priorWrite sameLocation
  simpa [Record.pointAtom, Record.pointOccurrence,
    AtomicOccurrence.toRC11Atom, priorShape, focusShape] using
    ((schedule.mem_recordsBefore_iff focusMember priorMember).1
      priorBefore)

/-- The exact RF predecessor of a Head CAS determines the current Head node
in the represented focus prefix. -/
theorem advanceHeadBefore_expectedNode
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
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    (Prefix.stateOf dummy (schedule.recordsBefore focus)).nodes[
        (Prefix.headMoves (schedule.recordsBefore focus)).length]? =
      some expected := by
  let before := schedule.recordsBefore focus
  change (Prefix.stateOf dummy before).nodes[
      (Prefix.headMoves before).length]? = some expected
  obtain ⟨source, latest, _immediate, origin⟩ :=
    schedule.headImmediateOrigin focusMember actionShape
  rcases origin with initializer | ⟨prior, previous, priorValue,
      priorMember, priorShape, priorExact⟩
  · have noHeadMoves : Prefix.headMoves before = [] := by
      rw [Prefix.headMoves, List.filterMap_eq_nil_iff]
      intro record recordBefore
      by_cases selectedNone : Prefix.Record.headMove? record = none
      · exact selectedNone
      exfalso
      obtain ⟨edge, selected⟩ := Option.ne_none_iff_exists'.mp
        selectedNone
      have recordShape :=
        action_eq_advanceHead_of_headMove?_eq_some selected
      have recordMember : record ∈ structuralRecords trace :=
        mem_structuralRecords_of_mem_recordsOn recordBefore
      have recordRMW : record.pointAtom.IsRMW :=
        pointAtom_isRMW_of_structuralRecord recordMember (by
          simp [recordShape, Action.IsCAS])
      have recordNoninitial :=
        MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW recordRMW
      have recordWrite : record.pointAtom.IsWrite := recordNoninitial.1
      have recordNeInitializer :
          record.pointAtom ≠ headInitializer dummy := by
        intro same
        have initial : record.pointAtom.IsInitial := by
          rw [same]
          trivial
        exact recordNoninitial.2 initial
      have recordLocation : record.pointAtom.location = .head := by
        calc
          record.pointAtom.location = record.action.site :=
            pointAtom_location recordMember
          _ = .head := by simp [recordShape, Action.site]
      have initializerAt := headInitializer_at execution
      have initializerBeforeRecord :
          MultiLocationRC11.MO execution.candidate
            (headInitializer dummy) record.pointAtom := by
        refine ⟨initializerAt.1,
          pointAtom_mem_candidate (execution := execution) recordMember,
          ?_, recordWrite, ?_, ?_⟩
        · trivial
        · simpa [headInitializer] using recordLocation.symm
        · exact execution.valid.toWellFormed.initializerFirst
            initializerAt
            (pointAtom_mem_candidate (execution := execution) recordMember)
            recordLocation recordWrite recordNeInitializer
      have recordBeforeFocus :
          MultiLocationRC11.IdBefore
            record.point focus.point schedule.ids :=
        (schedule.mem_recordsBefore_iff focusMember recordMember).1
          recordBefore
      rw [initializer.1] at latest
      exact latest.noLaterBefore initializerBeforeRecord (by
        simpa using recordBeforeFocus)
    have expectedIsDummy : expected = dummy := initializer.2.symm
    subst expected
    simp [Prefix.stateOf, noHeadMoves]
  · have priorBeforeFocus :
        MultiLocationRC11.IdBefore
          prior.point focus.point schedule.ids := by
      have sourceBefore := latest.sourceBefore
      rw [← priorExact] at sourceBefore
      simpa using sourceBefore
    have priorBefore : prior ∈ before :=
      (schedule.mem_recordsBefore_iff focusMember priorMember).2
        priorBeforeFocus
    obtain ⟨leading, trailing, beforeShape, _priorNotLeading⟩ :=
      List.eq_append_cons_of_mem priorBefore
    have trailingNoHead : Prefix.headMoves trailing = [] := by
      rw [Prefix.headMoves, List.filterMap_eq_nil_iff]
      intro record recordTrailing
      by_cases selectedNone : Prefix.Record.headMove? record = none
      · exact selectedNone
      exfalso
      obtain ⟨edge, selected⟩ := Option.ne_none_iff_exists'.mp
        selectedNone
      have recordShape :=
        action_eq_advanceHead_of_headMove?_eq_some selected
      have recordBefore : record ∈ before := by
        rw [beforeShape]
        simp [recordTrailing]
      have recordMember : record ∈ structuralRecords trace :=
        mem_structuralRecords_of_mem_recordsOn recordBefore
      have priorThenRecord : [prior, record].Sublist before := by
        rw [beforeShape]
        exact List.sublist_append_of_sublist_right
          (List.Sublist.cons_cons prior
            (List.singleton_sublist.mpr recordTrailing))
      have priorPointBeforeRecord :=
        schedule.idBefore_of_recordsBefore_pair_sublist focus
          priorThenRecord
      rcases schedule.priorHeadWrite_eq_source_or_before
          focusMember actionShape recordMember recordShape recordBefore
          latest with sameSource | recordBeforeSource
      · have samePoint : record.point = prior.point := by
          have sameId := congrArg MultiLocationRC11.Atom.id
            (sameSource.trans priorExact.symm)
          simpa [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, recordShape, priorShape] using
              sameId
        rw [samePoint] at priorPointBeforeRecord
        exact MultiLocationRC11.IdBefore.irreflexive
          priorPointBeforeRecord
      · have recordPointBeforePrior :=
          schedule.modificationOrder_before recordBeforeSource
        rw [← priorExact] at recordPointBeforePrior
        have cycle := MultiLocationRC11.IdBefore.transitive
          priorPointBeforeRecord (by
            simpa using recordPointBeforePrior)
        exact MultiLocationRC11.IdBefore.irreflexive cycle
    have headMovesShape :
        Prefix.headMoves before =
          Prefix.headMoves leading ++
            [⟨previous, expected, priorValue⟩] := by
      have priorProjection :=
        (Prefix.Record.projections_of_advanceHead priorShape).2.2
      rw [beforeShape, Prefix.headMoves_append]
      rw [show prior :: trailing = [prior] ++ trailing by rfl,
        Prefix.headMoves_append]
      have singletonShape :
          Prefix.headMoves [prior] =
            [⟨previous, expected, priorValue⟩] := by
        simp [Prefix.headMoves, priorProjection]
      rw [singletonShape, trailingNoHead]
      simp
    have headPositive : 0 < (Prefix.headMoves before).length := by
      rw [headMovesShape]
      simp
    have previousEdgeAtHead :
        (Prefix.headMoves before)[
          (Prefix.headMoves before).length - 1]? =
            some ⟨previous, expected, priorValue⟩ := by
      rw [headMovesShape]
      simp
    have previousEdgeAtLinks :
        (Prefix.links before)[
          (Prefix.headMoves before).length - 1]? =
            some ⟨previous, expected, priorValue⟩ := by
      rw [← List.getElem?_take_of_lt (by omega :
        (Prefix.headMoves before).length - 1 <
          (Prefix.headMoves before).length)]
      rw [← represented.headExact]
      exact previousEdgeAtHead
    obtain ⟨_previousAt, expectedAt, _payloadAt⟩ :=
      represented.edgeAt_state previousEdgeAtLinks
    have indexShape :
        (Prefix.headMoves before).length - 1 + 1 =
          (Prefix.headMoves before).length := by
      omega
    simpa [before, indexShape] using expectedAt

/-- Exact link-index readiness for a successful Head CAS at its strict
schedule prefix, including the non-atomic payload value recovered from source
publication. -/
theorem advanceHeadBefore_nextEdge
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
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    (Prefix.links (schedule.recordsBefore focus))[
        (Prefix.headMoves (schedule.recordsBefore focus)).length]? =
      some ⟨expected, desired, dequeued⟩ := by
  obtain ⟨link, linkMember, linkShape, linkBeforeFocus⟩ :=
    schedule.advanceHeadRecord_has_exactPayloadLink
      focusMember actionShape
  have linkBefore : link ∈ schedule.recordsBefore focus :=
    (schedule.mem_recordsBefore_iff focusMember linkMember).2
      linkBeforeFocus
  have edgeMember :
      (⟨expected, desired, dequeued⟩ : Prefix.Edge Value) ∈
        Prefix.links (schedule.recordsBefore focus) :=
    Prefix.edge_mem_links_of_record linkBefore linkShape
  obtain ⟨index, edgeAt⟩ := List.mem_iff_getElem?.mp edgeMember
  have indexBound :
      index < (Prefix.links (schedule.recordsBefore focus)).length :=
    (List.getElem?_eq_some_iff.mp edgeAt).1
  have ownerAtIndex := (represented.edgeAt_state edgeAt).1
  have ownerAtHead := schedule.advanceHeadBefore_expectedNode
    focusMember actionShape represented
  have headBound :
      (Prefix.headMoves (schedule.recordsBefore focus)).length <
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus)).nodes.length := by
    simp only [Prefix.stateOf, List.length_cons, List.length_map]
    have headBeforeTail := represented.headBeforeTail
    have tailBound := represented.tailBound
    omega
  have indexAsNodeBound :
      index <
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus)).nodes.length := by
    simp only [Prefix.stateOf, List.length_cons, List.length_map]
    omega
  have sameIndex :
      index =
        (Prefix.headMoves (schedule.recordsBefore focus)).length := by
    exact (List.getElem?_inj indexAsNodeBound represented.nodesNodup).mp
      (ownerAtIndex.trans ownerAtHead.symm)
  simpa [sameIndex] using edgeAt

/-- Once the source-level nonempty snapshot supplies the strict Head/Tail
gap, the exact edge above is precisely the readiness certificate required by
canonical replay.  The gap is separated here so its independent source
snapshot proof can import this module without a cycle. -/
theorem advanceHeadBeforeAppliesAndPreserves
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
    (headBeforeTail :
      (Prefix.headMoves (schedule.recordsBefore focus)).length <
        (Prefix.tailMoves (schedule.recordsBefore focus)).length) :
    focus.Applies
        (Prefix.stateOf dummy (schedule.recordsBefore focus))
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus ++ [focus])) ∧
      Prefix.Rep dummy (schedule.recordsBefore focus ++ [focus]) := by
  have nextEdge := schedule.advanceHeadBefore_nextEdge
    focusMember actionShape represented
  exact ⟨represented.advanceHeadApplies focus actionShape
      nextEdge headBeforeTail,
    represented.snocAdvanceHead focus actionShape
      nextEdge headBeforeTail⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
