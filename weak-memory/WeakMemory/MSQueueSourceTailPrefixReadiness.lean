import WeakMemory.MSQueueSourcePrefixReadiness

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Tail-advance readiness at an exact schedule prefix

This layer identifies the abstract Tail position represented by all structural
records strictly before one successful Tail CAS.  RMW adjacency makes the
CAS's RF source the last earlier Tail write; the prefix invariant then turns
that source into the next permanent link edge.
-/

namespace AtomSchedule

/-- Record order inside an exact focus prefix is still record-point order in
the complete atom schedule. -/
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
    mapped.trans (mappedPrefix.trans
      (List.take_sublist _ _))
  exact MultiLocationRC11.IdBefore.of_pair_sublist
    schedule.idsNodup pairInSchedule

/-- A Tail-advance point already scheduled before `focus` is either the
focus's RF source or is modification-order earlier than that source. -/
private theorem priorTailWrite_eq_source_or_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus prior : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {focusExpected focusDesired : NodeId}
    (focusShape :
      focus.action = .advanceTail focusExpected focusDesired)
    (priorMember : prior ∈ structuralRecords trace)
    {expected desired : NodeId}
    (priorShape : prior.action = .advanceTail expected desired)
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
      _ = .tail := by simp [priorShape, Action.site]
      _ = focus.pointAtom.location := by
        simpa [focusShape, Action.site] using
          (pointAtom_location focusMember).symm
  exact schedule.rfSource_latest_before latest.readsFrom
    (pointAtom_mem_candidate (execution := execution) priorMember)
    priorWrite sameLocation
    (by simpa using
      ((schedule.mem_recordsBefore_iff focusMember priorMember).1
        priorBefore))

/-- If the successful Tail CAS reads directly from the static initializer,
no successful Tail swing can occur in its strict schedule prefix. -/
private theorem tailMoves_recordsBefore_eq_nil_of_initializer
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    (focusShape : focus.action = .advanceTail expected desired)
    {source : MultiLocationRC11.Atom Site Ptr}
    (latest : LatestSource schedule source focus.pointAtom)
    (sourceShape : source = tailInitializer dummy) :
    Prefix.tailMoves (schedule.recordsBefore focus) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro prior priorBefore
  have priorMember : prior ∈ structuralRecords trace :=
    mem_structuralRecords_of_mem_recordsOn priorBefore
  rcases prior with ⟨occurrence, point, validation, action⟩
  cases action with
  | link owner child payload => rfl
  | advanceTail priorExpected priorDesired =>
      exfalso
      let prior : Record Value :=
        ⟨occurrence, point, validation,
          .advanceTail priorExpected priorDesired⟩
      have priorShape :
          prior.action = .advanceTail priorExpected priorDesired := rfl
      have priorRMW : prior.pointAtom.IsRMW :=
        pointAtom_isRMW_of_structuralRecord priorMember (by
          simp [priorShape, Action.IsCAS])
      have priorNotInitial : ¬ prior.pointAtom.IsInitial :=
        (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW priorRMW).2
      have priorNeSource : prior.pointAtom ≠ source := by
        intro same
        apply priorNotInitial
        rw [same, sourceShape]
        trivial
      rcases schedule.priorTailWrite_eq_source_or_before
          focusMember focusShape priorMember priorShape priorBefore latest with
        same | priorMO
      · exact priorNeSource same
      · have initializerAt :
            execution.candidate.InitializerAt source.location source := by
          rw [sourceShape]
          exact tailInitializer_at execution
        have initializerBefore :=
          execution.valid.toWellFormed.initializerFirst initializerAt
            (pointAtom_mem_candidate (execution := execution) priorMember)
            priorMO.sameLocation
            (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW priorRMW).1
            priorNeSource
        have priorBeforeSource := priorMO.2.2.2.2.2
        rw [priorMO.sameLocation] at priorBeforeSource
        exact (Nat.lt_asymm priorBeforeSource.2.2
          initializerBefore.2.2).elim
  | advanceHead priorExpected priorDesired payload => rfl
  | empty head => rfl

/-- If the Tail CAS reads from an earlier successful Tail swing, that swing
is the final Tail move in the exact structural focus prefix. -/
private theorem tailMoves_recordsBefore_getLast?_of_structuralSource
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    (focusShape : focus.action = .advanceTail expected desired)
    {source : MultiLocationRC11.Atom Site Ptr}
    (latest : LatestSource schedule source focus.pointAtom)
    {earlier : Record Value}
    {previous : NodeId}
    (earlierMember : earlier ∈ structuralRecords trace)
    (earlierShape : earlier.action = .advanceTail previous expected)
    (earlierExact : earlier.pointAtom = source) :
    (Prefix.tailMoves (schedule.recordsBefore focus)).getLast? =
      some (previous, expected) := by
  have earlierBeforeFocus :
      MultiLocationRC11.IdBefore
        earlier.point focus.point schedule.ids := by
    have sourceBefore := latest.sourceBefore
    rw [← earlierExact] at sourceBefore
    simpa using sourceBefore
  have earlierInPrefix : earlier ∈ schedule.recordsBefore focus :=
    (schedule.mem_recordsBefore_iff focusMember earlierMember).2
      earlierBeforeFocus
  obtain ⟨before, after, prefixShape⟩ :=
    List.mem_iff_append.mp earlierInPrefix
  have afterNone :
      ∀ prior ∈ after, Prefix.Record.tailMove? prior = none := by
    intro prior priorAfter
    have priorBefore : prior ∈ schedule.recordsBefore focus := by
      rw [prefixShape]
      simp [priorAfter]
    have priorMember : prior ∈ structuralRecords trace :=
      mem_structuralRecords_of_mem_recordsOn priorBefore
    rcases prior with ⟨occurrence, point, validation, action⟩
    cases action with
    | link owner child payload => rfl
    | advanceTail priorExpected priorDesired =>
        exfalso
        let prior : Record Value :=
          ⟨occurrence, point, validation,
            .advanceTail priorExpected priorDesired⟩
        have priorShape :
            prior.action = .advanceTail priorExpected priorDesired := rfl
        have ordered :
            [earlier, prior].Sublist (schedule.recordsBefore focus) := by
          rw [prefixShape]
          exact (List.nil_sublist before).append
            (List.Sublist.cons_cons earlier
              (List.singleton_sublist.mpr priorAfter))
        have earlierBeforePrior :=
          schedule.idBefore_of_recordsBefore_pair_sublist focus ordered
        rcases schedule.priorTailWrite_eq_source_or_before
            focusMember focusShape priorMember priorShape priorBefore latest with
          same | priorMO
        · have sameAtom : prior.pointAtom = earlier.pointAtom :=
            same.trans earlierExact.symm
          have samePoint : prior.point = earlier.point := by
            simpa using congrArg MultiLocationRC11.Atom.id sameAtom
          rw [samePoint] at earlierBeforePrior
          exact MultiLocationRC11.IdBefore.irreflexive
            earlierBeforePrior
        · have priorBeforeEarlier :=
            schedule.modificationOrder_before priorMO
          rw [← earlierExact] at priorBeforeEarlier
          have cycle := MultiLocationRC11.IdBefore.transitive
            earlierBeforePrior (by simpa using priorBeforeEarlier)
          exact MultiLocationRC11.IdBefore.irreflexive cycle
    | advanceHead priorExpected priorDesired payload => rfl
    | empty head => rfl
  have tailMovesShape :
      Prefix.tailMoves (schedule.recordsBefore focus) =
        Prefix.tailMoves before ++ [(previous, expected)] := by
    rw [prefixShape]
    have afterFilter :
        after.filterMap Prefix.Record.tailMove? = [] :=
      List.filterMap_eq_nil_iff.mpr afterNone
    simp only [Prefix.tailMoves, List.filterMap_append,
      List.filterMap_cons,
      (Prefix.Record.projections_of_advanceTail earlierShape).2.1,
      afterFilter]
  rw [tailMovesShape]
  simp

/-- The last represented Tail move determines the node at the canonical Tail
index. -/
private theorem tailNode_of_tailMoves_getLast?
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    (represented : Prefix.Rep dummy records)
    {previous node : NodeId}
    (lastMove :
      (Prefix.tailMoves records).getLast? = some (previous, node)) :
    (Prefix.stateOf dummy records).nodes[
        (Prefix.tailMoves records).length]? = some node := by
  have tailNonempty : Prefix.tailMoves records ≠ [] := by
    intro empty
    rw [empty] at lastMove
    simp at lastMove
  have tailPositive : 0 < (Prefix.tailMoves records).length :=
    List.length_pos_iff.mpr tailNonempty
  have mappedLast :
      (((Prefix.links records).take
          (Prefix.tailMoves records).length).map
        fun edge => (edge.owner, edge.child)).getLast? =
          some (previous, node) := by
    rw [← represented.tailExact]
    exact lastMove
  rw [List.getLast?_map] at mappedLast
  cases edgeLast :
      ((Prefix.links records).take
        (Prefix.tailMoves records).length).getLast? with
  | none => simp [edgeLast] at mappedLast
  | some edge =>
      have edgePair :
          (edge.owner, edge.child) = (previous, node) := by
        simpa [edgeLast] using mappedLast
      have edgeIndexBound :
          (Prefix.tailMoves records).length - 1 <
            (Prefix.links records).length := by
        have tailBound := represented.tailBound
        omega
      have edgeAt :
          (Prefix.links records)[
              (Prefix.tailMoves records).length - 1]? = some edge := by
        have exactLast := edgeLast
        rw [List.getLast?_take,
          if_neg (Nat.ne_of_gt tailPositive),
          List.getElem?_eq_getElem edgeIndexBound] at exactLast
        simp only [Option.some_or] at exactLast
        exact List.getElem?_eq_some_iff.mpr
          ⟨edgeIndexBound, Option.some.inj exactLast⟩
      obtain ⟨_ownerAt, childAt, _payloadAt⟩ :=
        represented.edgeAt_state edgeAt
      have childShape : edge.child = node :=
        congrArg Prod.snd edgePair
      rw [childShape] at childAt
      have indexShape :
          (Prefix.tailMoves records).length - 1 + 1 =
            (Prefix.tailMoves records).length := by
        omega
      rw [indexShape] at childAt
      exact childAt

/-- In a represented prefix, a linked edge whose owner is the current Tail
node is exactly the edge at the Tail index. -/
private theorem nextEdge_of_tailNode_of_mem
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    (represented : Prefix.Rep dummy records)
    {expected desired : NodeId}
    {payload : Value}
    (tailNode :
      (Prefix.stateOf dummy records).nodes[
          (Prefix.tailMoves records).length]? = some expected)
    (edgeMember :
      (⟨expected, desired, payload⟩ : Prefix.Edge Value) ∈
        Prefix.links records) :
    (Prefix.links records)[(Prefix.tailMoves records).length]? =
      some ⟨expected, desired, payload⟩ := by
  obtain ⟨index, edgeAt⟩ := List.mem_iff_getElem?.mp edgeMember
  have edgeIndexBound : index < (Prefix.links records).length :=
    (List.getElem?_eq_some_iff.mp edgeAt).1
  obtain ⟨ownerAt, _childAt, _payloadAt⟩ :=
    represented.edgeAt_state edgeAt
  have tailIndexBound :
      (Prefix.tailMoves records).length <
        (Prefix.stateOf dummy records).nodes.length := by
    simp only [Prefix.stateOf, List.length_cons, List.length_map]
    have tailBound := represented.tailBound
    omega
  have edgeNodeIndexBound :
      index < (Prefix.stateOf dummy records).nodes.length := by
    simp only [Prefix.stateOf, List.length_cons, List.length_map]
    omega
  have sameNode :
      (Prefix.stateOf dummy records).nodes[index]? =
        (Prefix.stateOf dummy records).nodes[
          (Prefix.tailMoves records).length]? :=
    ownerAt.trans tailNode.symm
  have stateNodesNodup :
      (Prefix.stateOf dummy records).nodes.Nodup := by
    simpa [Prefix.stateOf] using represented.nodesNodup
  have indexShape : index = (Prefix.tailMoves records).length :=
    (List.getElem?_inj edgeNodeIndexBound stateNodesNodup).mp sameNode
  simpa [indexShape] using edgeAt

/-- Exact focus-prefix readiness for a successful Tail swing: the permanent
link it traverses is precisely the next edge after all earlier Tail moves. -/
theorem advanceTailBeforeNextEdge
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    (actionShape : focus.action = .advanceTail expected desired)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    ∃ payload,
      (Prefix.links (schedule.recordsBefore focus))[
          (Prefix.tailMoves (schedule.recordsBefore focus)).length]? =
        some (⟨expected, desired, payload⟩ : Prefix.Edge Value) := by
  obtain ⟨link, payload, linkMember, linkShape, linkBefore⟩ :=
    schedule.advanceTailRecord_has_priorLink focusMember actionShape
  have linkInPrefix : link ∈ schedule.recordsBefore focus :=
    (schedule.mem_recordsBefore_iff focusMember linkMember).2 linkBefore
  have edgeMember :
      (⟨expected, desired, payload⟩ : Prefix.Edge Value) ∈
        Prefix.links (schedule.recordsBefore focus) :=
    Prefix.edge_mem_links_of_record linkInPrefix linkShape
  obtain ⟨source, latest, _immediate, origin⟩ :=
    schedule.tailImmediateOrigin focusMember actionShape
  have tailNode :
      (Prefix.stateOf dummy (schedule.recordsBefore focus)).nodes[
          (Prefix.tailMoves (schedule.recordsBefore focus)).length]? =
        some expected := by
    rcases origin with initializer | structural
    · rcases initializer with ⟨sourceShape, dummyShape⟩
      have noTailMoves :=
        schedule.tailMoves_recordsBefore_eq_nil_of_initializer
          focusMember actionShape latest sourceShape
      rw [noTailMoves]
      simp [Prefix.stateOf, dummyShape]
    · rcases structural with
        ⟨earlier, previous, earlierMember, earlierShape, earlierExact⟩
      exact tailNode_of_tailMoves_getLast? represented
        (schedule.tailMoves_recordsBefore_getLast?_of_structuralSource
          focusMember actionShape latest earlierMember earlierShape
            earlierExact)
  exact ⟨payload,
    nextEdge_of_tailNode_of_mem represented tailNode edgeMember⟩

/-- Replay-ready Tail case over the exact focus prefix. -/
theorem advanceTailBeforeAppliesAndPreserves
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {expected desired : NodeId}
    (actionShape : focus.action = .advanceTail expected desired)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    focus.Applies
        (Prefix.stateOf dummy (schedule.recordsBefore focus))
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus ++ [focus])) ∧
      Prefix.Rep dummy (schedule.recordsBefore focus ++ [focus]) := by
  obtain ⟨payload, nextEdge⟩ :=
    schedule.advanceTailBeforeNextEdge focusMember actionShape represented
  exact ⟨represented.advanceTailApplies focus actionShape nextEdge,
    represented.snocAdvanceTail focus actionShape nextEdge⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
