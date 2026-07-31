import WeakMemory.MSQueueSourcePrefixReadiness
import WeakMemory.MSQueueSourceRecordDependencies
import WeakMemory.MSQueueSourceHeadDependencies

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Empty-dequeue readiness at an exact scheduled prefix

An extracted empty action is anchored at the null read of `head.next`, not at
the later validation event.  This layer combines that null-read source with
the same-attempt Head=Tail snapshot to show that the canonical record prefix
is already empty at the anchor.
-/

namespace Prefix

/-- If a represented Head move reaches the final node, Head has consumed the
whole represented link prefix. -/
theorem Rep.headAtEnd_of_move_to_last
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    (represented : Rep dummy records)
    {previous node : NodeId}
    {payload : Value}
    (moveMember :
      (⟨previous, node, payload⟩ : Edge Value) ∈ headMoves records)
    (nodeAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some node) :
    (headMoves records).length = (links records).length := by
  have moveInEdges := moveMember
  rw [represented.headExact] at moveInEdges
  rcases List.mem_take_iff_getElem.mp moveInEdges with
    ⟨index, indexBound, edgeAtIndex⟩
  have edgeAt :
      (links records)[index]? = some ⟨previous, node, payload⟩ :=
    List.getElem?_eq_some_iff.mpr
      ⟨Nat.lt_of_lt_of_le indexBound (Nat.min_le_right _ _),
        edgeAtIndex⟩
  obtain ⟨_ownerAt, childAt, _payloadAt⟩ :=
    represented.edgeAt_state edgeAt
  have lastAt := nodeAtEnd
  rw [List.getLast?_eq_getElem?] at lastAt
  have sameNode :
      (dummy :: (links records).map Edge.child)[index + 1]? =
        (dummy :: (links records).map Edge.child)[
          (links records).length]? :=
    childAt.trans (by simpa using lastAt.symm)
  have firstIndexBound :
      index + 1 <
        (dummy :: (links records).map Edge.child).length := by
    simp only [List.length_cons, List.length_map]
    have indexBeforeHead : index < (headMoves records).length :=
      Nat.lt_of_lt_of_le indexBound (Nat.min_le_left _ _)
    have headBound :
        (headMoves records).length ≤ (links records).length :=
      Nat.le_trans represented.headBeforeTail represented.tailBound
    omega
  have indexAtLast : index + 1 = (links records).length :=
    (List.getElem?_inj firstIndexBound represented.nodesNodup).mp sameNode
  have indexBeforeHead : index < (headMoves records).length :=
    Nat.lt_of_lt_of_le indexBound (Nat.min_le_left _ _)
  have headBound :
      (headMoves records).length ≤ (links records).length :=
    Nat.le_trans represented.headBeforeTail represented.tailBound
  omega

/-- If the permanent dummy is the represented final node, no link or Head
move has occurred. -/
theorem Rep.headAtEnd_of_dummy_at_last
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    (represented : Rep dummy records)
    (dummyAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some dummy) :
    (headMoves records).length = (links records).length := by
  have headAt :
      (dummy :: (links records).map Edge.child)[0]? = some dummy :=
    rfl
  have lastAt := dummyAtEnd
  rw [List.getLast?_eq_getElem?] at lastAt
  have sameNode :
      (dummy :: (links records).map Edge.child)[0]? =
        (dummy :: (links records).map Edge.child)[
          (links records).length]? :=
    headAt.trans (by simpa using lastAt.symm)
  have zeroBound :
      0 < (dummy :: (links records).map Edge.child).length := by
    simp
  have noLinks : (links records).length = 0 :=
    (List.getElem?_inj zeroBound represented.nodesNodup).mp sameNode |>.symm
  have headBound :
      (headMoves records).length ≤ (links records).length :=
    Nat.le_trans represented.headBeforeTail represented.tailBound
  omega

end Prefix

namespace AtomSchedule

/-- The same-attempt Head=Tail snapshot behind an empty record is sourced by
the corresponding initializers or by exact earlier pointer advances. -/
theorem emptyRecord_pointerOrigins_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {head : NodeId}
    (actionShape : record.action = .empty head) :
    (head = dummy ∨
      ∃ earlier previous payload,
        earlier ∈ structuralRecords trace ∧
          earlier.action = .advanceHead previous head payload ∧
          MultiLocationRC11.IdBefore
            earlier.point record.point schedule.ids) ∧
    (head = dummy ∨
      ∃ earlier previous,
        earlier ∈ structuralRecords trace ∧
          earlier.action = .advanceTail previous head ∧
          MultiLocationRC11.IdBefore
            earlier.point record.point schedule.ids) := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  rcases occurrence with ⟨validationId, action⟩
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
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation sourceHead point =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp only [Action.empty.injEq] at actionShape
      subst sourceHead
      obtain ⟨headLoadId, tailLoadId, headTailPO, tailPointPO,
          _pointValidationPO⟩ :=
        execution.dequeueEmptyValidation_programOrder eventMember
      let headRead : MultiLocationRC11.Atom Site Ptr :=
        (⟨headLoadId,
          .dequeueHeadLoad thread operation (.node head)⟩ :
            AtomicOccurrence Value).toRC11Atom
      let tailRead : MultiLocationRC11.Atom Site Ptr :=
        (⟨tailLoadId,
          .dequeueTailLoad thread operation (.node head)⟩ :
            AtomicOccurrence Value).toRC11Atom
      obtain ⟨headSource, headRF, headOrigin⟩ :=
        headNodeRead_hasOrigin execution headTailPO.closed.1 rfl rfl
      obtain ⟨tailSource, tailRF, tailOrigin⟩ :=
        tailNodeRead_hasOrigin execution tailPointPO.closed.1 rfl rfl
      have headReadBeforePoint :
          MultiLocationRC11.IdBefore
            headRead.id point schedule.ids := by
        exact MultiLocationRC11.IdBefore.transitive
          (schedule.respectsProgramOrder headTailPO)
          (schedule.respectsProgramOrder tailPointPO)
      have tailReadBeforePoint :
          MultiLocationRC11.IdBefore
            tailRead.id point schedule.ids :=
        schedule.respectsProgramOrder tailPointPO
      constructor
      · rcases headOrigin with initializer |
          ⟨earlier, previous, payload, earlierMember,
            earlierShape, earlierExact⟩
        · exact Or.inl initializer.2.symm
        · right
          refine ⟨earlier, previous, payload, earlierMember,
            earlierShape, ?_⟩
          have sourceBeforeRead := schedule.readsFrom_before headRF
          rw [← earlierExact] at sourceBeforeRead
          exact MultiLocationRC11.IdBefore.transitive
            (by simpa [headRead] using sourceBeforeRead)
            (by simpa [headRead] using headReadBeforePoint)
      · rcases tailOrigin with initializer |
          ⟨earlier, previous, earlierMember,
            earlierShape, earlierExact⟩
        · exact Or.inl initializer.2.symm
        · right
          refine ⟨earlier, previous, earlierMember, earlierShape, ?_⟩
          have sourceBeforeRead := schedule.readsFrom_before tailRF
          rw [← earlierExact] at sourceBeforeRead
          exact MultiLocationRC11.IdBefore.transitive
            (by simpa [tailRead] using sourceBeforeRead)
            (by simpa [tailRead] using tailReadBeforePoint)
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      simp at actionShape

/-- The initializer source of the empty anchor excludes every earlier link
whose owner is the observed Head node. -/
theorem emptyBefore_noOutgoingLink
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {head : NodeId}
    (actionShape : record.action = .empty head) :
    head ∉ (Prefix.links (schedule.recordsBefore record)).map
      Prefix.Edge.owner := by
  obtain ⟨source, latest, initializer⟩ :=
    schedule.emptyRecord_has_nullInitializer member actionShape
  intro ownerMember
  rcases List.mem_map.mp ownerMember with ⟨edge, edgeMember, edgeOwner⟩
  obtain ⟨link, linkBefore, linkShape⟩ :=
    Prefix.record_of_edge_mem_links edgeMember
  have linkMember : link ∈ structuralRecords trace :=
    mem_structuralRecords_of_mem_recordsOn linkBefore
  have exactShape :
      link.action = .link head edge.child edge.payload := by
    simpa [edgeOwner] using linkShape
  have linkPointBefore :
      MultiLocationRC11.IdBefore
        link.point record.point schedule.ids :=
    (schedule.mem_recordsBefore_iff member linkMember).1 linkBefore
  have linkRMW : link.pointAtom.IsRMW :=
    pointAtom_isRMW_of_structuralRecord linkMember (by simp [exactShape])
  have linkWrite : link.pointAtom.IsWrite :=
    (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW linkRMW).1
  have sourceWrite : source.IsWrite :=
    MultiLocationRC11.Atom.isWrite_of_writtenValue
      (initializerAt_next_writesNull execution initializer)
  have different : link.pointAtom ≠ source := by
    intro same
    have linkNoninitial :=
      (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW linkRMW).2
    apply linkNoninitial
    simpa [same] using initializer.2.2
  have sameLocation : source.location = link.pointAtom.location := by
    calc
      source.location = .next head := initializer.2.1
      _ = link.action.site := by simp [exactShape, Action.site]
      _ = link.pointAtom.location :=
        (pointAtom_location linkMember).symm
  have initializerAtSource :
      execution.candidate.InitializerAt source.location source := by
    rw [initializer.2.1]
    exact initializer
  have sourceBeforeLink :
      MultiLocationRC11.MO execution.candidate source link.pointAtom :=
    ⟨initializer.1,
      pointAtom_mem_candidate (execution := execution) linkMember,
      sourceWrite,
      linkWrite, sameLocation,
      execution.valid.initializerFirst initializerAtSource
        (pointAtom_mem_candidate (execution := execution) linkMember)
        sameLocation.symm linkWrite different⟩
  exact latest.noLaterBefore sourceBeforeLink (by
    simpa using linkPointBefore)

/-- Exact empty-action readiness at the schedule prefix ending immediately
before its retroactive null-read point. -/
theorem emptyBeforeReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {head : NodeId}
    (actionShape : focus.action = .empty head)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    (Prefix.stateOf dummy (schedule.recordsBefore focus)).nodes[
        (Prefix.headMoves (schedule.recordsBefore focus)).length]? =
        some head ∧
      (Prefix.headMoves (schedule.recordsBefore focus)).length =
        (Prefix.links (schedule.recordsBefore focus)).length := by
  let earlier := schedule.recordsBefore focus
  have noOutgoing :
      head ∉ (Prefix.links earlier).map Prefix.Edge.owner := by
    exact schedule.emptyBefore_noOutgoingLink
      focusMember actionShape
  obtain ⟨headOrigin, _tailOrigin⟩ :=
    schedule.emptyRecord_pointerOrigins_before
      focusMember actionShape
  have headMember :
      head ∈ dummy :: (Prefix.links earlier).map Prefix.Edge.child := by
    rcases headOrigin with rooted |
        ⟨move, previous, payload, moveMember, moveShape, moveBefore⟩
    · simp [rooted]
    · have moveInEarlier : move ∈ earlier :=
        (schedule.mem_recordsBefore_iff focusMember moveMember).2
          moveBefore
      have moveProjection := Prefix.Record.projections_of_advanceHead moveShape
      have moveInHeads :
          (⟨previous, head, payload⟩ : Prefix.Edge Value) ∈
            Prefix.headMoves earlier := by
        apply List.mem_filterMap.mpr
        exact ⟨move, moveInEarlier, moveProjection.2.2⟩
      rw [represented.headExact] at moveInHeads
      have moveInLinks :
          (⟨previous, head, payload⟩ : Prefix.Edge Value) ∈
            Prefix.links earlier :=
        List.mem_of_mem_take moveInHeads
      exact List.mem_cons.mpr (Or.inr
        (List.mem_map.mpr
          ⟨(⟨previous, head, payload⟩ : Prefix.Edge Value),
            moveInLinks, rfl⟩))
  have headAtEnd :
      (dummy :: (Prefix.links earlier).map Prefix.Edge.child).getLast? =
        some head :=
    represented.getLast?_eq_of_mem_of_not_owner headMember noOutgoing
  have headLength :
      (Prefix.headMoves earlier).length =
        (Prefix.links earlier).length := by
    rcases headOrigin with rooted |
        ⟨move, previous, payload, moveMember, moveShape, moveBefore⟩
    · subst head
      exact represented.headAtEnd_of_dummy_at_last headAtEnd
    · have moveInEarlier : move ∈ earlier :=
        (schedule.mem_recordsBefore_iff focusMember moveMember).2
          moveBefore
      have moveInHeads :
          (⟨previous, head, payload⟩ : Prefix.Edge Value) ∈
            Prefix.headMoves earlier := by
        apply List.mem_filterMap.mpr
        exact ⟨move, moveInEarlier,
          (Prefix.Record.projections_of_advanceHead moveShape).2.2⟩
      exact represented.headAtEnd_of_move_to_last
        moveInHeads headAtEnd
  constructor
  · have lastAt := headAtEnd
    rw [List.getLast?_eq_getElem?] at lastAt
    simpa [Prefix.stateOf, earlier, headLength] using lastAt
  · exact headLength

/-- Replay-ready empty case: the exact-focus record applies and its no-op
extension preserves the canonical representation. -/
theorem emptyBeforeAppliesAndPreserves
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {head : NodeId}
    (actionShape : focus.action = .empty head)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    focus.Applies
        (Prefix.stateOf dummy (schedule.recordsBefore focus))
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus ++ [focus])) ∧
      Prefix.Rep dummy (schedule.recordsBefore focus ++ [focus]) := by
  obtain ⟨headNode, headAtEnd⟩ :=
    schedule.emptyBeforeReady focusMember actionShape represented
  exact ⟨represented.emptyApplies focus actionShape headNode headAtEnd,
    represented.snocEmpty focus actionShape⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
