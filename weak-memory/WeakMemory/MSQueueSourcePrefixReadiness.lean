import WeakMemory.MSQueueSourcePrefix
import WeakMemory.MSQueueRecordPrefix

namespace WeakMemory.MSQueue.Source.Structural

/-!
# From scheduled dependencies to prefix readiness

This layer connects the algorithm-specific link graph to the canonical prefix
state.  It is deliberately parameterized by an exact earlier-record prefix;
the atom-prefix replay will instantiate the closure hypotheses with
`AtomSchedule.recordsBefore`.
-/

namespace AtomSchedule

/-- A new scheduled link extends the last represented node and installs a
fresh child, provided the prefix contains exactly all records known to be
earlier than the link. -/
theorem linkGraphReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : focus.action = .link owner child payload)
    {earlier : List (Record Value)}
    (represented : Prefix.Rep dummy earlier)
    (earlierStructural :
      ∀ record ∈ earlier, record ∈ structuralRecords trace)
    (focusNotEarlier : focus ∉ earlier)
    (containsPointEarlier :
      ∀ record ∈ structuralRecords trace,
        MultiLocationRC11.IdBefore
          record.point focus.point schedule.ids →
        record ∈ earlier) :
    (dummy :: (Prefix.links earlier).map Prefix.Edge.child).getLast? =
        some owner ∧
      child ∉ dummy :: (Prefix.links earlier).map Prefix.Edge.child := by
  have noExistingOutgoing :
      owner ∉ (Prefix.links earlier).map Prefix.Edge.owner := by
    intro ownerMember
    rcases List.mem_map.mp ownerMember with
      ⟨edge, edgeMember, edgeOwner⟩
    obtain ⟨record, recordMember, recordShape⟩ :=
      Prefix.record_of_edge_mem_links edgeMember
    have recordStructural := earlierStructural record recordMember
    have ownerShape :
        record.action = .link owner edge.child edge.payload := by
      simpa [edgeOwner] using recordShape
    have sameRecord := schedule.linkRecord_outgoing_unique
      recordStructural focusMember ownerShape actionShape
    subst record
    exact focusNotEarlier recordMember
  have ownerMember :
      owner ∈ dummy :: (Prefix.links earlier).map Prefix.Edge.child := by
    rcases schedule.linkRecord_root_or_parent
        focusMember actionShape with
      rooted | ⟨parent, previous, parentPayload, parentMember,
        parentShape, parentBefore⟩
    · simp [rooted]
    · have parentInEarlier :=
        containsPointEarlier parent parentMember parentBefore
      have edgeMember := Prefix.edge_mem_links_of_record
        parentInEarlier parentShape
      exact List.mem_cons.mpr (Or.inr
        (List.mem_map.mpr
          ⟨(⟨previous, owner, parentPayload⟩ : Prefix.Edge Value),
            edgeMember, rfl⟩))
  have ownerAtEnd :=
    represented.getLast?_eq_of_mem_of_not_owner
      ownerMember noExistingOutgoing
  have childFresh :
      child ∉ dummy :: (Prefix.links earlier).map Prefix.Edge.child := by
    intro childMember
    rcases List.mem_cons.mp childMember with childIsDummy | childInLinks
    · exact (linkRecord_target_ne_dummy
        (execution := execution) focusMember actionShape)
        childIsDummy
    · rcases List.mem_map.mp childInLinks with
        ⟨edge, edgeMember, edgeChild⟩
      obtain ⟨record, recordMember, recordShape⟩ :=
        Prefix.record_of_edge_mem_links edgeMember
      have recordStructural := earlierStructural record recordMember
      have childShape :
          record.action = .link edge.owner child edge.payload := by
        simpa [edgeChild] using recordShape
      have sameRecord := linkRecord_eq_of_same_node
        execution.sourceWellFormed recordStructural focusMember
        childShape actionShape
      subst record
      exact focusNotEarlier recordMember
  exact ⟨ownerAtEnd, childFresh⟩

/-- The stable Tail observation upgrades graph readiness to the exact
Tail-at-end condition required by a link step. -/
theorem linkReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : focus.action = .link owner child payload)
    {earlier : List (Record Value)}
    (represented : Prefix.Rep dummy earlier)
    (earlierStructural :
      ∀ record ∈ earlier, record ∈ structuralRecords trace)
    (focusNotEarlier : focus ∉ earlier)
    (containsPointEarlier :
      ∀ record ∈ structuralRecords trace,
        MultiLocationRC11.IdBefore
          record.point focus.point schedule.ids →
        record ∈ earlier) :
    (dummy :: (Prefix.links earlier).map Prefix.Edge.child).getLast? =
        some owner ∧
      child ∉ dummy :: (Prefix.links earlier).map Prefix.Edge.child ∧
      (Prefix.tailMoves earlier).length =
        (Prefix.links earlier).length := by
  obtain ⟨ownerAtEnd, childFresh⟩ :=
    schedule.linkGraphReady focusMember actionShape represented
      earlierStructural focusNotEarlier containsPointEarlier
  obtain ⟨source, validation, latest, validationBefore, origin⟩ :=
    schedule.linkRecord_tailObservation focusMember actionShape
  have tailAtEnd :
      (Prefix.tailMoves earlier).length =
        (Prefix.links earlier).length := by
    rcases origin with initializer | ⟨advance, previous,
        advanceMember, advanceShape, advanceExact⟩
    · have dummyAtEnd := ownerAtEnd
      rw [← initializer.2] at dummyAtEnd
      exact represented.tailAtEnd_of_dummy_at_last dummyAtEnd
    · have advanceBeforeValidation :
          MultiLocationRC11.IdBefore
            advance.point validation.id schedule.ids := by
        have sourceBefore := latest.sourceBefore
        rw [← advanceExact] at sourceBefore
        simpa using sourceBefore
      have advanceBeforeFocus :=
        MultiLocationRC11.IdBefore.transitive
          advanceBeforeValidation validationBefore
      have advanceInEarlier := containsPointEarlier
        advance advanceMember advanceBeforeFocus
      have moveMember := Prefix.tailMove_mem_of_record
        advanceInEarlier advanceShape
      exact represented.tailAtEnd_of_move_to_last
        moveMember ownerAtEnd
  exact ⟨ownerAtEnd, childFresh, tailAtEnd⟩

/-- Replay-ready form of `linkReady`: the current link both applies to the
canonical prefix state and preserves the prefix representation. -/
theorem linkAppliesAndPreserves
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : focus.action = .link owner child payload)
    {earlier : List (Record Value)}
    (represented : Prefix.Rep dummy earlier)
    (earlierStructural :
      ∀ record ∈ earlier, record ∈ structuralRecords trace)
    (focusNotEarlier : focus ∉ earlier)
    (containsPointEarlier :
      ∀ record ∈ structuralRecords trace,
        MultiLocationRC11.IdBefore
          record.point focus.point schedule.ids →
        record ∈ earlier) :
    focus.Applies (Prefix.stateOf dummy earlier)
        (Prefix.stateOf dummy (earlier ++ [focus])) ∧
      Prefix.Rep dummy (earlier ++ [focus]) := by
  obtain ⟨ownerAtEnd, childFresh, tailAtEnd⟩ :=
    schedule.linkReady focusMember actionShape represented
      earlierStructural focusNotEarlier containsPointEarlier
  exact ⟨Prefix.Rep.linkApplies represented focus actionShape
      ownerAtEnd childFresh tailAtEnd,
    represented.snocLink focus actionShape
      ownerAtEnd childFresh tailAtEnd⟩

/-- Exact focus-prefix specialization used by atom-prefix induction. -/
theorem linkBeforeAppliesAndPreserves
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : focus.action = .link owner child payload)
    (represented : Prefix.Rep dummy (schedule.recordsBefore focus)) :
    focus.Applies
        (Prefix.stateOf dummy (schedule.recordsBefore focus))
        (Prefix.stateOf dummy
          (schedule.recordsBefore focus ++ [focus])) ∧
      Prefix.Rep dummy (schedule.recordsBefore focus ++ [focus]) := by
  apply schedule.linkAppliesAndPreserves focusMember actionShape represented
  · intro record recordMember
    exact mem_structuralRecords_of_mem_recordsOn recordMember
  · intro focusInEarlier
    have impossible :=
      (schedule.mem_recordsBefore_iff focusMember focusMember).1
        focusInEarlier
    exact MultiLocationRC11.IdBefore.irreflexive impossible
  · intro record recordMember pointBefore
    exact (schedule.mem_recordsBefore_iff focusMember recordMember).2
      pointBefore

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
