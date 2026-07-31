import WeakMemory.MSQueueSourceObservations
import WeakMemory.MSQueueSourceRecordDependencies
import WeakMemory.MSQueueSourceReservation

namespace WeakMemory.MSQueue.Source.Structural

/-!
# The scheduled link graph is rooted

Stable Tail provenance and the exact link traversed by every Tail swing imply
that a successful link either extends the dummy directly or extends a node
installed by an earlier successful link.  Reservation and site uniqueness in
the imported layers make those incoming and outgoing edges unique.
-/

namespace AtomSchedule

/-- Every extracted link is rooted at the dummy or has an exact earlier parent
link ending at its owner. -/
theorem linkRecord_root_or_parent
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {owner node : NodeId}
    {value : Value}
    (actionShape : record.action = .link owner node value) :
    owner = dummy ∨
      ∃ parent previous parentValue,
        parent ∈ structuralRecords trace ∧
          parent.action = .link previous owner parentValue ∧
          MultiLocationRC11.IdBefore
            parent.point record.point schedule.ids := by
  obtain ⟨source, validation, latest, validationBefore, origin⟩ :=
    schedule.linkRecord_tailObservation member actionShape
  rcases origin with initializer | ⟨advance, previous,
      advanceMember, advanceShape, advanceExact⟩
  · exact Or.inl initializer.2.symm
  · obtain ⟨parent, parentValue, parentMember, parentShape,
        parentBeforeAdvance⟩ :=
      schedule.advanceTailRecord_has_priorLink
        advanceMember advanceShape
    have advanceBeforeValidation :
        MultiLocationRC11.IdBefore
          advance.point validation.id schedule.ids := by
      have sourceBefore := latest.sourceBefore
      rw [← advanceExact] at sourceBefore
      simpa using sourceBefore
    exact Or.inr ⟨parent, previous, parentValue,
      parentMember, parentShape,
      MultiLocationRC11.IdBefore.transitive parentBeforeAdvance
        (MultiLocationRC11.IdBefore.transitive
          advanceBeforeValidation validationBefore)⟩

/-- The node installed by a link is fresh relative to the permanent dummy. -/
theorem linkRecord_target_ne_dummy
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {owner node : NodeId}
    {value : Value}
    (actionShape : record.action = .link owner node value) :
    node ≠ dummy :=
  linkedNode_ne_dummy execution.sourceWellFormed member actionShape

/-- A successful link cannot point a node to itself. -/
theorem linkRecord_owner_ne_target
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {owner node : NodeId}
    {value : Value}
    (actionShape : record.action = .link owner node value) :
    owner ≠ node := by
  intro same
  subst node
  rcases schedule.linkRecord_root_or_parent member actionShape with
      rooted | ⟨parent, previous, parentValue, parentMember,
        parentShape, parentBefore⟩
  · have targetNotDummy :=
      linkRecord_target_ne_dummy (execution := execution)
        member actionShape
    exact targetNotDummy rooted
  · have sameRecord := linkRecord_eq_of_same_node
      execution.sourceWellFormed parentMember member
      parentShape actionShape
    subst parent
    exact MultiLocationRC11.IdBefore.irreflexive parentBefore

/-- Incoming edges are unique: two links ending at one node are the same
structural record. -/
theorem linkRecord_incoming_unique
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {first second : Record Value}
    {firstOwner secondOwner node : NodeId}
    {firstValue secondValue : Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace)
    (firstAction : first.action = .link firstOwner node firstValue)
    (secondAction : second.action = .link secondOwner node secondValue) :
    first = second :=
  linkRecord_eq_of_same_node execution.sourceWellFormed
    firstMember secondMember firstAction secondAction

/-- Outgoing edges are unique: one owner has at most one successful link. -/
theorem linkRecord_outgoing_unique
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {first second : Record Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace)
    {owner firstNode secondNode : NodeId}
    {firstValue secondValue : Value}
    (firstAction : first.action = .link owner firstNode firstValue)
    (secondAction : second.action = .link owner secondNode secondValue) :
    first = second :=
  schedule.linkRecord_eq_of_same_owner firstMember secondMember
    firstAction secondAction

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
