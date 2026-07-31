import WeakMemory.MSQueueSourceWriteClassification

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Site-specific origins of Michael--Scott writes

The generic `WriteOrigin` theorem says that every represented write is an
initializer or an exact successful structural CAS.  This module uses the
source record shape to refine that disjunction by queue location:

* a `next owner` write is its initializer or a link at `owner`;
* a Tail write is the static Tail initializer or a Tail advance; and
* a Head write is the static Head initializer or a Head advance.

The structural branches retain the exact source record and the pointer value
written by its successful CAS.
-/

/-- Recover the occurrence that selected an extracted structural record. -/
theorem selectedOccurrence_of_structuralRecord
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    ∃ occurrence,
      occurrence ∈ atomicOccurrences trace ∧
        structuralRecordOfOccurrence? occurrence = some record := by
  rcases List.mem_filterMap.mp member with
    ⟨event, eventMember, selected⟩
  cases event with
  | atomic occurrence =>
      refine ⟨occurrence,
        atomicOccurrence_mem_of_atomicEvent_mem eventMember, ?_⟩
      simpa [structuralRecordOfEvent?] using selected
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected

/-- Exhaustive source shape of an extracted structural record, including its
atomic site and written pointer. -/
theorem structuralRecord_shape
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    (∃ owner node value,
      record.action = .link owner node value ∧
        record.pointAtom.location = .next owner ∧
        record.pointAtom.writtenValue = some (.node node)) ∨
    (∃ expected desired,
      record.action = .advanceTail expected desired ∧
        record.pointAtom.location = .tail ∧
        record.pointAtom.writtenValue = some (.node desired)) ∨
    (∃ expected desired value,
      record.action = .advanceHead expected desired value ∧
        record.pointAtom.location = .head ∧
        record.pointAtom.writtenValue = some (.node desired)) ∨
    (∃ head,
      record.action = .empty head ∧
        record.pointAtom.location = .next head ∧
        record.pointAtom.writtenValue = none) := by
  obtain ⟨occurrence, _occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext =>
      simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad =>
      simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad =>
      simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate =>
      simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation owner node value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          exact Or.inl ⟨owner, node, value, rfl, rfl, rfl⟩
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          exact Or.inr (Or.inl ⟨expected, desired, rfl, rfl, rfl⟩)
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          exact Or.inr (Or.inl ⟨expected, desired, rfl, rfl, rfl⟩)
  | dequeueHeadLoad =>
      simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad =>
      simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad =>
      simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate =>
      simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      exact Or.inr (Or.inr (Or.inr ⟨head, rfl, rfl, rfl⟩))
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          exact Or.inr (Or.inl ⟨expected, desired, rfl, rfl, rfl⟩)
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          exact Or.inr
            (Or.inr (Or.inl ⟨expected, desired, value, rfl, rfl, rfl⟩))

/-- The static Head initializer is present in every exact source projection. -/
theorem headInitializer_at
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) :
    execution.candidate.InitializerAt .head (headInitializer dummy) := by
  refine ⟨?_, rfl, ?_⟩
  · rw [execution.atoms_exact, projectedAtoms]
    simp [staticAtoms]
  · trivial

/-- The static Tail initializer is present in every exact source projection. -/
theorem tailInitializer_at
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) :
    execution.candidate.InitializerAt .tail (tailInitializer dummy) := by
  refine ⟨?_, rfl, ?_⟩
  · rw [execution.atoms_exact, projectedAtoms]
    simp [staticAtoms]
  · trivial

/-- Every source-generated initializer of a node's `next` field writes null. -/
theorem initializerAt_next_writesNull
    {Value : Type}
    {dummy owner : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {atom : MultiLocationRC11.Atom Site Ptr}
    (initializerAt :
      execution.candidate.InitializerAt (.next owner) atom) :
    atom.writtenValue = some .null := by
  rcases initializerAt with ⟨atomMember, atSite, initial⟩
  rw [execution.atoms_exact, projectedAtoms] at atomMember
  rcases List.mem_append.mp atomMember with staticMember | dynamicMember
  · simp [staticAtoms] at staticMember
    rcases staticMember with head | tail | next
    · subst atom
      simp [headInitializer] at atSite
    · subst atom
      simp [tailInitializer] at atSite
    · subst atom
      rfl
  · rcases List.mem_map.mp dynamicMember with
      ⟨occurrence, _occurrenceMember, atomShape⟩
    subst atom
    rcases occurrence with ⟨id, action⟩
    cases action with
    | initializeNext => rfl
    | enqueueTailLoad =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | enqueueNextLoad =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | enqueueTailValidate =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | enqueueLinkCAS thread operation tail node value observed succeeded =>
        cases succeeded <;>
          simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
            MultiLocationRC11.Atom.IsInitial,
            MultiLocationRC11.Access.IsInitial] at initial
    | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
        cases succeeded <;>
          simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
            MultiLocationRC11.Atom.IsInitial,
            MultiLocationRC11.Access.IsInitial] at initial
    | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
        cases succeeded <;>
          simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
            MultiLocationRC11.Atom.IsInitial,
            MultiLocationRC11.Access.IsInitial] at initial
    | dequeueHeadLoad =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | dequeueTailLoad =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | dequeueNextLoad =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | dequeueHeadValidate =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | dequeueHeadValidateEmpty =>
        simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
          MultiLocationRC11.Atom.IsInitial,
          MultiLocationRC11.Access.IsInitial] at initial
    | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
        cases succeeded <;>
          simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
            MultiLocationRC11.Atom.IsInitial,
            MultiLocationRC11.Access.IsInitial] at initial
    | dequeueHeadCAS thread operation expected desired value observed succeeded =>
        cases succeeded <;>
          simp [AtomicOccurrence.toRC11Atom, AtomicAction.access,
            MultiLocationRC11.Atom.IsInitial,
            MultiLocationRC11.Access.IsInitial] at initial

/-- Two initializer certificates at one represented location select the same
carrier atom. -/
theorem initializerAt_unique
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {location : Site}
    {first second : MultiLocationRC11.Atom Site Ptr}
    (firstAt : execution.candidate.InitializerAt location first)
    (secondAt : execution.candidate.InitializerAt location second) :
    first = second := by
  obtain ⟨initializer, _initializerAt, unique⟩ :=
    execution.valid.initializerExistsUnique location
      ⟨first, firstAt.1, firstAt.2.1⟩
  exact (unique first firstAt).trans (unique second secondAt).symm

namespace WriteOrigin

/-- A write at `next owner` is exactly that site's initializer or a successful
link record that installs `node`. -/
theorem atNext
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {atom : MultiLocationRC11.Atom Site Ptr}
    (origin : WriteOrigin execution atom)
    (owner : NodeId)
    (atSite : atom.location = .next owner) :
    (execution.candidate.InitializerAt (.next owner) atom ∧
      atom.writtenValue = some .null) ∨
      ∃ record node value,
        record ∈ structuralRecords trace ∧
          record.action = .link owner node value ∧
          record.pointAtom = atom ∧
          atom.writtenValue = some (.node node) := by
  cases origin with
  | initializer initializerAt =>
      left
      have transported :
          execution.candidate.InitializerAt (.next owner) atom := by
        simpa [atSite] using initializerAt
      exact ⟨transported,
        initializerAt_next_writesNull execution transported⟩
  | structural record member casPoint exact =>
      rcases structuralRecord_shape member with
        link | tailAdvance | headAdvance | empty
      · rcases link with
          ⟨recordOwner, node, value, actionShape,
            pointSite, written⟩
        have ownerEquality : recordOwner = owner := by
          have locationsEqual :
              Site.next recordOwner = Site.next owner := by
            calc
              Site.next recordOwner = record.pointAtom.location :=
                pointSite.symm
              _ = atom.location := congrArg
                MultiLocationRC11.Atom.location exact
              _ = Site.next owner := atSite
          exact Site.next.inj locationsEqual
        subst recordOwner
        right
        refine ⟨record, node, value, member, actionShape, exact, ?_⟩
        simpa [← exact] using written
      · rcases tailAdvance with
          ⟨expected, desired, actionShape, pointSite, _written⟩
        have impossible : Site.tail = Site.next owner := by
          calc
            Site.tail = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.next owner := atSite
        cases impossible
      · rcases headAdvance with
          ⟨expected, desired, value, actionShape, pointSite, _written⟩
        have impossible : Site.head = Site.next owner := by
          calc
            Site.head = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.next owner := atSite
        cases impossible
      · rcases empty with ⟨head, actionShape, _pointSite, _written⟩
        rw [actionShape] at casPoint
        exact (Action.empty_not_isCAS head casPoint).elim

/-- A Tail write is exactly the static Tail initializer or a successful Tail
advance record. -/
theorem atTail
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {atom : MultiLocationRC11.Atom Site Ptr}
    (origin : WriteOrigin execution atom)
    (atSite : atom.location = .tail) :
    atom = tailInitializer dummy ∨
      ∃ record expected desired,
        record ∈ structuralRecords trace ∧
          record.action = .advanceTail expected desired ∧
          record.pointAtom = atom ∧
          atom.writtenValue = some (.node desired) := by
  cases origin with
  | initializer initializerAt =>
      left
      apply initializerAt_unique execution
      · simpa [atSite] using initializerAt
      · exact tailInitializer_at execution
  | structural record member casPoint exact =>
      rcases structuralRecord_shape member with
        link | tailAdvance | headAdvance | empty
      · rcases link with
          ⟨owner, node, value, actionShape, pointSite, _written⟩
        have impossible : Site.next owner = Site.tail := by
          calc
            Site.next owner = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.tail := atSite
        cases impossible
      · rcases tailAdvance with
          ⟨expected, desired, actionShape, _pointSite, written⟩
        right
        refine ⟨record, expected, desired, member,
          actionShape, exact, ?_⟩
        simpa [← exact] using written
      · rcases headAdvance with
          ⟨expected, desired, value, actionShape, pointSite, _written⟩
        have impossible : Site.head = Site.tail := by
          calc
            Site.head = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.tail := atSite
        cases impossible
      · rcases empty with ⟨head, actionShape, _pointSite, _written⟩
        rw [actionShape] at casPoint
        exact (Action.empty_not_isCAS head casPoint).elim

/-- A Head write is exactly the static Head initializer or a successful Head
advance record. -/
theorem atHead
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {atom : MultiLocationRC11.Atom Site Ptr}
    (origin : WriteOrigin execution atom)
    (atSite : atom.location = .head) :
    atom = headInitializer dummy ∨
      ∃ record expected desired value,
        record ∈ structuralRecords trace ∧
          record.action = .advanceHead expected desired value ∧
          record.pointAtom = atom ∧
          atom.writtenValue = some (.node desired) := by
  cases origin with
  | initializer initializerAt =>
      left
      apply initializerAt_unique execution
      · simpa [atSite] using initializerAt
      · exact headInitializer_at execution
  | structural record member casPoint exact =>
      rcases structuralRecord_shape member with
        link | tailAdvance | headAdvance | empty
      · rcases link with
          ⟨owner, node, value, actionShape, pointSite, _written⟩
        have impossible : Site.next owner = Site.head := by
          calc
            Site.next owner = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.head := atSite
        cases impossible
      · rcases tailAdvance with
          ⟨expected, desired, actionShape, pointSite, _written⟩
        have impossible : Site.tail = Site.head := by
          calc
            Site.tail = record.pointAtom.location := pointSite.symm
            _ = atom.location := congrArg
              MultiLocationRC11.Atom.location exact
            _ = Site.head := atSite
        cases impossible
      · rcases headAdvance with
          ⟨expected, desired, value, actionShape, _pointSite, written⟩
        right
        refine ⟨record, expected, desired, value, member,
          actionShape, exact, ?_⟩
        simpa [← exact] using written
      · rcases empty with ⟨head, actionShape, _pointSite, _written⟩
        rw [actionShape] at casPoint
        exact (Action.empty_not_isCAS head casPoint).elim

end WriteOrigin

end WeakMemory.MSQueue.Source.Structural
