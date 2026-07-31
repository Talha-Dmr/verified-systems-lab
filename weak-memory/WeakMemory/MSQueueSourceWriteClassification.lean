import WeakMemory.MSQueueStructuralRMW

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Exact classification of source-backed RC11 writes

The queue refinement must not invent abstract mutations.  This module proves
the converse carrier fact: every non-initial RC11 write emitted by the source
machine is the point atom of an extracted structural record.  Together with
the point-membership lemmas, successful CAS records and dynamic writes are
therefore two views of the same events.
-/

theorem structuralRecord_mem_of_selected
    {trace : List (TraceEvent Value)}
    {occurrence : AtomicOccurrence Value}
    (occurrenceMember : occurrence ∈ atomicOccurrences trace)
    {record : Record Value}
    (selected : structuralRecordOfOccurrence? occurrence = some record) :
    record ∈ structuralRecords trace := by
  rcases List.mem_filterMap.mp occurrenceMember with
    ⟨event, eventMember, occurrenceSelected⟩
  cases event with
  | atomic emitted =>
      simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
      subst emitted
      apply List.mem_filterMap.mpr
      exact ⟨.atomic occurrence, eventMember, by
        simpa [structuralRecordOfEvent?] using selected⟩
  | invokeEnqueue => simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
  | initializePayload =>
      simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
  | invokeDequeue => simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
  | readPayload => simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
  | respondEnqueue => simp [TraceEvent.atomicOccurrence?] at occurrenceSelected
  | respondDequeue => simp [TraceEvent.atomicOccurrence?] at occurrenceSelected

/-- Every dynamic non-initial write selects a structural record at exactly
that atom. -/
theorem selectedStructuralRecord_of_noninitialWrite
    {occurrence : AtomicOccurrence Value}
    (noninitial : occurrence.toRC11Atom.IsNoninitialWrite) :
    ∃ record,
      structuralRecordOfOccurrence? occurrence = some record ∧
        record.action.IsCAS ∧
        record.pointAtom = occurrence.toRC11Atom := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsInitial, AtomicAction.access,
        MultiLocationRC11.Access.IsInitial] at noninitial
  | enqueueTailLoad =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | enqueueNextLoad =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | enqueueTailValidate =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded with
      | false =>
          simp [AtomicOccurrence.toRC11Atom,
            MultiLocationRC11.Atom.IsNoninitialWrite,
            MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at noninitial
      | true =>
          simp [structuralRecordOfOccurrence?, Record.pointAtom,
            Record.pointOccurrence]

  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false =>
          simp [AtomicOccurrence.toRC11Atom,
            MultiLocationRC11.Atom.IsNoninitialWrite,
            MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at noninitial
      | true =>
          simp [structuralRecordOfOccurrence?, Record.pointAtom,
            Record.pointOccurrence]
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false =>
          simp [AtomicOccurrence.toRC11Atom,
            MultiLocationRC11.Atom.IsNoninitialWrite,
            MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at noninitial
      | true =>
          simp [structuralRecordOfOccurrence?, Record.pointAtom,
            Record.pointOccurrence]
  | dequeueHeadLoad =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | dequeueTailLoad =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | dequeueNextLoad =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | dequeueHeadValidate =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | dequeueHeadValidateEmpty =>
      simp [AtomicOccurrence.toRC11Atom,
        MultiLocationRC11.Atom.IsNoninitialWrite,
        MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
        MultiLocationRC11.Access.IsWrite] at noninitial
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false =>
          simp [AtomicOccurrence.toRC11Atom,
            MultiLocationRC11.Atom.IsNoninitialWrite,
            MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at noninitial
      | true =>
          simp [structuralRecordOfOccurrence?, Record.pointAtom,
            Record.pointOccurrence]
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded with
      | false =>
          simp [AtomicOccurrence.toRC11Atom,
            MultiLocationRC11.Atom.IsNoninitialWrite,
            MultiLocationRC11.Atom.IsWrite, AtomicAction.access,
            MultiLocationRC11.Access.IsWrite] at noninitial
      | true =>
          simp [structuralRecordOfOccurrence?, Record.pointAtom,
            Record.pointOccurrence]

/-- Every non-initial write in an exact supported carrier is the point atom
of an extracted CAS-backed structural record. -/
theorem structuralRecord_of_noninitialWrite
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {atom : MultiLocationRC11.Atom Site Ptr}
    (atomMember : atom ∈ execution.candidate.atoms)
    (noninitial : atom.IsNoninitialWrite) :
    ∃ record,
      record ∈ structuralRecords trace ∧
        record.action.IsCAS ∧
        record.pointAtom = atom := by
  rw [execution.atoms_exact, projectedAtoms] at atomMember
  rcases List.mem_append.mp atomMember with staticMember | dynamicMember
  · have initial : atom.IsInitial := by
      simp [staticAtoms] at staticMember
      rcases staticMember with head | tail | next
      · subst atom
        trivial
      · subst atom
        trivial
      · subst atom
        trivial
    exact (noninitial.2 initial).elim
  · rcases List.mem_map.mp dynamicMember with
      ⟨occurrence, occurrenceMember, atomShape⟩
    have occurrenceNoninitial :
        occurrence.toRC11Atom.IsNoninitialWrite := by
      rw [atomShape]
      exact noninitial
    obtain ⟨record, selected, casPoint, pointShape⟩ :=
      selectedStructuralRecord_of_noninitialWrite occurrenceNoninitial
    exact ⟨record,
      structuralRecord_mem_of_selected occurrenceMember selected,
      casPoint, pointShape.trans atomShape⟩

/-- Exhaustive origin certificate for one represented write. -/
inductive WriteOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    (atom : MultiLocationRC11.Atom Site Ptr) : Prop where
  | initializer
      (atLocation :
        execution.candidate.InitializerAt atom.location atom) :
      WriteOrigin execution atom
  | structural
      (record : Record Value)
      (member : record ∈ structuralRecords trace)
      (casPoint : record.action.IsCAS)
      (exact : record.pointAtom = atom) :
      WriteOrigin execution atom

/-- Every represented write is either an initializer or an exact extracted
successful structural CAS. -/
theorem writeOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {atom : MultiLocationRC11.Atom Site Ptr}
    (atomMember : atom ∈ execution.candidate.atoms)
    (write : atom.IsWrite) :
    WriteOrigin execution atom := by
  by_cases initial : atom.IsInitial
  · exact .initializer ⟨atomMember, rfl, initial⟩
  · obtain ⟨record, recordMember, casPoint, exact⟩ :=
      structuralRecord_of_noninitialWrite atomMember ⟨write, initial⟩
    exact .structural record recordMember casPoint exact

namespace AtomSchedule

/-- The immediate predecessor of every structural RMW has an exhaustive
source origin, while retaining its scheduled latest-source certificate. -/
theorem pointImmediateWriteOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    (casPoint : record.action.IsCAS) :
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom ∧
        WriteOrigin execution source := by
  obtain ⟨source, latest, immediate⟩ :=
    schedule.pointRMWLatestSource member casPoint
  exact ⟨source, latest, immediate,
    writeOrigin execution latest.readsFrom.closed.1
      latest.readsFrom.2.2.1⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
