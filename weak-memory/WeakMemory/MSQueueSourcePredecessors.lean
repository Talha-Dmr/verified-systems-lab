import WeakMemory.MSQueueRecordScheduling
import WeakMemory.MSQueueSourceWriteOrigins

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Exact read operands and predecessor origins

The RMW-origin layer identifies the write immediately preceding a structural
CAS.  Here the checked source machine supplies the compare operand read by
that CAS, so later queue-representation proofs can specialize predecessor
origins by site and pointer value.
-/

namespace Action

/-- RC11 location mutated or observed by a structural point. -/
def site : Action Value → Site
  | .link owner .. => .next owner
  | .advanceTail .. => .tail
  | .advanceHead .. => .head
  | .empty head => .next head

/-- Pointer value that a structural point reads before taking effect. -/
def expectedRead : Action Value → Ptr
  | .link .. => .null
  | .advanceTail expected .. => .node expected
  | .advanceHead expected .. => .node expected
  | .empty .. => .null

/-- Pointer written by a structural point, if it is a CAS point. -/
def written : Action Value → Option Ptr
  | .link _ node _ => some (.node node)
  | .advanceTail _ desired => some (.node desired)
  | .advanceHead _ desired _ => some (.node desired)
  | .empty .. => none

end Action

/-- Extraction preserves the exact RC11 site advertised by the structural
action. -/
theorem pointAtom_location
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom.location = record.action.site := by
  rcases structuralRecord_shape member with
    ⟨owner, node, value, actionShape, location, written⟩ |
    ⟨expected, desired, actionShape, location, written⟩ |
    ⟨expected, desired, value, actionShape, location, written⟩ |
    ⟨head, actionShape, location, written⟩
  · simpa [Action.site, actionShape] using location
  · simpa [Action.site, actionShape] using location
  · simpa [Action.site, actionShape] using location
  · simpa [Action.site, actionShape] using location

/-- Extraction also preserves the exact pointer written by the action. -/
theorem pointAtom_writtenValue
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom.writtenValue = record.action.written := by
  rcases structuralRecord_shape member with
    ⟨owner, node, value, actionShape, location, written⟩ |
    ⟨expected, desired, actionShape, location, written⟩ |
    ⟨expected, desired, value, actionShape, location, written⟩ |
    ⟨head, actionShape, location, written⟩
  · simpa [Action.written, actionShape] using written
  · simpa [Action.written, actionShape] using written
  · simpa [Action.written, actionShape] using written
  · simpa [Action.written, actionShape] using written

/-- Every extracted point reads the operand encoded by its structural action.
For CAS points, source well-formedness rules out a mismatched success; for an
empty dequeue, `pointAtom` is definitionally the earlier null load. -/
theorem pointAtom_readValue
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom.readValue = some record.action.expectedRead := by
  obtain ⟨occurrence, occurrenceMember, selected⟩ :=
    selectedOccurrence_of_structuralRecord member
  have eventMember :=
    atomicEvent_mem_of_atomicOccurrence_mem occurrenceMember
  have notMalformed := wellFormed.atomic_not_malformedSuccess eventMember
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]
            at notMalformed
          simp [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.readValue,
            AtomicAction.access, MultiLocationRC11.Access.readValue,
            Action.expectedRead, notMalformed]
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]
            at notMalformed
          simp [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.readValue,
            AtomicAction.access, MultiLocationRC11.Access.readValue,
            Action.expectedRead, notMalformed]
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]
            at notMalformed
          simp [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.readValue,
            AtomicAction.access, MultiLocationRC11.Access.readValue,
            Action.expectedRead, notMalformed]
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]
            at notMalformed
          simp [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.readValue,
            AtomicAction.access, MultiLocationRC11.Access.readValue,
            Action.expectedRead, notMalformed]
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]
            at notMalformed
          simp [Record.pointAtom, Record.pointOccurrence,
            AtomicOccurrence.toRC11Atom, MultiLocationRC11.Atom.readValue,
            AtomicAction.access, MultiLocationRC11.Access.readValue,
            Action.expectedRead, notMalformed]

/-- Any represented read of `node` from `next owner` is sourced by the exact
successful link that installed that node; a null-writing initializer cannot
explain the observation. -/
theorem nextNodeRead_hasLinkOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {target : MultiLocationRC11.Atom Site Ptr}
    (targetMember : target ∈ execution.candidate.atoms)
    {owner node : NodeId}
    (targetSite : target.location = .next owner)
    (targetValue : target.readValue = some (.node node)) :
    ∃ source record value,
      MultiLocationRC11.RF execution.candidate source target ∧
        record ∈ structuralRecords trace ∧
        record.action = .link owner node value ∧
        record.pointAtom = source := by
  have targetRead : target.IsRead := by
    change target.access.readValue = some (.node node) at targetValue
    change target.access.IsRead
    generalize target.access = access at targetValue ⊢
    cases access <;>
      simp [MultiLocationRC11.Access.readValue,
        MultiLocationRC11.Access.IsRead] at targetValue ⊢
  obtain ⟨source, readsFrom⟩ :=
    execution.valid.toWellFormed.everyRead_hasSource
      targetMember targetRead
  have origin := writeOrigin execution readsFrom.closed.1
    readsFrom.2.2.1
  have sourceSite : source.location = .next owner :=
    readsFrom.sameLocation.trans targetSite
  rcases origin.atNext owner sourceSite with
    initializer | ⟨record, installed, value, recordMember,
      actionShape, exact, sourceWritten⟩
  · have agreement := readsFrom.valueAgreement
    rw [initializer.2, targetValue] at agreement
    simp at agreement
  · have agreement := readsFrom.valueAgreement
    rw [sourceWritten, targetValue] at agreement
    simp at agreement
    subst installed
    exact ⟨source, record, value, readsFrom, recordMember,
      actionShape, exact⟩

/-- Dually, a represented null read from `next owner` is sourced by that
site's initializer, never by a link write. -/
theorem nextNullRead_hasInitializerSource
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {target : MultiLocationRC11.Atom Site Ptr}
    (targetMember : target ∈ execution.candidate.atoms)
    {owner : NodeId}
    (targetSite : target.location = .next owner)
    (targetValue : target.readValue = some .null) :
    ∃ source,
      MultiLocationRC11.RF execution.candidate source target ∧
        execution.candidate.InitializerAt (.next owner) source := by
  have targetRead : target.IsRead := by
    change target.access.readValue = some .null at targetValue
    change target.access.IsRead
    generalize target.access = access at targetValue ⊢
    cases access <;>
      simp [MultiLocationRC11.Access.readValue,
        MultiLocationRC11.Access.IsRead] at targetValue ⊢
  obtain ⟨source, readsFrom⟩ :=
    execution.valid.toWellFormed.everyRead_hasSource
      targetMember targetRead
  have origin := writeOrigin execution readsFrom.closed.1
    readsFrom.2.2.1
  have sourceSite : source.location = .next owner :=
    readsFrom.sameLocation.trans targetSite
  rcases origin.atNext owner sourceSite with
    initializer | ⟨record, installed, value, recordMember,
      actionShape, exact, sourceWritten⟩
  · exact ⟨source, readsFrom, initializer.1⟩
  · have agreement := readsFrom.valueAgreement
    rw [sourceWritten, targetValue] at agreement
    simp at agreement

/-- A Tail read of `observed` is sourced by the dummy initializer or by the
exact previous Tail advance that installed `observed`. -/
theorem tailNodeRead_hasOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {target : MultiLocationRC11.Atom Site Ptr}
    (targetMember : target ∈ execution.candidate.atoms)
    {observed : NodeId}
    (targetSite : target.location = .tail)
    (targetValue : target.readValue = some (.node observed)) :
    ∃ source,
      MultiLocationRC11.RF execution.candidate source target ∧
        ((source = tailInitializer dummy ∧ dummy = observed) ∨
          ∃ earlier previous,
            earlier ∈ structuralRecords trace ∧
              earlier.action = .advanceTail previous observed ∧
              earlier.pointAtom = source) := by
  have targetRead : target.IsRead := by
    change target.access.readValue = some (.node observed) at targetValue
    change target.access.IsRead
    generalize target.access = access at targetValue ⊢
    cases access <;>
      simp [MultiLocationRC11.Access.readValue,
        MultiLocationRC11.Access.IsRead] at targetValue ⊢
  obtain ⟨source, readsFrom⟩ :=
    execution.valid.toWellFormed.everyRead_hasSource
      targetMember targetRead
  have origin := writeOrigin execution readsFrom.closed.1
    readsFrom.2.2.1
  rcases origin.atTail (readsFrom.sameLocation.trans targetSite) with
    sourceShape | ⟨earlier, previous, installed, earlierMember,
      earlierShape, earlierExact, sourceWritten⟩
  · have agreement := readsFrom.valueAgreement
    rw [sourceShape, targetValue] at agreement
    simp [tailInitializer, MultiLocationRC11.Atom.writtenValue,
      MultiLocationRC11.Access.writtenValue] at agreement
    exact ⟨source, readsFrom, Or.inl ⟨sourceShape, agreement⟩⟩
  · have agreement := readsFrom.valueAgreement
    rw [sourceWritten, targetValue] at agreement
    simp at agreement
    subst installed
    exact ⟨source, readsFrom,
      Or.inr ⟨earlier, previous, earlierMember,
        earlierShape, earlierExact⟩⟩

/-- The analogous Head-read origin theorem. -/
theorem headNodeRead_hasOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {target : MultiLocationRC11.Atom Site Ptr}
    (targetMember : target ∈ execution.candidate.atoms)
    {observed : NodeId}
    (targetSite : target.location = .head)
    (targetValue : target.readValue = some (.node observed)) :
    ∃ source,
      MultiLocationRC11.RF execution.candidate source target ∧
        ((source = headInitializer dummy ∧ dummy = observed) ∨
          ∃ earlier previous earlierValue,
            earlier ∈ structuralRecords trace ∧
              earlier.action =
                .advanceHead previous observed earlierValue ∧
              earlier.pointAtom = source) := by
  have targetRead : target.IsRead := by
    change target.access.readValue = some (.node observed) at targetValue
    change target.access.IsRead
    generalize target.access = access at targetValue ⊢
    cases access <;>
      simp [MultiLocationRC11.Access.readValue,
        MultiLocationRC11.Access.IsRead] at targetValue ⊢
  obtain ⟨source, readsFrom⟩ :=
    execution.valid.toWellFormed.everyRead_hasSource
      targetMember targetRead
  have origin := writeOrigin execution readsFrom.closed.1
    readsFrom.2.2.1
  rcases origin.atHead (readsFrom.sameLocation.trans targetSite) with
    sourceShape | ⟨earlier, previous, installed, earlierValue,
      earlierMember, earlierShape, earlierExact, sourceWritten⟩
  · have agreement := readsFrom.valueAgreement
    rw [sourceShape, targetValue] at agreement
    simp [headInitializer, MultiLocationRC11.Atom.writtenValue,
      MultiLocationRC11.Access.writtenValue] at agreement
    exact ⟨source, readsFrom, Or.inl ⟨sourceShape, agreement⟩⟩
  · have agreement := readsFrom.valueAgreement
    rw [sourceWritten, targetValue] at agreement
    simp at agreement
    subst installed
    exact ⟨source, readsFrom,
      Or.inr ⟨earlier, previous, earlierValue, earlierMember,
        earlierShape, earlierExact⟩⟩

namespace AtomSchedule

/-- A successful link reads null, so its immediate `next owner` predecessor
cannot be an earlier link; it is exactly that site's initializer. -/
theorem linkImmediateInitializer
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
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom ∧
        execution.candidate.InitializerAt (.next owner) source := by
  have casPoint : record.action.IsCAS := by
    simp [actionShape]
  obtain ⟨source, latest, immediate, origin⟩ :=
    schedule.pointImmediateWriteOrigin member casPoint
  have sourceSite : source.location = .next owner := by
    calc
      source.location = record.pointAtom.location :=
        latest.readsFrom.sameLocation
      _ = record.action.site := pointAtom_location member
      _ = .next owner := by simp [actionShape, Action.site]
  rcases origin.atNext owner sourceSite with
    initializer | ⟨earlier, earlierNode, earlierValue, earlierMember,
      earlierShape, earlierExact, sourceWritten⟩
  · exact ⟨source, latest, immediate, initializer.1⟩
  · have agreement := latest.readsFrom.valueAgreement
    rw [sourceWritten,
      pointAtom_readValue execution.sourceWellFormed member,
      actionShape] at agreement
    simp [Action.expectedRead] at agreement

/-- A Tail CAS either follows the static dummy initializer or an earlier Tail
advance whose desired node is exactly this CAS's expected node. -/
theorem tailImmediateOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {expected desired : NodeId}
    (actionShape : record.action = .advanceTail expected desired) :
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom ∧
        ((source = tailInitializer dummy ∧ dummy = expected) ∨
          ∃ earlier previous,
            earlier ∈ structuralRecords trace ∧
              earlier.action = .advanceTail previous expected ∧
              earlier.pointAtom = source) := by
  have casPoint : record.action.IsCAS := by
    simp [actionShape]
  obtain ⟨source, latest, immediate, origin⟩ :=
    schedule.pointImmediateWriteOrigin member casPoint
  have sourceSite : source.location = .tail := by
    calc
      source.location = record.pointAtom.location :=
        latest.readsFrom.sameLocation
      _ = record.action.site := pointAtom_location member
      _ = .tail := by simp [actionShape, Action.site]
  rcases origin.atTail sourceSite with
    sourceShape | ⟨earlier, previous, priorDesired, earlierMember,
      earlierShape, earlierExact, sourceWritten⟩
  · have agreement := latest.readsFrom.valueAgreement
    rw [sourceShape,
      pointAtom_readValue execution.sourceWellFormed member,
      actionShape] at agreement
    simp [tailInitializer, MultiLocationRC11.Atom.writtenValue,
      MultiLocationRC11.Access.writtenValue,
      Action.expectedRead] at agreement
    exact ⟨source, latest, immediate,
      Or.inl ⟨sourceShape, agreement⟩⟩
  · have agreement := latest.readsFrom.valueAgreement
    rw [sourceWritten,
      pointAtom_readValue execution.sourceWellFormed member,
      actionShape] at agreement
    simp [Action.expectedRead] at agreement
    subst priorDesired
    exact ⟨source, latest, immediate,
      Or.inr ⟨earlier, previous, earlierMember,
        earlierShape, earlierExact⟩⟩

/-- A Head CAS likewise follows the dummy Head initializer or an earlier Head
advance whose desired node is this CAS's expected node. -/
theorem headImmediateOrigin
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {expected desired : NodeId}
    {value : Value}
    (actionShape : record.action = .advanceHead expected desired value) :
    ∃ source,
      LatestSource schedule source record.pointAtom ∧
        MultiLocationRC11.ImmediateMO
          execution.candidate source record.pointAtom ∧
        ((source = headInitializer dummy ∧ dummy = expected) ∨
          ∃ earlier previous earlierValue,
            earlier ∈ structuralRecords trace ∧
              earlier.action =
                .advanceHead previous expected earlierValue ∧
              earlier.pointAtom = source) := by
  have casPoint : record.action.IsCAS := by
    simp [actionShape]
  obtain ⟨source, latest, immediate, origin⟩ :=
    schedule.pointImmediateWriteOrigin member casPoint
  have sourceSite : source.location = .head := by
    calc
      source.location = record.pointAtom.location :=
        latest.readsFrom.sameLocation
      _ = record.action.site := pointAtom_location member
      _ = .head := by simp [actionShape, Action.site]
  rcases origin.atHead sourceSite with
    sourceShape | ⟨earlier, previous, priorDesired, earlierValue,
      earlierMember, earlierShape, earlierExact, sourceWritten⟩
  · have agreement := latest.readsFrom.valueAgreement
    rw [sourceShape,
      pointAtom_readValue execution.sourceWellFormed member,
      actionShape] at agreement
    simp [headInitializer, MultiLocationRC11.Atom.writtenValue,
      MultiLocationRC11.Access.writtenValue,
      Action.expectedRead] at agreement
    exact ⟨source, latest, immediate,
      Or.inl ⟨sourceShape, agreement⟩⟩
  · have agreement := latest.readsFrom.valueAgreement
    rw [sourceWritten,
      pointAtom_readValue execution.sourceWellFormed member,
      actionShape] at agreement
    simp [Action.expectedRead] at agreement
    subst priorDesired
    exact ⟨source, latest, immediate,
      Or.inr ⟨earlier, previous, earlierValue, earlierMember,
        earlierShape, earlierExact⟩⟩

/-- One `next owner` location can contain at most one successful link CAS. -/
theorem linkRecord_eq_of_same_owner
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {left right : Record Value}
    (leftMember : left ∈ structuralRecords trace)
    (rightMember : right ∈ structuralRecords trace)
    {owner leftNode rightNode : NodeId}
    {leftValue rightValue : Value}
    (leftShape : left.action = .link owner leftNode leftValue)
    (rightShape : right.action = .link owner rightNode rightValue) :
    left = right := by
  obtain ⟨leftSource, _leftLatest, leftImmediate, leftInitializer⟩ :=
    schedule.linkImmediateInitializer leftMember leftShape
  obtain ⟨rightSource, _rightLatest, rightImmediate,
      rightInitializer⟩ :=
    schedule.linkImmediateInitializer rightMember rightShape
  have sameSource : leftSource = rightSource :=
    initializerAt_unique execution leftInitializer rightInitializer
  subst rightSource
  have sameAtom : left.pointAtom = right.pointAtom :=
    MultiLocationRC11.ImmediateMO.target_eq
      execution.valid.toWellFormed leftImmediate rightImmediate
  have samePoint : left.point = right.point := by
    simpa using congrArg MultiLocationRC11.Atom.id sameAtom
  exact structuralRecord_eq_of_point_eq execution.sourceWellFormed
    leftMember rightMember samePoint

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
