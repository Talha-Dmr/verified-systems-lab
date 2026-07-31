import WeakMemory.MSQueueSourceWellFormed
import WeakMemory.MSQueueChain

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Source-to-chain structural certificates

This module is the memory-model-facing bridge to `MSQueueChain`.  It extracts
every successful structural CAS, together with the retroactive empty-dequeue
point, from a source trace.  A certificate may reorder those records by their
anchored atomic points, but it may neither invent a favorable queue commit nor
erase a successful Tail-helping step.

`SupportedExecution` supplies the exact source/RC11 carrier.  The remaining
`Replay` field is the explicit representation-invariant obligation.  A later
derivation layer must construct that field from RC11 visibility and
modification-order facts; this module deliberately does not assume that
`MultiLocationRC11.Valid` already entails the Michael--Scott invariant.
-/

inductive Action (Value : Type) where
  | link (tail node : NodeId) (value : Value)
  | advanceTail (expected desired : NodeId)
  | advanceHead (expected desired : NodeId) (value : Value)
  | empty (head : NodeId)
  deriving Repr, DecidableEq

/-- A structural effect and the source point at which it takes effect. -/
structure Record (Value : Type) where
  occurrence : AtomicOccurrence Value
  point : EventId
  validation : EventId
  action : Action Value
  deriving Repr, DecidableEq

namespace Record

/-- Tail swings are concrete structural effects but not abstract operations. -/
def commit? : Record Value → Option (Commit Value)
  | ⟨_, _, _, .link _ _ value⟩ => some (.enqueue value)
  | ⟨_, _, _, .advanceTail _ _⟩ => none
  | ⟨_, _, _, .advanceHead _ _ value⟩ =>
      some (.dequeueValue value)
  | ⟨_, _, _, .empty _⟩ => some .dequeueEmpty

/-- Retain operation and validation metadata when projecting a commit. -/
def commitRecord? (record : Record Value) :
    Option (AtomicOccurrence.CommitRecord Value) :=
  record.commit?.map fun commit => {
    thread := record.occurrence.action.thread
    operation := record.occurrence.action.operation
    point := record.point
    validation := record.validation
    commit := commit
  }

/-- The actual atom carrying the structural effect's linearization point. -/
def pointOccurrence (record : Record Value) : AtomicOccurrence Value :=
  match record.action with
  | .empty head =>
      ⟨record.point,
        .dequeueNextLoad record.occurrence.action.thread
          record.occurrence.action.operation head .null⟩
  | _ => ⟨record.point, record.occurrence.action⟩

def pointAtom (record : Record Value) :
    MultiLocationRC11.Atom Site Ptr :=
  record.pointOccurrence.toRC11Atom

@[simp] theorem pointOccurrence_id (record : Record Value) :
    record.pointOccurrence.id = record.point := by
  cases record with
  | mk occurrence point validation action =>
      cases action <;> rfl

@[simp] theorem pointAtom_id (record : Record Value) :
    record.pointAtom.id = record.point :=
  record.pointOccurrence_id

/-!
`Applies` deliberately mentions the node identities seen by the CAS labels.
The smaller `Chain.Step` relation erases these identities once this frontend
obligation has checked them.
-/
def Applies
    (record : Record Value)
    (before after : Chain.State Value) : Prop :=
  match record.action with
  | .link tail node value =>
      before.nodes[before.tail]? = some tail ∧
      node ∉ before.nodes ∧
      before.tail + 1 = before.nodes.length ∧
      after = {
        before with
        nodes := before.nodes ++ [node]
        payloads := before.payloads ++ [value]
      }
  | .advanceTail expected desired =>
      before.nodes[before.tail]? = some expected ∧
      before.nodes[before.tail + 1]? = some desired ∧
      before.tail + 1 < before.nodes.length ∧
      after = { before with tail := before.tail + 1 }
  | .advanceHead expected desired value =>
      before.nodes[before.head]? = some expected ∧
      before.nodes[before.head + 1]? = some desired ∧
      before.head < before.tail ∧
      before.payloads[before.head]? = some value ∧
      after = { before with head := before.head + 1 }
  | .empty head =>
      before.nodes[before.head]? = some head ∧
      before.head + 1 = before.nodes.length ∧
      after = before

theorem Applies.toStep
    {record : Record Value}
    {before after : Chain.State Value}
    (applies : record.Applies before after) :
    Chain.Step before record.commit? after := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action with
  | link tail node value =>
      rcases applies with ⟨_, fresh, tailWasLast, rfl⟩
      exact Chain.Step.link before node value fresh tailWasLast
  | advanceTail expected desired =>
      rcases applies with ⟨_, _, hasNext, rfl⟩
      exact Chain.Step.advanceTail before hasNext
  | advanceHead expected desired value =>
      rcases applies with ⟨_, _, headBeforeTail, payload, rfl⟩
      exact Chain.Step.advanceHead before value headBeforeTail payload
  | empty head =>
      rcases applies with ⟨_, headWasLast, same⟩
      subst after
      exact Chain.Step.empty before headWasLast

/-- A fixed source effect and pre-state determine at most one post-state. -/
theorem Applies.deterministic
    {record : Record Value}
    {before firstAfter secondAfter : Chain.State Value}
    (first : record.Applies before firstAfter)
    (second : record.Applies before secondAfter) :
    firstAfter = secondAfter := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action with
  | link tail node value =>
      rcases first with ⟨_, _, _, firstShape⟩
      rcases second with ⟨_, _, _, secondShape⟩
      exact firstShape.trans secondShape.symm
  | advanceTail expected desired =>
      rcases first with ⟨_, _, _, firstShape⟩
      rcases second with ⟨_, _, _, secondShape⟩
      exact firstShape.trans secondShape.symm
  | advanceHead expected desired value =>
      rcases first with ⟨_, _, _, _, firstShape⟩
      rcases second with ⟨_, _, _, _, secondShape⟩
      exact firstShape.trans secondShape.symm
  | empty head =>
      rcases first with ⟨_, _, firstShape⟩
      rcases second with ⟨_, _, secondShape⟩
      exact firstShape.trans secondShape.symm

end Record

/-- Extract every source event that changes, or validates, queue structure. -/
def structuralRecordOfOccurrence?
    (occurrence : AtomicOccurrence Value) : Option (Record Value) :=
  match occurrence.action with
  | .enqueueLinkCAS _ _ tail node value _ true =>
      some ⟨occurrence, occurrence.id, occurrence.id,
        .link tail node value⟩
  | .enqueueHelpTailCAS _ _ expected desired _ true
  | .enqueueFinishTailCAS _ _ expected desired _ true
  | .dequeueHelpTailCAS _ _ expected desired _ true =>
      some ⟨occurrence, occurrence.id, occurrence.id,
        .advanceTail expected desired⟩
  | .dequeueHeadCAS _ _ expected desired value _ true =>
      some ⟨occurrence, occurrence.id, occurrence.id,
        .advanceHead expected desired value⟩
  | .dequeueHeadValidateEmpty _ _ head nextRead =>
      some ⟨occurrence, nextRead, occurrence.id, .empty head⟩
  | _ => none

def structuralRecordOfEvent? :
    TraceEvent Value → Option (Record Value)
  | .atomic occurrence => structuralRecordOfOccurrence? occurrence
  | _ => none

def structuralRecords
    (trace : List (TraceEvent Value)) : List (Record Value) :=
  trace.filterMap structuralRecordOfEvent?

theorem pointAtom_isRead_of_selected
    {occurrence : AtomicOccurrence Value}
    {record : Record Value}
    (selected : structuralRecordOfOccurrence? occurrence = some record) :
    record.pointAtom.IsRead := by
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
          trivial
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      trivial
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded with
      | false => simp [structuralRecordOfOccurrence?] at selected
      | true =>
          simp [structuralRecordOfOccurrence?] at selected
          subst record
          trivial

/-- Every extracted structural point is a read (a successful RMW, or the
null `next` load anchoring an empty dequeue). -/
theorem pointAtom_isRead_of_structuralRecord
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom.IsRead := by
  rcases List.mem_filterMap.mp member with
    ⟨event, eventMember, selected⟩
  cases event with
  | atomic occurrence =>
      exact pointAtom_isRead_of_selected selected
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected

theorem structuralRecordOfOccurrence_commitRecord
    (occurrence : AtomicOccurrence Value) :
    (structuralRecordOfOccurrence? occurrence).bind
        Record.commitRecord? =
      occurrence.commitRecord? := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => rfl
  | enqueueTailLoad => rfl
  | enqueueNextLoad => rfl
  | enqueueTailValidate => rfl
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;> rfl
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;> rfl
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;> rfl
  | dequeueHeadLoad => rfl
  | dequeueTailLoad => rfl
  | dequeueNextLoad => rfl
  | dequeueHeadValidate => rfl
  | dequeueHeadValidateEmpty => rfl
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;> rfl
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded <;> rfl

theorem structuralRecordOfEvent_commitRecord
    (event : TraceEvent Value) :
    (structuralRecordOfEvent? event).bind Record.commitRecord? =
      event.commitRecord? := by
  cases event with
  | atomic occurrence =>
      exact structuralRecordOfOccurrence_commitRecord occurrence
  | invokeEnqueue => rfl
  | initializePayload => rfl
  | invokeDequeue => rfl
  | readPayload => rfl
  | respondEnqueue => rfl
  | respondDequeue => rfl

/-- Structural extraction has exactly the source layer's commit projection. -/
theorem structuralCommitRecords
    (trace : List (TraceEvent Value)) :
    (structuralRecords trace).filterMap Record.commitRecord? =
      trace.filterMap TraceEvent.commitRecord? := by
  rw [structuralRecords, List.filterMap_filterMap]
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.filterMap_cons]
      rw [structuralRecordOfEvent_commitRecord, inductionHypothesis]

theorem atomicId_mem_of_atomicEvent_mem
    {occurrence : AtomicOccurrence Value}
    {trace : List (TraceEvent Value)}
    (member : TraceEvent.atomic occurrence ∈ trace) :
    occurrence.id ∈ atomicIds trace := by
  apply List.mem_map.mpr
  refine ⟨occurrence, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨.atomic occurrence, member, rfl⟩

theorem atomicOccurrence_mem_of_atomicEvent_mem
    {occurrence : AtomicOccurrence Value}
    {trace : List (TraceEvent Value)}
    (member : TraceEvent.atomic occurrence ∈ trace) :
    occurrence ∈ atomicOccurrences trace := by
  apply List.mem_filterMap.mpr
  exact ⟨.atomic occurrence, member, rfl⟩

/--
Every extracted record resolves to the exact source occurrence carrying its
linearization point.  For an empty dequeue this is the earlier null `next`
read certified by `SourceWellFormed.emptyAnchor`, not the later validation.
-/
theorem pointOccurrence_mem_of_structuralRecord
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointOccurrence ∈ atomicOccurrences trace := by
  rcases List.mem_filterMap.mp member with
    ⟨event, eventMember, selected⟩
  cases event with
  | invokeEnqueue =>
      simp [structuralRecordOfEvent?] at selected
  | initializePayload =>
      simp [structuralRecordOfEvent?] at selected
  | invokeDequeue =>
      simp [structuralRecordOfEvent?] at selected
  | readPayload =>
      simp [structuralRecordOfEvent?] at selected
  | respondEnqueue =>
      simp [structuralRecordOfEvent?] at selected
  | respondDequeue =>
      simp [structuralRecordOfEvent?] at selected
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | initializeNext =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | enqueueTailLoad =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | enqueueNextLoad =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | enqueueTailValidate =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded with
          | false =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact atomicOccurrence_mem_of_atomicEvent_mem eventMember
      | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact atomicOccurrence_mem_of_atomicEvent_mem eventMember
      | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact atomicOccurrence_mem_of_atomicEvent_mem eventMember
      | dequeueHeadLoad =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | dequeueTailLoad =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | dequeueNextLoad =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | dequeueHeadValidate =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
      | dequeueHeadValidateEmpty thread operation head nextRead =>
          simp [structuralRecordOfEvent?,
            structuralRecordOfOccurrence?] at selected
          subst record
          exact atomicOccurrence_mem_of_atomicEvent_mem
            (wellFormed.emptyAnchor eventMember).1
      | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact atomicOccurrence_mem_of_atomicEvent_mem eventMember
      | dequeueHeadCAS thread operation expected desired value observed succeeded =>
          cases succeeded with
          | false =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact atomicOccurrence_mem_of_atomicEvent_mem eventMember

/-- Every extracted anchor resolves to an actual dynamic atom identifier. -/
theorem structuralPoint_mem_of_sourceWellFormed
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.point ∈ atomicIds trace := by
  apply List.mem_map.mpr
  exact ⟨record.pointOccurrence,
    pointOccurrence_mem_of_structuralRecord wellFormed member,
    record.pointOccurrence_id⟩

/-! A structural replay retains the source records rather than only commits. -/
inductive Replay :
    Chain.State Value → List (Record Value) → Chain.State Value → Prop where
  | nil (state : Chain.State Value) : Replay state [] state
  | cons
      {before middle after : Chain.State Value}
      {record : Record Value}
      {records : List (Record Value)}
      (first : record.Applies before middle)
      (later : Replay middle records after) :
      Replay before (record :: records) after

theorem Replay.toChainReplay
    {initial final : Chain.State Value}
    {records : List (Record Value)}
    (replay : Replay initial records final) :
    Chain.Replay initial (records.filterMap Record.commit?) final := by
  induction replay with
  | nil state => exact Chain.Replay.nil state
  | @cons before middle after record records first later inductionHypothesis =>
      rcases record with ⟨occurrence, point, validation, action⟩
      cases action with
      | link tail node value =>
          exact Chain.Replay.commit (.enqueue value) _ first.toStep
            inductionHypothesis
      | advanceTail expected desired =>
          exact Chain.Replay.silent first.toStep inductionHypothesis
      | advanceHead expected desired value =>
          exact Chain.Replay.commit (.dequeueValue value) _ first.toStep
            inductionHypothesis
      | empty head =>
          exact Chain.Replay.commit .dequeueEmpty _ first.toStep
            inductionHypothesis

/-- Replay over one exact structural record list has a unique final state. -/
theorem Replay.deterministic
    {initial firstFinal secondFinal : Chain.State Value}
    {records : List (Record Value)}
    (first : Replay initial records firstFinal)
    (second : Replay initial records secondFinal) :
    firstFinal = secondFinal := by
  induction first generalizing secondFinal with
  | nil state =>
      cases second
      rfl
  | @cons before middle firstFinal record records applies later
      inductionHypothesis =>
      cases second with
      | @cons _ secondMiddle secondFinal _ _ secondApplies secondLater =>
          have sameMiddle := applies.deterministic secondApplies
          subst secondMiddle
          exact inductionHypothesis secondLater

/-!
Cross-thread order comes from a linear extension of the RC11 graph, not from
the source carrier's enumeration.  This mirrors the scheduling boundary used
by the Treiber development.
-/
theorem extendedCoherence_closed
    {candidate : MultiLocationRC11.Candidate Location Value}
    {source target : MultiLocationRC11.Atom Location Value}
    (path : MultiLocationRC11.ECO candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms := by
  induction path with
  | readsFrom edge => exact edge.closed
  | modificationOrder edge => exact edge.closed
  | readsBefore edge =>
      rcases edge with ⟨origin, readsFrom, modificationOrder, _⟩
      exact ⟨readsFrom.closed.2, modificationOrder.closed.2⟩
  | transitive first second firstClosed secondClosed =>
      exact ⟨firstClosed.1, secondClosed.2⟩

structure AtomSchedule
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) where
  atoms : List (MultiLocationRC11.Atom Site Ptr)
  permutation : atoms.Perm execution.candidate.atoms
  respectsProgramOrder :
    ∀ {source target},
      MultiLocationRC11.PO execution.candidate source target →
        MultiLocationRC11.IdBefore source.id target.id
          (atoms.map MultiLocationRC11.Atom.id)
  respectsExtendedCoherence :
    ∀ {source target},
      MultiLocationRC11.ECO execution.candidate source target →
        MultiLocationRC11.IdBefore source.id target.id
          (atoms.map MultiLocationRC11.Atom.id)

namespace AtomSchedule

def ids
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) : List EventId :=
  schedule.atoms.map MultiLocationRC11.Atom.id

theorem idsNodup
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    schedule.ids.Nodup := by
  exact (schedule.permutation.symm.map MultiLocationRC11.Atom.id).nodup
    execution.valid.atomIdsNodup

theorem atomicId_mem
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {eventId : EventId}
    (member : eventId ∈ atomicIds trace) :
    eventId ∈ schedule.ids := by
  have candidateMember : eventId ∈ execution.candidate.atomIds := by
    change eventId ∈ (projectedAtoms dummy trace).map
      MultiLocationRC11.Atom.id
    rw [projectedAtoms, List.map_append]
    apply List.mem_append.mpr
    right
    rw [List.map_map]
    rcases List.mem_map.mp member with ⟨occurrence, occurrenceMember,
      sameId⟩
    apply List.mem_map.mpr
    exact ⟨occurrence, occurrenceMember, by
      simpa [Function.comp_def, AtomicOccurrence.toRC11Atom] using sameId⟩
  exact (schedule.permutation.map MultiLocationRC11.Atom.id).mem_iff.mpr
    candidateMember

/-- The point atom reconstructed from a structural record is in the exact
source-backed RC11 carrier. -/
theorem pointAtom_mem_candidate
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom ∈ execution.candidate.atoms := by
  rw [execution.atoms_exact, projectedAtoms]
  apply List.mem_append.mpr
  right
  apply List.mem_map.mpr
  exact ⟨record.pointOccurrence,
    pointOccurrence_mem_of_structuralRecord
      execution.sourceWellFormed member,
    rfl⟩

/-- The exact point atom occurs in every atom schedule, not merely an atom
sharing its identifier. -/
theorem pointAtom_mem
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.pointAtom ∈ schedule.atoms :=
  schedule.permutation.mem_iff.mpr
    (pointAtom_mem_candidate (execution := execution) member)

theorem structuralPoint_mem
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.point ∈ schedule.ids :=
  schedule.atomicId_mem
    (structuralPoint_mem_of_sourceWellFormed
      execution.sourceWellFormed member)

end AtomSchedule

/--
Place each structural record at its anchor atom.  In particular, an empty
dequeue is placed at its earlier null-next load rather than at the later
validation occurrence that emitted the record.
-/
def recordsOn
    (trace : List (TraceEvent Value))
    (atomSchedule : List (MultiLocationRC11.Atom Site Ptr)) :
    List (Record Value) :=
  atomSchedule.flatMap fun atom =>
    (structuralRecords trace).filter fun record =>
      record.point == atom.id

theorem mem_structuralRecords_of_mem_recordsOn
    {record : Record Value}
    {trace : List (TraceEvent Value)}
    {atomSchedule : List (MultiLocationRC11.Atom Site Ptr)}
    (member : record ∈ recordsOn trace atomSchedule) :
    record ∈ structuralRecords trace := by
  rw [recordsOn, List.mem_flatMap] at member
  rcases member with ⟨atom, _, recordMember⟩
  exact (List.mem_filter.mp recordMember).1

theorem point_mem_of_mem_recordsOn
    {record : Record Value}
    {trace : List (TraceEvent Value)}
    {atomSchedule : List (MultiLocationRC11.Atom Site Ptr)}
    (member : record ∈ recordsOn trace atomSchedule) :
    record.point ∈ atomSchedule.map MultiLocationRC11.Atom.id := by
  rw [recordsOn, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, recordMember⟩
  have samePoint := (List.mem_filter.mp recordMember).2
  have samePoint' : record.point = atom.id := by
    simpa using samePoint
  exact List.mem_map.mpr ⟨atom, atomMember, samePoint'.symm⟩

/-!
An exact representation certificate for one supported execution and one
RC11-respecting atom schedule.  `recordCoverage` is the anti-oracle condition:
anchoring on the atom schedule contains every extracted structural effect
exactly once.  The replay therefore has no independently chosen record order.
-/
structure Certificate
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace) where
  atomSchedule : AtomSchedule execution
  recordCoverage :
    (recordsOn trace atomSchedule.atoms).Perm (structuralRecords trace)
  recordPointsNodup :
    ((structuralRecords trace).map Record.point).Nodup
  finalState : Chain.State Value
  replay : Replay (Chain.State.initial dummy)
    (recordsOn trace atomSchedule.atoms) finalState

namespace Certificate

def commits
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) : List (Commit Value) :=
  (recordsOn trace certificate.atomSchedule.atoms).filterMap
    Record.commit?

def commitRecords
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    List (AtomicOccurrence.CommitRecord Value) :=
  (recordsOn trace certificate.atomSchedule.atoms).filterMap
    Record.commitRecord?

/-- The scheduled commit records are exactly the source records, up to order. -/
theorem commitRecords_perm_source
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    certificate.commitRecords.Perm
      (trace.filterMap TraceEvent.commitRecord?) := by
  have filtered :=
    certificate.recordCoverage.filterMap Record.commitRecord?
  simpa [commitRecords, structuralCommitRecords] using filtered

theorem chainReplay
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    Chain.Replay (Chain.State.initial dummy)
      certificate.commits certificate.finalState :=
  certificate.replay.toChainReplay

theorem finalWellFormed
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    Chain.WellFormed certificate.finalState :=
  certificate.chainReplay.finalWellFormed
    (Chain.initial_wellFormed dummy)

theorem preservesRoot
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    Chain.Rooted dummy certificate.finalState :=
  certificate.chainReplay.preservesRooted (Chain.initial_rooted dummy)

/-- The exact source-derived commit projection is an abstract FIFO trace. -/
theorem fifoCommitTrace
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    CommitTrace [] certificate.commits
      certificate.finalState.contents := by
  simpa [Chain.State.initial, Chain.State.contents] using
    certificate.chainReplay.commitTrace
      (Chain.initial_wellFormed dummy)

/-- FIFO safety for the exact source-derived commit projection. -/
theorem fifoLegal
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (certificate : Certificate execution) :
    QueueSpec.Legal []
      (completedHistory certificate.commits)
      certificate.finalState.contents :=
  commitTrace_linearizable certificate.fifoCommitTrace

end Certificate

end WeakMemory.MSQueue.Source.Structural
