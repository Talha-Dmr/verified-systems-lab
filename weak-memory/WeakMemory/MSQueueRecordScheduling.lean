import WeakMemory.MSQueueSourceChain

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Exact record scheduling by unique points

This module isolates the finite-list fact behind `recordsOn`: bucketing a
list by a duplicate-free list of points is only a permutation when every
item's point is covered.  The result removes `Certificate.recordCoverage` as
an algorithm-specific proof obligation once point coverage is known.
-/

/-- Bucket `items` in the order supplied by `points`. -/
def recordsAtPoints
    [BEq Point]
    (items : List Item)
    (points : List Point)
    (pointOf : Item → Point) : List Item :=
  points.flatMap fun point =>
    items.filter fun item => pointOf item == point

/--
Filtering out items at a point not mentioned by the bucket list does not
change any bucket.
-/
theorem recordsAtPoints_filter_unmentioned
    [BEq Point] [LawfulBEq Point]
    {items : List Item}
    {points : List Point}
    {pointOf : Item → Point}
    {excluded : Point}
    (unmentioned : excluded ∉ points) :
    recordsAtPoints items points pointOf =
      recordsAtPoints
        (items.filter fun item => !(pointOf item == excluded))
        points pointOf := by
  induction points with
  | nil => rfl
  | cons point points inductionHypothesis =>
      have unmentionedParts :
          excluded ≠ point ∧ excluded ∉ points := by
        simpa using unmentioned
      simp only [recordsAtPoints, List.flatMap_cons]
      congr 1
      · rw [List.filter_filter]
        apply List.filter_congr
        intro item itemMember
        by_cases matchAtPoint : pointOf item == point
        · have samePoint : pointOf item = point :=
            beq_iff_eq.mp matchAtPoint
          have differentPoint : pointOf item ≠ excluded := by
            intro sameExcluded
            exact unmentionedParts.1 (sameExcluded.symm.trans samePoint)
          have excludedComparison :
              (pointOf item == excluded) = false :=
            beq_eq_false_iff_ne.mpr differentPoint
          simp [matchAtPoint, excludedComparison]
        · simp [matchAtPoint]
      · exact inductionHypothesis unmentionedParts.2

/--
Unique, covering point buckets contain every item exactly once, although
they may reorder items from different buckets.
-/
theorem recordsAtPoints_perm
    [BEq Point] [LawfulBEq Point]
    {items : List Item}
    {points : List Point}
    {pointOf : Item → Point}
    (pointsNodup : points.Nodup)
    (covered : ∀ item ∈ items, pointOf item ∈ points) :
    (recordsAtPoints items points pointOf).Perm items := by
  induction points generalizing items with
  | nil =>
      have itemsEmpty : items = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro item itemMember
        have pointMember := covered item itemMember
        exact (by simp at pointMember)
      subst items
      exact List.Perm.refl []
  | cons point points inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp pointsNodup
      let remaining :=
        items.filter fun item => !(pointOf item == point)
      have remainingCovered :
          ∀ item ∈ remaining, pointOf item ∈ points := by
        intro item itemMember
        have filtered := List.mem_filter.mp itemMember
        have pointMember := covered item filtered.1
        simp only [List.mem_cons] at pointMember
        rcases pointMember with samePoint | pointInTail
        · subst point
          simp at filtered
        · exact pointInTail
      have laterBuckets :=
        recordsAtPoints_filter_unmentioned
          (items := items)
          (points := points)
          (pointOf := pointOf)
          nodupParts.1
      have remainingPermutation :=
        inductionHypothesis nodupParts.2 remainingCovered
      change
        (items.filter (fun item => pointOf item == point) ++
          recordsAtPoints items points pointOf).Perm items
      rw [laterBuckets]
      exact
        (List.Perm.append_left _
          (by simpa only [remaining] using remainingPermutation)).trans
          (List.filter_append_perm
            (fun item => pointOf item == point) items)

/-- `recordsOn` is generic point bucketing over scheduled atom IDs. -/
theorem recordsOn_eq_recordsAtPoints
    (trace : List (TraceEvent Value))
    (atomSchedule : List (MultiLocationRC11.Atom Site Ptr)) :
    recordsOn trace atomSchedule =
      recordsAtPoints
        (structuralRecords trace)
        (atomSchedule.map MultiLocationRC11.Atom.id)
        Record.point := by
  simp [recordsOn, recordsAtPoints, List.flatMap_map]

/--
An atom schedule covers the extracted structural records exactly whenever
its IDs are unique and every extracted anchor occurs in it.
-/
theorem recordsOn_perm_structuralRecords
    {trace : List (TraceEvent Value)}
    {atomSchedule : List (MultiLocationRC11.Atom Site Ptr)}
    (scheduleIdsNodup :
      (atomSchedule.map MultiLocationRC11.Atom.id).Nodup)
    (recordPointCoverage :
      ∀ record ∈ structuralRecords trace,
        record.point ∈ atomSchedule.map MultiLocationRC11.Atom.id) :
    (recordsOn trace atomSchedule).Perm (structuralRecords trace) := by
  rw [recordsOn_eq_recordsAtPoints]
  exact recordsAtPoints_perm scheduleIdsNodup recordPointCoverage

namespace AtomSchedule

/--
Every source-backed atom schedule covers the structural record list exactly;
the fact follows from schedule ID uniqueness and the checked source anchor.
-/
theorem recordsOn_perm
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    (recordsOn trace schedule.atoms).Perm (structuralRecords trace) := by
  apply recordsOn_perm_structuralRecords schedule.idsNodup
  intro record recordMember
  exact schedule.structuralPoint_mem recordMember

end AtomSchedule

/-! ## Uniqueness of retroactive empty points -/

/-- Empty validations retained with their full source occurrence. -/
private def emptyValidationOccurrence? :
    TraceEvent Value → Option (AtomicOccurrence Value)
  | .atomic occurrence@⟨_, .dequeueHeadValidateEmpty ..⟩ => some occurrence
  | _ => none

private def emptyValidationOccurrences
    (events : List (TraceEvent Value)) :
    List (AtomicOccurrence Value) :=
  events.filterMap emptyValidationOccurrence?

private theorem emptyValidationOccurrences_cons
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    emptyValidationOccurrences (event :: rest) =
      emptyValidationOccurrences [event] ++
        emptyValidationOccurrences rest := by
  change List.filterMap emptyValidationOccurrence? (event :: rest) =
    List.filterMap emptyValidationOccurrence? [event] ++
      List.filterMap emptyValidationOccurrence? rest
  rw [show event :: rest = [event] ++ rest by rfl,
    List.filterMap_append]

private theorem invocationIds_cons_append
    (event : TraceEvent Value)
    (rest : List (TraceEvent Value)) :
    invocationIds (event :: rest) =
      invocationIds [event] ++ invocationIds rest := by
  change List.filterMap TraceEvent.invocationId? (event :: rest) =
    List.filterMap TraceEvent.invocationId? [event] ++
      List.filterMap TraceEvent.invocationId? rest
  rw [show event :: rest = [event] ++ rest by rfl,
    List.filterMap_append]

/-
An in-flight dequeue has one unit of "empty credit" until it either commits
empty, commits a value, or remains pending.  This small accounting invariant
avoids baking terminal-operation uniqueness into `SourceWellFormed`.
-/
private def emptyCredit
    (target : OperationId) : LocalState Value → Nat
  | .dequeueLoadingHead operation
  | .dequeueLoadingTail operation _
  | .dequeueLoadingNext operation _ _
  | .dequeueValidatingHead operation _ _ _ _
  | .dequeueHelpingTail operation _ _
  | .dequeueReadingPayload operation _ _
  | .dequeueSwingingHead operation _ _ _ =>
      if operation = target then 1 else 0
  | _ => 0

private theorem localStep_emptyAccounting
    {thread : ThreadId}
    {initial final : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread initial event final)
    (target : OperationId) :
    List.count target
        ((emptyValidationOccurrences [event]).map
          (fun occurrence => occurrence.action.operation)) +
        emptyCredit target final ≤
      List.count target (invocationIds [event]) +
        emptyCredit target initial := by
  cases step <;>
    simp [emptyValidationOccurrences, emptyValidationOccurrence?,
      emptyCredit, invocationIds, TraceEvent.invocationId?,
      AtomicAction.operation, List.count_cons] <;> omega

private theorem run_emptyAccounting
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    (target : OperationId) :
    List.count target
        ((emptyValidationOccurrences events).map
          (fun occurrence => occurrence.action.operation)) +
        emptyCredit target final ≤
      List.count target (invocationIds events) +
        emptyCredit target initial := by
  induction run with
  | nil state => simp [emptyValidationOccurrences, invocationIds]
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      have firstAccounting := localStep_emptyAccounting first target
      have laterAccounting := inductionHypothesis
      rw [emptyValidationOccurrences_cons,
        invocationIds_cons_append, List.map_append,
        List.count_append, List.count_append]
      omega

private theorem invocationIds_threadTrace_sublist
    (trace : List (TraceEvent Value))
    (thread : ThreadId) :
    (invocationIds (threadTrace trace thread)).Sublist
      (invocationIds trace) := by
  exact (List.filter_sublist (p := fun event => event.thread == thread)
    (l := trace)).filterMap TraceEvent.invocationId?

private theorem emptyValidationOperationsNodup
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    (thread : ThreadId) :
    ((emptyValidationOccurrences (threadTrace trace thread)).map
      (fun occurrence => occurrence.action.operation)).Nodup := by
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  apply List.nodup_iff_count.mpr
  intro operation
  have accounting := run_emptyAccounting run operation
  have localInvocationNodup :
      (invocationIds (threadTrace trace thread)).Nodup :=
    (invocationIds_threadTrace_sublist trace thread).nodup
      wellFormed.invocationIdsNodup
  have invocationBound :=
    (List.nodup_iff_count.mp localInvocationNodup) operation
  simp [emptyCredit] at accounting
  omega

private theorem emptyValidationOccurrence_mem_thread
    {trace : List (TraceEvent Value)}
    {id thread operation head point : Nat}
    (member :
      TraceEvent.atomic
          ⟨id, AtomicAction.dequeueHeadValidateEmpty
            thread operation head point⟩ ∈ trace) :
    (⟨id, AtomicAction.dequeueHeadValidateEmpty
        thread operation head point⟩ : AtomicOccurrence Value) ∈
      emptyValidationOccurrences (threadTrace trace thread) := by
  apply List.mem_filterMap.mpr
  refine ⟨TraceEvent.atomic
    ⟨id, AtomicAction.dequeueHeadValidateEmpty
      thread operation head point⟩, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨member, by simp [TraceEvent.thread, AtomicAction.thread]⟩

private theorem eq_of_mem_of_map_nodup
    {items : List Item}
    {key : Item → Point}
    (keysNodup : (items.map key).Nodup)
    {left right : Item}
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameKey : key left = key right) :
    left = right := by
  induction items generalizing left right with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp keysNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (nodupParts.1
            (List.mem_map.mpr ⟨right, rightMember, sameKey.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (nodupParts.1
            (List.mem_map.mpr ⟨left, leftMember, sameKey⟩))
        · exact inductionHypothesis nodupParts.2
            leftMember rightMember sameKey

/-- Two empty validations of one local operation are the same occurrence. -/
private theorem emptyValidationOccurrence_eq
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {firstId secondId thread operation firstHead secondHead
      firstPoint secondPoint : Nat}
    (firstMember :
      TraceEvent.atomic
          ⟨firstId, AtomicAction.dequeueHeadValidateEmpty
            thread operation firstHead firstPoint⟩ ∈ trace)
    (secondMember :
      TraceEvent.atomic
          ⟨secondId, AtomicAction.dequeueHeadValidateEmpty
            thread operation secondHead secondPoint⟩ ∈ trace) :
    (⟨firstId, AtomicAction.dequeueHeadValidateEmpty
        thread operation firstHead firstPoint⟩ : AtomicOccurrence Value) =
      ⟨secondId, AtomicAction.dequeueHeadValidateEmpty
        thread operation secondHead secondPoint⟩ := by
  apply eq_of_mem_of_map_nodup
    (items := emptyValidationOccurrences (threadTrace trace thread))
    (key := fun occurrence => occurrence.action.operation)
    (emptyValidationOperationsNodup wellFormed thread)
    (emptyValidationOccurrence_mem_thread firstMember)
    (emptyValidationOccurrence_mem_thread secondMember)
  rfl

/-! ## Structural-point injectivity -/

private theorem occurrence_eq_of_selected
    {occurrence : AtomicOccurrence Value}
    {record : Record Value}
    (selected :
      structuralRecordOfOccurrence? occurrence = some record) :
    record.occurrence = occurrence := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl

private theorem validation_eq_id_of_selected
    {occurrence : AtomicOccurrence Value}
    {record : Record Value}
    (selected :
      structuralRecordOfOccurrence? occurrence = some record) :
    record.validation = occurrence.id := by
  rcases occurrence with ⟨id, action⟩
  cases action with
  | initializeNext => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | enqueueTailValidate => simp [structuralRecordOfOccurrence?] at selected
  | enqueueLinkCAS thread operation tail node value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHeadLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueTailLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueNextLoad => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidate => simp [structuralRecordOfOccurrence?] at selected
  | dequeueHeadValidateEmpty thread operation head nextRead =>
      simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl
  | dequeueHeadCAS thread operation expected desired value observed succeeded =>
      cases succeeded <;>
        simp [structuralRecordOfOccurrence?] at selected
      subst record
      rfl

private theorem recordOccurrence_mem_trace
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    TraceEvent.atomic record.occurrence ∈ trace := by
  rcases List.mem_filterMap.mp member with
    ⟨event, eventMember, selected⟩
  cases event with
  | atomic occurrence =>
      rw [occurrence_eq_of_selected selected]
      exact eventMember
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected

private theorem extractedRecord_classification
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    (record.validation = record.point ∧
      record.pointOccurrence = record.occurrence ∧
      record.pointOccurrence.action.succeededCAS = true) ∨
    ∃ thread operation head,
      record.occurrence =
        ⟨record.validation,
          AtomicAction.dequeueHeadValidateEmpty
            thread operation head record.point⟩ ∧
      record.action = .empty head := by
  rcases List.mem_filterMap.mp member with
    ⟨event, eventMember, selected⟩
  cases event with
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected
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
          | false => simp [structuralRecordOfEvent?,
              structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact Or.inl ⟨rfl, rfl, rfl⟩

      | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false => simp [structuralRecordOfEvent?,
              structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact Or.inl ⟨rfl, rfl, rfl⟩
      | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false => simp [structuralRecordOfEvent?,
              structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact Or.inl ⟨rfl, rfl, rfl⟩
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
          exact Or.inr ⟨thread, operation, head, rfl, rfl⟩
      | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded with
          | false => simp [structuralRecordOfEvent?,
              structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact Or.inl ⟨rfl, rfl, rfl⟩
      | dequeueHeadCAS thread operation expected desired value observed succeeded =>
          cases succeeded with
          | false => simp [structuralRecordOfEvent?,
              structuralRecordOfOccurrence?] at selected
          | true =>
              simp [structuralRecordOfEvent?,
                structuralRecordOfOccurrence?] at selected
              subst record
              exact Or.inl ⟨rfl, rfl, rfl⟩

private theorem structuralRecords_eq_occurrence_filterMap
    (trace : List (TraceEvent Value)) :
    structuralRecords trace =
      (atomicOccurrences trace).filterMap
        structuralRecordOfOccurrence? := by
  rw [structuralRecords, atomicOccurrences,
    List.filterMap_filterMap]
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases event with
      | atomic occurrence =>
          cases selected : structuralRecordOfOccurrence? occurrence <;>
            simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
              selected, inductionHypothesis]
      | invokeEnqueue =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]
      | initializePayload =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]
      | invokeDequeue =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]
      | readPayload =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]
      | respondEnqueue =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]
      | respondDequeue =>
          simp [structuralRecordOfEvent?, TraceEvent.atomicOccurrence?,
            inductionHypothesis]

private theorem filterMap_key_nodup
    {items : List Item}
    {sourceKey : Item → Point}
    {select : Item → Option Selected}
    {selectedKey : Selected → Point}
    (sourceKeysNodup : (items.map sourceKey).Nodup)
    (keyPreserved :
      ∀ item selected,
        select item = some selected →
          selectedKey selected = sourceKey item) :
    ((items.filterMap select).map selectedKey).Nodup := by
  induction items with
  | nil => simp
  | cons item items inductionHypothesis =>
      have sourceParts := List.nodup_cons.mp sourceKeysNodup
      cases selected : select item with
      | none =>
          simp only [List.filterMap_cons, selected]
          exact inductionHypothesis sourceParts.2
      | some chosen =>
          simp only [List.filterMap_cons, selected, List.map_cons,
            List.nodup_cons]
          constructor
          · intro chosenKeyMember
            rcases List.mem_map.mp chosenKeyMember with
              ⟨later, laterMember, sameKey⟩
            rcases List.mem_filterMap.mp laterMember with
              ⟨laterItem, laterItemMember, laterSelected⟩
            apply sourceParts.1
            apply List.mem_map.mpr
            refine ⟨laterItem, laterItemMember, ?_⟩
            calc
              sourceKey laterItem = selectedKey later :=
                (keyPreserved laterItem later laterSelected).symm
              _ = selectedKey chosen := sameKey
              _ = sourceKey item := keyPreserved item chosen selected
          · exact inductionHypothesis sourceParts.2

private theorem structuralValidationNodup
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace) :
    ((structuralRecords trace).map Record.validation).Nodup := by
  rw [structuralRecords_eq_occurrence_filterMap]
  apply filterMap_key_nodup wellFormed.atomicIdsNodup
  intro occurrence record selected
  exact validation_eq_id_of_selected selected

private theorem structuralValidation_eq_of_point_eq
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {left right : Record Value}
    (leftMember : left ∈ structuralRecords trace)
    (rightMember : right ∈ structuralRecords trace)
    (samePoint : left.point = right.point) :
    left.validation = right.validation := by
  have samePointOccurrence :
      left.pointOccurrence = right.pointOccurrence := by
    apply eq_of_mem_of_map_nodup
      (items := atomicOccurrences trace)
      (key := AtomicOccurrence.id)
      wellFormed.atomicIdsNodup
      (pointOccurrence_mem_of_structuralRecord
        wellFormed leftMember)
      (pointOccurrence_mem_of_structuralRecord
        wellFormed rightMember)
    simpa using samePoint
  rcases extractedRecord_classification leftMember with
    leftDirect | leftEmpty
  · rcases extractedRecord_classification rightMember with
      rightDirect | rightEmpty
    · exact leftDirect.1.trans
        (samePoint.trans rightDirect.1.symm)
    · obtain ⟨thread, operation, head,
          occurrenceShape, actionShape⟩ := rightEmpty
      have rightFails :
          right.pointOccurrence.action.succeededCAS = false := by
        simp [Record.pointOccurrence, actionShape, occurrenceShape,
          AtomicAction.thread, AtomicAction.operation,
          AtomicAction.succeededCAS]
      have sameSuccess := congrArg
        (fun occurrence => occurrence.action.succeededCAS)
        samePointOccurrence
      rw [leftDirect.2.2, rightFails] at sameSuccess
      contradiction
  · rcases extractedRecord_classification rightMember with
      rightDirect | rightEmpty
    · obtain ⟨thread, operation, head,
          occurrenceShape, actionShape⟩ := leftEmpty
      have leftFails :
          left.pointOccurrence.action.succeededCAS = false := by
        simp [Record.pointOccurrence, actionShape, occurrenceShape,
          AtomicAction.thread, AtomicAction.operation,
          AtomicAction.succeededCAS]
      have sameSuccess := congrArg
        (fun occurrence => occurrence.action.succeededCAS)
        samePointOccurrence
      rw [leftFails, rightDirect.2.2] at sameSuccess
      contradiction
    · obtain ⟨leftThread, leftOperation, leftHead,
          leftOccurrenceShape, leftActionShape⟩ := leftEmpty
      obtain ⟨rightThread, rightOperation, rightHead,
          rightOccurrenceShape, rightActionShape⟩ := rightEmpty
      have leftPointShape :
          left.pointOccurrence =
            ⟨left.point,
              AtomicAction.dequeueNextLoad leftThread leftOperation
                leftHead .null⟩ := by
        simp [Record.pointOccurrence, leftActionShape,
          leftOccurrenceShape, AtomicAction.thread,
          AtomicAction.operation]
      have rightPointShape :
          right.pointOccurrence =
            ⟨right.point,
              AtomicAction.dequeueNextLoad rightThread rightOperation
                rightHead .null⟩ := by
        simp [Record.pointOccurrence, rightActionShape,
          rightOccurrenceShape, AtomicAction.thread,
          AtomicAction.operation]
      rw [leftPointShape, rightPointShape] at samePointOccurrence
      have sameAction := congrArg AtomicOccurrence.action
        samePointOccurrence
      injection sameAction with sameThread sameOperation sameHead
      cases sameThread
      cases sameOperation
      have leftEventMember := recordOccurrence_mem_trace leftMember
      have rightEventMember := recordOccurrence_mem_trace rightMember
      rw [leftOccurrenceShape] at leftEventMember
      rw [rightOccurrenceShape] at rightEventMember
      exact congrArg AtomicOccurrence.id
        (emptyValidationOccurrence_eq wellFormed
          leftEventMember rightEventMember)

private theorem nodup_map_of_refinement
    {items : List Item}
    {fineKey : Item → Fine}
    {coarseKey : Item → Coarse}
    (fineNodup : (items.map fineKey).Nodup)
    (refines :
      ∀ left ∈ items, ∀ right ∈ items,
        coarseKey left = coarseKey right →
          fineKey left = fineKey right) :
    (items.map coarseKey).Nodup := by
  induction items with
  | nil => simp
  | cons head tail inductionHypothesis =>
      have fineParts := List.nodup_cons.mp fineNodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro coarseMember
        rcases List.mem_map.mp coarseMember with
          ⟨later, laterMember, sameCoarse⟩
        apply fineParts.1
        apply List.mem_map.mpr
        refine ⟨later, laterMember, ?_⟩
        exact (refines head (by simp) later (by simp [laterMember])
          sameCoarse.symm).symm
      · apply inductionHypothesis fineParts.2
        intro left leftMember right rightMember sameCoarse
        exact refines left (by simp [leftMember])
          right (by simp [rightMember]) sameCoarse

/-- Source well-formedness makes all extracted structural anchor points
unique, including retroactive empty-dequeue anchors. -/
theorem recordPointsNodup_of_sourceWellFormed
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace) :
    ((structuralRecords trace).map Record.point).Nodup := by
  apply nodup_map_of_refinement
    (fineKey := Record.validation)
    (coarseKey := Record.point)
    (structuralValidationNodup wellFormed)
  intro left leftMember right rightMember samePoint
  exact structuralValidation_eq_of_point_eq wellFormed
    leftMember rightMember samePoint

/-- Within a well-formed source trace, the anchor point identifies the whole
extracted structural record. -/
theorem structuralRecord_eq_of_point_eq
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {left right : Record Value}
    (leftMember : left ∈ structuralRecords trace)
    (rightMember : right ∈ structuralRecords trace)
    (samePoint : left.point = right.point) :
    left = right :=
  eq_of_mem_of_map_nodup
    (recordPointsNodup_of_sourceWellFormed wellFormed)
    leftMember rightMember samePoint

namespace Certificate

/--
Build an exact certificate from the substantive replay obligations.  Record
coverage is derived, rather than supplied by the caller.
-/
def ofReplay
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    (atomSchedule : AtomSchedule execution)
    (finalState : Chain.State Value)
    (replay : Replay (Chain.State.initial dummy)
      (recordsOn trace atomSchedule.atoms) finalState) :
    Certificate execution where
  atomSchedule := atomSchedule
  recordCoverage := atomSchedule.recordsOn_perm
  recordPointsNodup :=
    recordPointsNodup_of_sourceWellFormed
      execution.sourceWellFormed
  finalState := finalState
  replay := replay

end Certificate

end WeakMemory.MSQueue.Source.Structural
