import WeakMemory.MSQueueSourceHistory
import WeakMemory.MSQueueSourceHeadProvenance
import WeakMemory.MSQueueRecordPrefix

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Per-thread equivalence of source and scheduled queue commits

An atom schedule may reorder commits owned by different threads, but its
program-order obligation prevents it from reversing two commits of one
thread.  Empty dequeues require one extra argument: their structural point is
the null `next` load immediately preceding the later validation occurrence in
the local source trace.
-/

private theorem idBefore_asymm
    {first second : EventId}
    {order : List EventId}
    (forward : MultiLocationRC11.IdBefore first second order) :
    ¬ MultiLocationRC11.IdBefore second first order := by
  intro reverse
  exact (Nat.not_lt_of_ge (Nat.le_of_lt forward.2.2)) reverse.2.2

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

/-- Position order in a duplicate-free list has the expected pair sublist. -/
private theorem pair_sublist_of_idBefore
    {first second : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (before : MultiLocationRC11.IdBefore first second order) :
    [first, second].Sublist order := by
  induction order with
  | nil =>
      have impossible : first ∈ ([] : List EventId) := before.first_mem
      simp at impossible
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp noDuplicates
      by_cases firstHead : first = head
      · subst head
        have secondNeFirst : second ≠ first := by
          intro same
          subst second
          exact Nat.lt_irrefl _ before.2.2
        have secondMember : second ∈ tail := by
          have member := before.second_mem
          simpa [secondNeFirst] using member
        exact .cons_cons first
          (List.singleton_sublist.mpr secondMember)
      · have firstMember : first ∈ tail := by
          have member := before.first_mem
          simpa [firstHead] using member
        have secondHead : second ≠ head := by
          intro same
          subst head
          have firstNeSecond : first ≠ second := firstHead
          have firstBeq : (second == first) = false :=
            beq_eq_false_iff_ne.mpr firstNeSecond.symm
          have impossible : tail.idxOf first + 1 < 0 := by
            simpa [List.idxOf_cons, firstBeq] using before.2.2
          omega
        have secondMember : second ∈ tail := by
          have member := before.second_mem
          simpa [secondHead] using member
        have headNeFirst : head ≠ first := Ne.symm firstHead
        have headNeSecond : head ≠ second := Ne.symm secondHead
        have headBeqFirst : (head == first) = false :=
          beq_eq_false_iff_ne.mpr headNeFirst
        have headBeqSecond : (head == second) = false :=
          beq_eq_false_iff_ne.mpr headNeSecond
        have tailBefore :
            MultiLocationRC11.IdBefore first second tail := by
          refine ⟨firstMember, secondMember, ?_⟩
          simpa [List.idxOf_cons, headBeqFirst, headBeqSecond] using
            before.2.2
        exact (inductionHypothesis nodupParts.2 tailBefore).cons head

/-- Strict identifier order restricts to any duplicate-free sublist. -/
private theorem idBefore_of_sublist
    {first second : EventId}
    {smaller larger : List EventId}
    (sublist : smaller.Sublist larger)
    (largerNodup : larger.Nodup)
    (firstMember : first ∈ smaller)
    (secondMember : second ∈ smaller)
    (before : MultiLocationRC11.IdBefore first second larger) :
    MultiLocationRC11.IdBefore first second smaller := by
  have smallerNodup := sublist.nodup largerNodup
  have different : first ≠ second := by
    intro same
    subst second
    exact MultiLocationRC11.IdBefore.irreflexive before
  rcases MultiLocationRC11.IdBefore.total
      smallerNodup firstMember secondMember different with
    forward | reverse
  · exact forward
  · have reversePair := pair_sublist_of_idBefore smallerNodup reverse
    have reverseLarger := MultiLocationRC11.IdBefore.of_pair_sublist
      largerNodup (reversePair.trans sublist)
    exact (idBefore_asymm before reverseLarger).elim

/-- Consecutive elements of a duplicate-free list are identifier-adjacent. -/
private theorem idAdjacent_append_pair
    (leading trailing : List EventId)
    (first second : EventId)
    (noDuplicates :
      (leading ++ first :: second :: trailing).Nodup) :
    MultiLocationRC11.IdAdjacent first second
      (leading ++ first :: second :: trailing) := by
  have firstNotLeading : first ∉ leading := by
    intro member
    exact (List.nodup_append.mp noDuplicates).2.2
      first member first (by simp) rfl
  have secondNotLeading : second ∉ leading := by
    intro member
    exact (List.nodup_append.mp noDuplicates).2.2
      second member second (by simp) rfl
  have firstNeSecond : first ≠ second := by
    have suffixNodup := (List.nodup_append.mp noDuplicates).2.1
    intro same
    subst second
    exact (List.nodup_cons.mp suffixNodup).1 (by simp)
  have firstBeforeSecond :
      MultiLocationRC11.IdBefore first second
        (leading ++ first :: second :: trailing) :=
    MultiLocationRC11.IdBefore.of_pair_sublist noDuplicates (by simp)
  refine ⟨firstBeforeSecond, ?_⟩
  intro middle between
  have firstIndex :
      (leading ++ first :: second :: trailing).idxOf first =
        leading.length := by
    simp [List.idxOf_append, firstNotLeading]
  have secondIndex :
      (leading ++ first :: second :: trailing).idxOf second =
        leading.length + 1 := by
    have suffixIndex :
        (first :: second :: trailing).idxOf second = 1 := by
      have firstBeqSecond : (first == second) = false :=
        beq_eq_false_iff_ne.mpr firstNeSecond
      simp [List.idxOf_cons, firstBeqSecond]
    rw [List.idxOf_append, if_neg secondNotLeading, suffixIndex]
    omega
  have lower := between.1.2.2
  have upper := between.2.2.2
  rw [firstIndex] at lower
  rw [secondIndex] at upper
  omega

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
  | dequeueHeadValidateEmpty =>
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
  | dequeueHeadValidateEmpty =>
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

private theorem recordOccurrence_id_eq_validation
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.occurrence.id = record.validation := by
  rcases List.mem_filterMap.mp member with
    ⟨event, _eventMember, selected⟩
  cases event with
  | atomic occurrence =>
      have occurrenceShape := occurrence_eq_of_selected selected
      have validationShape := validation_eq_id_of_selected selected
      rw [occurrenceShape, validationShape]
  | invokeEnqueue => simp [structuralRecordOfEvent?] at selected
  | initializePayload => simp [structuralRecordOfEvent?] at selected
  | invokeDequeue => simp [structuralRecordOfEvent?] at selected
  | readPayload => simp [structuralRecordOfEvent?] at selected
  | respondEnqueue => simp [structuralRecordOfEvent?] at selected
  | respondDequeue => simp [structuralRecordOfEvent?] at selected

/-- Structural validation identifiers retain source atomic order. -/
private theorem structuralValidationIds_sublist
    (trace : List (TraceEvent Value)) :
    ((structuralRecords trace).map Record.validation).Sublist
      (atomicIds trace) := by
  induction trace with
  | nil => exact .slnil
  | cons event rest inductionHypothesis =>
      cases event with
      | atomic occurrence =>
          cases selected : structuralRecordOfOccurrence? occurrence with
          | none =>
              simpa [structuralRecords, structuralRecordOfEvent?,
                atomicIds, atomicOccurrences,
                TraceEvent.atomicOccurrence?, selected] using
                inductionHypothesis.cons occurrence.id
          | some record =>
              have validation := validation_eq_id_of_selected selected
              simpa [structuralRecords, structuralRecordOfEvent?,
                atomicIds, atomicOccurrences,
                TraceEvent.atomicOccurrence?, selected, validation] using
                inductionHypothesis.cons_cons occurrence.id
      | invokeEnqueue =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis
      | initializePayload =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis
      | invokeDequeue =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis
      | readPayload =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis
      | respondEnqueue =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis
      | respondDequeue =>
          simpa [structuralRecords, structuralRecordOfEvent?,
            atomicIds, atomicOccurrences,
            TraceEvent.atomicOccurrence?] using inductionHypothesis

private theorem recordValidationBefore
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {first second : Record Value}
    (ordered : [first, second].Sublist (structuralRecords trace)) :
    MultiLocationRC11.IdBefore first.validation second.validation
      (atomicIds trace) := by
  apply MultiLocationRC11.IdBefore.of_pair_sublist
    wellFormed.atomicIdsNodup
  exact (ordered.map Record.validation).trans
    (structuralValidationIds_sublist trace)

private theorem recordPointClassification
    {trace : List (TraceEvent Value)}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    record.validation = record.point ∨
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
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | enqueueTailLoad =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | enqueueNextLoad =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | enqueueTailValidate =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded <;>
            simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
              at selected
          subst record
          exact Or.inl rfl
      | enqueueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded <;>
            simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
              at selected
          subst record
          exact Or.inl rfl
      | enqueueFinishTailCAS thread operation expected desired observed succeeded =>
          cases succeeded <;>
            simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
              at selected
          subst record
          exact Or.inl rfl
      | dequeueHeadLoad =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | dequeueTailLoad =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | dequeueNextLoad =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | dequeueHeadValidate =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
      | dequeueHeadValidateEmpty thread operation head nextRead =>
          simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
            at selected
          subst record
          exact Or.inr ⟨thread, operation, head, rfl, rfl⟩
      | dequeueHelpTailCAS thread operation expected desired observed succeeded =>
          cases succeeded <;>
            simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
              at selected
          subst record
          exact Or.inl rfl
      | dequeueHeadCAS thread operation expected desired value observed succeeded =>
          cases succeeded <;>
            simp [structuralRecordOfEvent?, structuralRecordOfOccurrence?]
              at selected
          subst record
          exact Or.inl rfl

private theorem commitRecord_thread
    {record : Record Value}
    {entry : AtomicOccurrence.CommitRecord Value}
    (selected : record.commitRecord? = some entry) :
    entry.thread = record.occurrence.action.thread := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;>
    simp [Record.commitRecord?, Record.commit?] at selected
  all_goals subst entry
  all_goals rfl

private theorem atomicOccurrence_mem_threadTrace
    {trace : List (TraceEvent Value)}
    {occurrence : AtomicOccurrence Value}
    {thread : ThreadId}
    (member : TraceEvent.atomic occurrence ∈ trace)
    (sameThread : occurrence.action.thread = thread) :
    occurrence ∈ atomicOccurrences (threadTrace trace thread) := by
  apply List.mem_filterMap.mpr
  refine ⟨.atomic occurrence, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨member, by simp [TraceEvent.thread, sameThread]⟩

private theorem emptyPointAdjacent
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {record : Record Value}
    (member : record ∈ structuralRecords trace)
    {thread operation head : Nat}
    (emptyShape :
      record.occurrence =
        ⟨record.validation,
          AtomicAction.dequeueHeadValidateEmpty
            thread operation head record.point⟩) :
    MultiLocationRC11.IdAdjacent record.point record.validation
      (atomicIds (threadTrace trace thread)) := by
  have validationMember :
      TraceEvent.atomic
        ⟨record.validation,
          AtomicAction.dequeueHeadValidateEmpty
            thread operation head record.point⟩ ∈ trace := by
    rw [← emptyShape]
    exact recordOccurrence_mem_trace member
  obtain ⟨leading, headLoadId, tailLoadId, trailing, threadShape,
      _headMember, _tailMember, _pointMember, _headTail, _tailPoint,
      _pointValidation⟩ :=
    wellFormed.dequeueEmptyValidation_provenance validationMember
  have idsShape :
      atomicIds (threadTrace trace thread) =
        (atomicIds leading ++ [headLoadId, tailLoadId]) ++
          record.point :: record.validation :: atomicIds trailing := by
    rw [threadShape]
    simp [atomicIds, atomicOccurrences,
      TraceEvent.atomicOccurrence?, List.append_assoc]
  have localNodup :
      (atomicIds (threadTrace trace thread)).Nodup :=
    (atomicIds_threadTrace_sublist trace thread).nodup
      wellFormed.atomicIdsNodup
  rw [idsShape] at localNodup ⊢
  exact idAdjacent_append_pair _ _ _ _ localNodup

private theorem pointOccurrence_thread
    (record : Record Value) :
    record.pointOccurrence.action.thread =
      record.occurrence.action.thread := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> rfl

/-- Two source-ordered commits of one thread retain their anchor order.

For an empty dequeue the anchor is the null `next` read immediately before
the validation.  Thus a later empty anchor cannot move before an earlier
validation: that validation would lie strictly between the later anchor and
its adjacent validation. -/
private theorem recordPointBefore
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {first second : Record Value}
    (ordered : [first, second].Sublist (structuralRecords trace))
    {thread : ThreadId}
    (firstThread : first.occurrence.action.thread = thread)
    (secondThread : second.occurrence.action.thread = thread) :
    MultiLocationRC11.IdBefore first.point second.point
      (atomicIds trace) := by
  have firstMember : first ∈ structuralRecords trace :=
    ordered.subset (by simp)
  have secondMember : second ∈ structuralRecords trace :=
    ordered.subset (by simp)
  have validationBefore :=
    recordValidationBefore wellFormed ordered
  have firstValidationMember :
      first.validation ∈ atomicIds (threadTrace trace thread) := by
    have occurrenceMember := recordOccurrence_mem_trace firstMember
    have localOccurrence := atomicOccurrence_mem_threadTrace
      occurrenceMember firstThread
    exact List.mem_map.mpr ⟨first.occurrence, localOccurrence,
      recordOccurrence_id_eq_validation firstMember⟩
  have secondValidationMember :
      second.validation ∈ atomicIds (threadTrace trace thread) := by
    have occurrenceMember := recordOccurrence_mem_trace secondMember
    have localOccurrence := atomicOccurrence_mem_threadTrace
      occurrenceMember secondThread
    exact List.mem_map.mpr ⟨second.occurrence, localOccurrence,
      recordOccurrence_id_eq_validation secondMember⟩
  have localNodup :
      (atomicIds (threadTrace trace thread)).Nodup :=
    (atomicIds_threadTrace_sublist trace thread).nodup
      wellFormed.atomicIdsNodup
  have localValidationBefore :
      MultiLocationRC11.IdBefore first.validation second.validation
        (atomicIds (threadTrace trace thread)) :=
    idBefore_of_sublist
      (atomicIds_threadTrace_sublist trace thread)
      wellFormed.atomicIdsNodup
      firstValidationMember secondValidationMember validationBefore
  have pointsDifferent : first.point ≠ second.point := by
    exact
      (recordPointsNodup_of_sourceWellFormed wellFormed).forall_sublist
        (ordered.map Record.point)
  have firstPosition :
      first.point = first.validation ∨
        MultiLocationRC11.IdBefore first.point first.validation
          (atomicIds (threadTrace trace thread)) := by
    rcases recordPointClassification firstMember with direct | empty
    · exact Or.inl direct.symm
    · obtain ⟨emptyThread, operation, head, shape, _⟩ := empty
      have emptyThreadEq : emptyThread = thread := by
        rw [shape] at firstThread
        simpa [AtomicAction.thread] using firstThread
      subst emptyThread
      exact Or.inr
        (emptyPointAdjacent wellFormed firstMember shape).1
  have secondPosition :
      second.point = second.validation ∨
        MultiLocationRC11.IdAdjacent second.point second.validation
          (atomicIds (threadTrace trace thread)) := by
    rcases recordPointClassification secondMember with direct | empty
    · exact Or.inl direct.symm
    · obtain ⟨emptyThread, operation, head, shape, _⟩ := empty
      have emptyThreadEq : emptyThread = thread := by
        rw [shape] at secondThread
        simpa [AtomicAction.thread] using secondThread
      subst emptyThread
      exact Or.inr
        (emptyPointAdjacent wellFormed secondMember shape)
  have validationToSecondPoint :
      first.validation = second.point ∨
        MultiLocationRC11.IdBefore first.validation second.point
          (atomicIds (threadTrace trace thread)) := by
    rcases secondPosition with direct | adjacent
    · right
      simpa [direct] using localValidationBefore
    · by_cases same : first.validation = second.point
      · exact Or.inl same
      · rcases MultiLocationRC11.IdBefore.total localNodup
          firstValidationMember adjacent.1.first_mem same with
          forward | reverse
        · exact Or.inr forward
        · exact (adjacent.2 first.validation
            ⟨reverse, localValidationBefore⟩).elim
  have localPointBefore :
      MultiLocationRC11.IdBefore first.point second.point
        (atomicIds (threadTrace trace thread)) := by
    rcases firstPosition with firstDirect | firstEarlier
    · rcases validationToSecondPoint with same | later
      · exact (pointsDifferent (firstDirect.trans same)).elim
      · simpa [firstDirect] using later
    · rcases validationToSecondPoint with same | later
      · simpa [same] using firstEarlier
      · exact firstEarlier.transitive later
  apply MultiLocationRC11.IdBefore.of_pair_sublist
    wellFormed.atomicIdsNodup
  exact
    (pair_sublist_of_idBefore localNodup localPointBefore).trans
      (atomicIds_threadTrace_sublist trace thread)

/-- Source order for two same-thread commits becomes schedule order through
the typed RC11 program-order edge between their exact anchor occurrences. -/
private theorem scheduledPointBefore_of_sourcePair
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {first second : Record Value}
    (ordered : [first, second].Sublist (structuralRecords trace))
    {thread : ThreadId}
    (firstThread : first.occurrence.action.thread = thread)
    (secondThread : second.occurrence.action.thread = thread) :
    MultiLocationRC11.IdBefore first.point second.point schedule.ids := by
  have firstMember : first ∈ structuralRecords trace :=
    ordered.subset (by simp)
  have secondMember : second ∈ structuralRecords trace :=
    ordered.subset (by simp)
  have sourceBefore := recordPointBefore execution.sourceWellFormed
    ordered firstThread secondThread
  have pointProgramOrder := execution.programOrder_of_atomicIdBefore
    (pointOccurrence_mem_of_structuralRecord
      execution.sourceWellFormed firstMember)
    (pointOccurrence_mem_of_structuralRecord
      execution.sourceWellFormed secondMember)
    (by rw [pointOccurrence_thread, pointOccurrence_thread,
      firstThread, secondThread])
    (by simpa only [Record.pointOccurrence_id] using sourceBefore)
  simpa [AtomSchedule.ids, Record.pointAtom,
    AtomicOccurrence.toRC11Atom] using
      schedule.respectsProgramOrder pointProgramOrder

/-- Retain a commit together with its structural anchor while selecting one
client thread.  Keeping the record here makes anchor uniqueness available to
the schedule-equivalence proof. -/
private def pointedCommitForThread?
    (thread : ThreadId)
    (record : Record Value) :
    Option (Record Value × AtomicOccurrence.CommitRecord Value) :=
  match record.commitRecord? with
  | none => none
  | some commit =>
      if commit.thread = thread then some (record, commit) else none

private theorem pointedCommitForThread?_facts
    {thread : ThreadId}
    {record : Record Value}
    {selected : Record Value × AtomicOccurrence.CommitRecord Value}
    (selection :
      pointedCommitForThread? thread record = some selected) :
    selected.1 = record ∧
      record.commitRecord? = some selected.2 ∧
      selected.2.thread = thread := by
  unfold pointedCommitForThread? at selection
  split at selection <;> rename_i commitShape
  · contradiction
  · split at selection <;> rename_i sameThread
    · injection selection with selectedShape
      subst selected
      exact ⟨rfl, commitShape, sameThread⟩
    · contradiction

/-- Filtering identified commits by thread is the same as retaining their
pointed source records first and then erasing the anchor metadata. -/
private theorem operationsForThread_commitRecords
    (thread : ThreadId)
    (records : List (Record Value)) :
    MSQueue.HW.operationsForThread thread
        ((records.filterMap Record.commitRecord?).map
          Source.identifiedCommit) =
      (records.filterMap (pointedCommitForThread? thread)).map
        (fun selected => Source.identifiedCommit selected.2) := by
  induction records with
  | nil => rfl
  | cons record records inductionHypothesis =>
      cases commitShape : record.commitRecord? with
      | none =>
          simp [pointedCommitForThread?, commitShape,
            inductionHypothesis]
      | some commit =>
          by_cases sameThread : commit.thread = thread
          · simp [pointedCommitForThread?, commitShape, sameThread,
              MSQueue.HW.operationsForThread,
              inductionHypothesis]
          · simp [pointedCommitForThread?, commitShape, sameThread,
              MSQueue.HW.operationsForThread,
              inductionHypothesis]

/-- The source and atom-scheduled pointed commits have exactly the same
per-thread order. -/
private theorem pointedCommitsForThread_eq
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (thread : ThreadId) :
    (structuralRecords trace).filterMap
        (pointedCommitForThread? thread) =
      (recordsOn trace schedule.atoms).filterMap
        (pointedCommitForThread? thread) := by
  let select := pointedCommitForThread? (Value := Value) thread
  let position := fun
      (selected : Record Value ×
        AtomicOccurrence.CommitRecord Value) =>
      schedule.ids.idxOf selected.1.point
  have selectedPermutation :
      ((structuralRecords trace).filterMap select).Perm
        ((recordsOn trace schedule.atoms).filterMap select) :=
    (schedule.recordsOn_perm.filterMap select).symm
  have sourceSorted :
      ((structuralRecords trace).filterMap select).Pairwise
        (fun first second => position first ≤ position second) := by
    rw [List.pairwise_filterMap]
    apply List.pairwise_of_forall_sublist
    intro firstRecord secondRecord ordered
      firstSelected firstSelection secondSelected secondSelection
    have firstFacts := pointedCommitForThread?_facts firstSelection
    have secondFacts := pointedCommitForThread?_facts secondSelection
    have firstThread :
        firstRecord.occurrence.action.thread = thread := by
      exact (commitRecord_thread firstFacts.2.1).symm.trans
        firstFacts.2.2
    have secondThread :
        secondRecord.occurrence.action.thread = thread := by
      exact (commitRecord_thread secondFacts.2.1).symm.trans
        secondFacts.2.2
    have before := scheduledPointBefore_of_sourcePair schedule ordered
      firstThread secondThread
    change schedule.ids.idxOf firstSelected.1.point ≤
      schedule.ids.idxOf secondSelected.1.point
    rw [firstFacts.1, secondFacts.1]
    exact Nat.le_of_lt before.2.2
  have scheduleSorted :
      ((recordsOn trace schedule.atoms).filterMap select).Pairwise
        (fun first second => position first ≤ position second) := by
    rw [List.pairwise_filterMap]
    apply List.pairwise_of_forall_sublist
    intro firstRecord secondRecord ordered
      firstSelected firstSelection secondSelected secondSelection
    have firstFacts := pointedCommitForThread?_facts firstSelection
    have secondFacts := pointedCommitForThread?_facts secondSelection
    have before := schedule.idBefore_of_recordsOn_pair_sublist ordered
    change schedule.ids.idxOf firstSelected.1.point ≤
      schedule.ids.idxOf secondSelected.1.point
    rw [firstFacts.1, secondFacts.1]
    exact Nat.le_of_lt before.2.2
  apply List.Perm.eq_of_pairwise
    (le := fun first second => position first ≤ position second)
  · intro first second firstMember secondMember
      firstBefore secondBefore
    rcases List.mem_filterMap.mp firstMember with
      ⟨firstRecord, firstRecordMember, firstSelection⟩
    rcases List.mem_filterMap.mp secondMember with
      ⟨secondRecord, secondRecordScheduled, secondSelection⟩
    have firstFacts := pointedCommitForThread?_facts firstSelection
    have secondFacts := pointedCommitForThread?_facts secondSelection
    have secondRecordMember :
        secondRecord ∈ structuralRecords trace :=
      mem_structuralRecords_of_mem_recordsOn secondRecordScheduled
    have firstPointMember : firstRecord.point ∈ schedule.ids :=
      schedule.structuralPoint_mem firstRecordMember
    have secondPointMember : secondRecord.point ∈ schedule.ids :=
      point_mem_of_mem_recordsOn secondRecordScheduled
    have positionEq :
        schedule.ids.idxOf firstRecord.point =
          schedule.ids.idxOf secondRecord.point := by
      apply Nat.le_antisymm
      · simpa [position, firstFacts.1, secondFacts.1] using firstBefore
      · simpa [position, firstFacts.1, secondFacts.1] using secondBefore
    have pointEq : firstRecord.point = secondRecord.point := by
      apply Classical.byContradiction
      intro different
      rcases MultiLocationRC11.IdBefore.total schedule.idsNodup
          firstPointMember secondPointMember different with
          forward | reverse
      · exact (Nat.ne_of_lt forward.2.2) positionEq
      · exact (Nat.ne_of_lt reverse.2.2) positionEq.symm
    have recordEq : firstRecord = secondRecord :=
      structuralRecord_eq_of_point_eq execution.sourceWellFormed
        firstRecordMember secondRecordMember pointEq
    apply Prod.ext
    · exact firstFacts.1.trans (recordEq.trans secondFacts.1.symm)
    · apply Option.some.inj
      calc
        some first.2 = firstRecord.commitRecord? := firstFacts.2.1.symm
        _ = secondRecord.commitRecord? := by rw [recordEq]
        _ = some second.2 := secondFacts.2.1
  · simpa [select, position] using sourceSorted
  · simpa [select, position] using scheduleSorted
  · simpa [select] using selectedPermutation

/-- Every RC11-respecting atom schedule preserves each client's source
commit order, including the retroactive point of an empty dequeue. -/
theorem AtomSchedule.scheduleEquivalent
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) :
    MSQueue.HW.Equivalent
      (Source.sourceCompletedOperations trace)
      schedule.scheduledOperations := by
  refine ⟨schedule.scheduledOperations_perm_source.symm, ?_⟩
  intro thread
  rw [Source.sourceCompletedOperations,
    ← structuralCommitRecords,
    operationsForThread_commitRecords]
  unfold AtomSchedule.scheduledOperations
  rw [operationsForThread_commitRecords,
    pointedCommitsForThread_eq schedule thread]

end WeakMemory.MSQueue.Source.Structural
