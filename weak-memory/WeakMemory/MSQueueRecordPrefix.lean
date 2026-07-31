import WeakMemory.MSQueueRecordScheduling

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Structural-record prefixes of an atom schedule

`recordsOn` is a `flatMap` of point buckets.  These lemmas expose its finite
prefix behavior in the form needed by replay induction: membership is exactly
membership of the record point in the corresponding identifier prefix, and
strict record order is exactly strict point order in that prefix.
-/

/-- A record occurs in a collection of point buckets exactly when it is a
structural record and one bucket carries its point. -/
theorem mem_recordsOn_iff
    {trace : List (TraceEvent Value)}
    {atoms : List (MultiLocationRC11.Atom Site Ptr)}
    {record : Record Value} :
    record ∈ recordsOn trace atoms ↔
      record ∈ structuralRecords trace ∧
        record.point ∈ atoms.map MultiLocationRC11.Atom.id := by
  constructor
  · intro member
    exact ⟨mem_structuralRecords_of_mem_recordsOn member,
      point_mem_of_mem_recordsOn member⟩
  · rintro ⟨recordMember, pointMember⟩
    rcases List.mem_map.mp pointMember with
      ⟨atom, atomMember, samePoint⟩
    rw [recordsOn, List.mem_flatMap]
    refine ⟨atom, atomMember, List.mem_filter.mpr
      ⟨recordMember, ?_⟩⟩
    simp [samePoint]

namespace AtomSchedule

/-- Prefix-bucket membership is exactly membership of the record point in
the corresponding prefix of scheduled identifiers. -/
theorem mem_recordsOn_take_iff
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (prefixLength : Nat)
    {record : Record Value} :
    record ∈ recordsOn trace (schedule.atoms.take prefixLength) ↔
      record ∈ structuralRecords trace ∧
        record.point ∈ schedule.ids.take prefixLength := by
  simpa [AtomSchedule.ids] using
    (mem_recordsOn_iff
      (trace := trace)
      (atoms := schedule.atoms.take prefixLength)
      (record := record))

/-- For a known structural record, entering a replay prefix is controlled
solely by whether its unique point has entered the identifier prefix. -/
theorem mem_recordsOn_take_iff_point_mem
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (prefixLength : Nat)
    {record : Record Value}
    (recordMember : record ∈ structuralRecords trace) :
    record ∈ recordsOn trace (schedule.atoms.take prefixLength) ↔
      record.point ∈ schedule.ids.take prefixLength := by
  rw [schedule.mem_recordsOn_take_iff]
  simp [recordMember]

end AtomSchedule

/-! ## Point-order preservation -/

/-- A duplicate-free list all of whose entries equal one point is a sublist
of that point's singleton list. -/
private theorem nodup_sublist_singleton_of_all_eq
    {items : List Point}
    {point : Point}
    (noDuplicates : items.Nodup)
    (allEqual : ∀ item ∈ items, item = point) :
    items.Sublist [point] := by
  cases items with
  | nil => simp
  | cons head tail =>
      have headShape : head = point := allEqual head (by simp)
      have nodupParts := List.nodup_cons.mp noDuplicates
      have tailEmpty : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro item itemMember
        have itemShape : item = point :=
          allEqual item (by simp [itemMember])
        subst head
        subst item
        exact nodupParts.1 itemMember
      subst head
      subst tail
      simp

/-- Mapping a unique-point record bucket to points yields at most the atom's
singleton identifier. -/
private theorem bucketPoints_sublist_singleton
    {trace : List (TraceEvent Value)}
    (recordPointsNodup :
      ((structuralRecords trace).map Record.point).Nodup)
    (atom : MultiLocationRC11.Atom Site Ptr) :
    (((structuralRecords trace).filter fun record =>
        record.point == atom.id).map Record.point).Sublist [atom.id] := by
  apply nodup_sublist_singleton_of_all_eq
  · exact
      ((List.filter_sublist
        (p := fun record : Record Value => record.point == atom.id)
        (l := structuralRecords trace)).map Record.point).nodup
        recordPointsNodup
  · intro point pointMember
    rcases List.mem_map.mp pointMember with
      ⟨record, recordMember, rfl⟩
    exact beq_iff_eq.mp (List.mem_filter.mp recordMember).2

/-- With unique structural points, the points emitted by `recordsOn` form a
sublist of the bucket identifiers.  This is the central order bridge. -/
theorem recordsOn_points_sublist
    {trace : List (TraceEvent Value)}
    (recordPointsNodup :
      ((structuralRecords trace).map Record.point).Nodup)
    (atoms : List (MultiLocationRC11.Atom Site Ptr)) :
    ((recordsOn trace atoms).map Record.point).Sublist
      (atoms.map MultiLocationRC11.Atom.id) := by
  induction atoms with
  | nil => simp [recordsOn]
  | cons atom rest inductionHypothesis =>
      simpa [recordsOn] using
        (bucketPoints_sublist_singleton recordPointsNodup atom).append
          inductionHypothesis

namespace AtomSchedule

/-- Every prefix record-point list embeds, in order, into the corresponding
prefix of scheduled identifiers. -/
theorem recordsOn_take_points_sublist
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (prefixLength : Nat) :
    ((recordsOn trace (schedule.atoms.take prefixLength)).map
        Record.point).Sublist
      (schedule.ids.take prefixLength) := by
  simpa [AtomSchedule.ids] using
    recordsOn_points_sublist
      (recordPointsNodup_of_sourceWellFormed
        execution.sourceWellFormed)
      (schedule.atoms.take prefixLength)

/-- Ordered records inside a replay prefix induce strict identifier order in
that same schedule prefix. -/
theorem idBefore_of_recordsOn_take_pair_sublist
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (prefixLength : Nat)
    {first second : Record Value}
    (ordered :
      [first, second].Sublist
        (recordsOn trace (schedule.atoms.take prefixLength))) :
    MultiLocationRC11.IdBefore first.point second.point
      (schedule.ids.take prefixLength) := by
  have mapped := ordered.map Record.point
  have pointPair :
      [first.point, second.point].Sublist
        (schedule.ids.take prefixLength) := by
    exact mapped.trans
      (schedule.recordsOn_take_points_sublist prefixLength)
  exact MultiLocationRC11.IdBefore.of_pair_sublist
    schedule.idsNodup.take pointPair

/-- Full scheduled record order induces strict order of the two anchor IDs. -/
theorem idBefore_of_recordsOn_pair_sublist
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {first second : Record Value}
    (ordered :
      [first, second].Sublist (recordsOn trace schedule.atoms)) :
    MultiLocationRC11.IdBefore first.point second.point schedule.ids := by
  have mapped := ordered.map Record.point
  have pointPair :
      [first.point, second.point].Sublist schedule.ids := by
    exact mapped.trans (by
      simpa [AtomSchedule.ids] using
        recordsOn_points_sublist
          (recordPointsNodup_of_sourceWellFormed
            execution.sourceWellFormed)
          schedule.atoms)
  exact MultiLocationRC11.IdBefore.of_pair_sublist
    schedule.idsNodup pointPair

end AtomSchedule

/-! ## Exact order equivalence -/

/-- Two distinct members of a list occur in one of the two strict orders. -/
private theorem pair_sublist_total
    {first second : Item}
    {items : List Item}
    (firstMember : first ∈ items)
    (secondMember : second ∈ items)
    (different : first ≠ second) :
    [first, second].Sublist items ∨
      [second, first].Sublist items := by
  induction items with
  | nil => simp at firstMember
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with firstIsHead | firstInTail
      · subst head
        rcases secondMember with secondIsFirst | secondInTail
        · exact (different secondIsFirst.symm).elim
        · left
          exact List.Sublist.cons_cons first
            (List.singleton_sublist.mpr secondInTail)
      · rcases secondMember with secondIsHead | secondInTail
        · subst head
          right
          exact List.Sublist.cons_cons second
            (List.singleton_sublist.mpr firstInTail)
        · rcases inductionHypothesis firstInTail secondInTail with
              forward | backward
          · exact Or.inl (forward.cons head)
          · exact Or.inr (backward.cons head)

namespace AtomSchedule

/-- For known structural records, strict list order in any replay prefix is
equivalent to strict order of their unique anchor IDs in the schedule prefix. -/
theorem recordsOn_take_pair_sublist_iff_idBefore
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (prefixLength : Nat)
    {first second : Record Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace) :
    [first, second].Sublist
        (recordsOn trace (schedule.atoms.take prefixLength)) ↔
      MultiLocationRC11.IdBefore first.point second.point
        (schedule.ids.take prefixLength) := by
  constructor
  · exact schedule.idBefore_of_recordsOn_take_pair_sublist prefixLength
  · intro pointBefore
    have firstInPrefix :
        first ∈ recordsOn trace
          (schedule.atoms.take prefixLength) :=
      (schedule.mem_recordsOn_take_iff_point_mem
        prefixLength firstMember).2 pointBefore.first_mem
    have secondInPrefix :
        second ∈ recordsOn trace
          (schedule.atoms.take prefixLength) :=
      (schedule.mem_recordsOn_take_iff_point_mem
        prefixLength secondMember).2 pointBefore.second_mem
    have different : first ≠ second := by
      intro sameRecord
      subst second
      exact MultiLocationRC11.IdBefore.irreflexive pointBefore
    rcases pair_sublist_total firstInPrefix secondInPrefix different with
        forward | backward
    · exact forward
    · have reverseBefore :=
        schedule.idBefore_of_recordsOn_take_pair_sublist
          prefixLength backward
      exact (Nat.lt_asymm pointBefore.2.2 reverseBefore.2.2).elim

/-- The full scheduled record list has exactly the strict order of its anchor
identifiers. -/
theorem recordsOn_pair_sublist_iff_idBefore
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {first second : Record Value}
    (firstMember : first ∈ structuralRecords trace)
    (secondMember : second ∈ structuralRecords trace) :
    [first, second].Sublist (recordsOn trace schedule.atoms) ↔
      MultiLocationRC11.IdBefore first.point second.point schedule.ids := by
  constructor
  · exact schedule.idBefore_of_recordsOn_pair_sublist
  · intro pointBefore
    have firstInRecords :
        first ∈ recordsOn trace schedule.atoms :=
      schedule.recordsOn_perm.mem_iff.mpr firstMember
    have secondInRecords :
        second ∈ recordsOn trace schedule.atoms :=
      schedule.recordsOn_perm.mem_iff.mpr secondMember
    have different : first ≠ second := by
      intro sameRecord
      subst second
      exact MultiLocationRC11.IdBefore.irreflexive pointBefore
    rcases pair_sublist_total firstInRecords secondInRecords different with
        forward | backward
    · exact forward
    · have reverseBefore :=
        schedule.idBefore_of_recordsOn_pair_sublist backward
      exact (Nat.lt_asymm pointBefore.2.2 reverseBefore.2.2).elim

/-! ## Prefix focused at one structural record -/

/-- The scheduled records strictly before `focus`.  The atom prefix stops at
the index of the focus point and therefore excludes the focus bucket itself. -/
def recordsBefore
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (focus : Record Value) : List (Record Value) :=
  recordsOn trace
    (schedule.atoms.take (schedule.ids.idxOf focus.point))

/-- In a duplicate-free identifier list, membership before the first
occurrence of `focus` is exactly strict `IdBefore` order. -/
private theorem mem_take_idxOf_iff_idBefore
    {item focus : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (focusMember : focus ∈ order) :
    item ∈ order.take (order.idxOf focus) ↔
      MultiLocationRC11.IdBefore item focus order := by
  induction order with
  | nil => simp at focusMember
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp noDuplicates
      simp only [List.mem_cons] at focusMember
      rcases focusMember with focusIsHead | focusInTail
      · subst focus
        simp [MultiLocationRC11.IdBefore]
      · have headNeFocus : head ≠ focus := by
          intro same
          subst focus
          exact nodupParts.1 focusInTail
        have tailEquivalence :=
          inductionHypothesis nodupParts.2 focusInTail
        have headFocusFalse : (head == focus) = false :=
          beq_eq_false_iff_ne.mpr headNeFocus
        by_cases itemIsHead : item = head
        · subst item
          simp [List.idxOf_cons, headFocusFalse,
            MultiLocationRC11.IdBefore, focusInTail]
        · have headItemFalse : (head == item) = false :=
            beq_eq_false_iff_ne.mpr (Ne.symm itemIsHead)
          simp [List.idxOf_cons, headFocusFalse, headItemFalse,
            itemIsHead,
            MultiLocationRC11.IdBefore, focusInTail,
            tailEquivalence]

/-- A structural record belongs to the focus prefix exactly when its point is
strictly before the focus point in the atom schedule. -/
theorem mem_recordsBefore_iff
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus record : Record Value}
    (focusMember : focus ∈ structuralRecords trace)
    (recordMember : record ∈ structuralRecords trace) :
    record ∈ schedule.recordsBefore focus ↔
      MultiLocationRC11.IdBefore
        record.point focus.point schedule.ids := by
  rw [recordsBefore,
    schedule.mem_recordsOn_take_iff_point_mem _ recordMember]
  exact mem_take_idxOf_iff_idBefore schedule.idsNodup
    (schedule.structuralPoint_mem focusMember)

/-- A duplicate-free list containing `focus`, all of whose elements equal
`focus`, is exactly its singleton. -/
private theorem eq_singleton_of_nodup_of_all_eq
    {items : List Item}
    {focus : Item}
    (noDuplicates : items.Nodup)
    (focusMember : focus ∈ items)
    (allEqual : ∀ item ∈ items, item = focus) :
    items = [focus] := by
  cases items with
  | nil => simp at focusMember
  | cons head tail =>
      have headShape : head = focus := allEqual head (by simp)
      have nodupParts := List.nodup_cons.mp noDuplicates
      have tailEmpty : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro item itemMember
        have itemShape : item = focus :=
          allEqual item (by simp [itemMember])
        apply nodupParts.1
        simpa [headShape, itemShape] using itemMember
      rw [headShape, tailEmpty]

/-- The atom selected by the index of a represented point carries exactly
that identifier. -/
private theorem atomId_at_point_idxOf
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {point : EventId}
    (pointMember : point ∈ schedule.ids) :
    (schedule.atoms[schedule.ids.idxOf point]'(by
      simpa [AtomSchedule.ids] using
        (List.idxOf_lt_length_of_mem pointMember))).id = point := by
  have selected :
      schedule.ids[schedule.ids.idxOf point]'(by
        exact List.idxOf_lt_length_of_mem pointMember) = point := by
    apply beq_iff_eq.mp
    exact List.findIdx_getElem
      (p := fun candidate : EventId => candidate == point)
  simpa [AtomSchedule.ids] using selected

/-- The structural bucket at the focus point is the focus singleton. -/
private theorem focusBucket_eq_singleton
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace) :
    (structuralRecords trace).filter (fun record =>
      record.point ==
        (schedule.atoms[schedule.ids.idxOf focus.point]'(by
          have pointMember := schedule.structuralPoint_mem focusMember
          simpa [AtomSchedule.ids] using
            (List.idxOf_lt_length_of_mem pointMember))).id) = [focus] := by
  let selectedAtom :=
    schedule.atoms[schedule.ids.idxOf focus.point]'(by
      have pointMember := schedule.structuralPoint_mem focusMember
      simpa [AtomSchedule.ids] using
        (List.idxOf_lt_length_of_mem pointMember))
  have pointMember := schedule.structuralPoint_mem focusMember
  have selectedId : selectedAtom.id = focus.point := by
    simpa [selectedAtom] using
      atomId_at_point_idxOf schedule pointMember
  let bucket := (structuralRecords trace).filter fun record =>
    record.point == selectedAtom.id
  have structuralNodup : (structuralRecords trace).Nodup := by
    exact List.Pairwise.of_map Record.point
      (fun left right different sameRecord =>
        different (congrArg Record.point sameRecord))
      (recordPointsNodup_of_sourceWellFormed
        execution.sourceWellFormed)
  have bucketNodup : bucket.Nodup :=
    (List.filter_sublist
      (p := fun record : Record Value =>
        record.point == selectedAtom.id)
      (l := structuralRecords trace)).nodup structuralNodup
  have focusInBucket : focus ∈ bucket := by
    apply List.mem_filter.mpr
    exact ⟨focusMember, by simp [selectedId]⟩
  have bucketAll : ∀ record ∈ bucket, record = focus := by
    intro record recordInBucket
    have filtered := List.mem_filter.mp recordInBucket
    have samePoint : record.point = focus.point :=
      (beq_iff_eq.mp filtered.2).trans selectedId
    exact structuralRecord_eq_of_point_eq
      execution.sourceWellFormed filtered.1 focusMember samePoint
  exact eq_singleton_of_nodup_of_all_eq
    bucketNodup focusInBucket bucketAll

/-- The scheduled prefix through `focus` is the strict focus prefix followed
by exactly the focus record.  The take length is explicitly
`idxOf focus.point + 1`, matching one replay-induction step. -/
theorem recordsBefore_current
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {focus : Record Value}
    (focusMember : focus ∈ structuralRecords trace) :
    recordsOn trace
        (schedule.atoms.take (schedule.ids.idxOf focus.point + 1)) =
      schedule.recordsBefore focus ++ [focus] := by
  have pointMember := schedule.structuralPoint_mem focusMember
  have atomBound :
      schedule.ids.idxOf focus.point < schedule.atoms.length := by
    simpa [AtomSchedule.ids] using
      (List.idxOf_lt_length_of_mem pointMember)
  rw [List.take_succ_eq_append_getElem atomBound]
  change
    recordsOn trace
        (schedule.atoms.take (schedule.ids.idxOf focus.point) ++
          [schedule.atoms[schedule.ids.idxOf focus.point]]) =
      schedule.recordsBefore focus ++ [focus]
  simp only [recordsOn, List.flatMap_append, List.flatMap_singleton]
  rw [focusBucket_eq_singleton schedule focusMember]
  rfl

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
