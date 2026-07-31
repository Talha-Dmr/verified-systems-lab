import WeakMemory.MSQueueSourcePrefixReadiness

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Generic atom-prefix replay induction

An atom schedule emits at most one structural record per atom because source
well-formedness makes record points unique.  Consequently, a local readiness
proof for each record over its exact `recordsBefore` prefix is sufficient to
construct the complete canonical replay.
-/

private theorem idxOf_eq_of_getElem?_eq_some
    {order : List EventId}
    (noDuplicates : order.Nodup)
    {index item : EventId}
    (itemAt : order[index]? = some item) :
    order.idxOf item = index := by
  induction order generalizing index with
  | nil => simp at itemAt
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp noDuplicates
      cases index with
      | zero =>
          simp at itemAt
          subst item
          simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at itemAt
          have headNeItem : head ≠ item := by
            intro same
            subst item
            apply nodupParts.1
            exact List.mem_iff_getElem.mpr
              ⟨index,
                (List.getElem?_eq_some_iff.mp itemAt).1,
                (List.getElem?_eq_some_iff.mp itemAt).2⟩
          rw [List.idxOf_cons]
          simp only [cond_eq_ite, beq_iff_eq, if_neg headNeItem]
          exact congrArg (· + 1)
            (inductionHypothesis nodupParts.2 itemAt)

private theorem recordBucket_nil_or_singleton
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    (atom : MultiLocationRC11.Atom Site Ptr) :
    ((structuralRecords trace).filter fun record =>
        record.point == atom.id) = [] ∨
      ∃ focus,
        ((structuralRecords trace).filter fun record =>
            record.point == atom.id) = [focus] ∧
          focus ∈ structuralRecords trace ∧ focus.point = atom.id := by
  let bucket := (structuralRecords trace).filter fun record =>
    record.point == atom.id
  have bucketPointsNodup :
      (bucket.map Record.point).Nodup :=
    ((List.filter_sublist
      (p := fun record : Record Value => record.point == atom.id)
      (l := structuralRecords trace)).map Record.point).nodup
        (recordPointsNodup_of_sourceWellFormed wellFormed)
  cases bucketShape : bucket with
  | nil =>
      exact Or.inl (by simpa [bucket] using bucketShape)
  | cons focus rest =>
      have focusBucket : focus ∈ bucket := by
        rw [bucketShape]
        simp
      have focusParts := List.mem_filter.mp focusBucket
      have focusPoint : focus.point = atom.id :=
        beq_iff_eq.mp focusParts.2
      have restEmpty : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro later laterMember
        have laterBucket : later ∈ bucket := by
          rw [bucketShape]
          simp [laterMember]
        have laterPoint : later.point = atom.id :=
          beq_iff_eq.mp (List.mem_filter.mp laterBucket).2
        have nodupParts :
            (focus.point :: rest.map Record.point).Nodup := by
          simpa [bucketShape] using bucketPointsNodup
        apply (List.nodup_cons.mp nodupParts).1
        apply List.mem_map.mpr
        exact ⟨later, laterMember, laterPoint.trans focusPoint.symm⟩
      right
      refine ⟨focus, ?_, focusParts.1, focusPoint⟩
      simp [bucket, bucketShape, restEmpty]

namespace Prefix

/-- The post-state named by `Applies` is the canonical snoc projection when
the pre-state is the canonical projection of the preceding records. -/
theorem applies_stateOf_snoc
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    {record : Record Value}
    {after : Chain.State Value}
    (applies : record.Applies (stateOf dummy records) after) :
    after = stateOf dummy (records ++ [record]) := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action with
  | link owner child payload =>
      rcases applies with ⟨_, _, _, afterShape⟩
      exact afterShape.trans
        (stateOf_snoc_link dummy records
          ⟨occurrence, point, validation, .link owner child payload⟩ rfl).symm
  | advanceTail expected desired =>
      rcases applies with ⟨_, _, _, afterShape⟩
      exact afterShape.trans
        (stateOf_snoc_advanceTail dummy records
          ⟨occurrence, point, validation, .advanceTail expected desired⟩ rfl).symm
  | advanceHead expected desired payload =>
      rcases applies with ⟨_, _, _, _, afterShape⟩
      exact afterShape.trans
        (stateOf_snoc_advanceHead dummy records
          ⟨occurrence, point, validation,
            .advanceHead expected desired payload⟩ rfl).symm
  | empty head =>
      rcases applies with ⟨_, _, afterShape⟩
      exact afterShape.trans
        (stateOf_snoc_empty dummy records
          ⟨occurrence, point, validation, .empty head⟩ rfl).symm

end Prefix

namespace Replay

/-- Split a replay at a distinguished record occurrence. -/
theorem split
    {Value : Type}
    {initial final : Chain.State Value}
    {leading trailing : List (Record Value)}
    {focus : Record Value}
    (replayed : Replay initial (leading ++ focus :: trailing) final) :
    ∃ before after,
      Replay initial leading before ∧
        focus.Applies before after ∧
        Replay after trailing final := by
  induction leading generalizing initial with
  | nil =>
      cases replayed with
      | cons applies later =>
          exact ⟨_, _, Replay.nil initial, applies, later⟩
  | cons record records inductionHypothesis =>
      cases replayed with
      | @cons _ middle _ _ _ first later =>
          obtain ⟨before, after, prefixReplay, applies, suffixReplay⟩ :=
            inductionHypothesis later
          exact ⟨before, after, Replay.cons first prefixReplay,
            applies, suffixReplay⟩

/-- A replay beginning in a canonical prefix state ends in the canonical
state obtained by appending all replayed records. -/
theorem final_eq_stateOf_append
    {Value : Type}
    {dummy : NodeId}
    (priorRecords : List (Record Value))
    {records : List (Record Value)}
    {final : Chain.State Value}
    (replayed : Replay (Prefix.stateOf dummy priorRecords) records final) :
    final = Prefix.stateOf dummy (priorRecords ++ records) := by
  induction records generalizing priorRecords final with
  | nil =>
      cases replayed
      simp
  | cons record records inductionHypothesis =>
      cases replayed with
      | @cons _ middle _ _ _ applies later =>
          have middleShape := Prefix.applies_stateOf_snoc applies
          subst middle
          have finalShape := inductionHypothesis
            (priorRecords ++ [record]) later
          simpa [List.append_assoc] using finalShape

/-- Replay evidence exposes the exact canonical `Applies` fact at every
record position. -/
theorem applies_at
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    {focus : Record Value}
    {leading trailing : List (Record Value)}
    (recordsShape : records = leading ++ focus :: trailing)
    (replayed : Replay (Chain.State.initial dummy) records
      (Prefix.stateOf dummy records)) :
    focus.Applies
      (Prefix.stateOf dummy leading)
      (Prefix.stateOf dummy (leading ++ [focus])) := by
  subst records
  obtain ⟨before, after, prefixReplay, applies, _suffixReplay⟩ :=
    replayed.split
  have beforeShape : before = Prefix.stateOf dummy leading := by
    simpa using
      (final_eq_stateOf_append (dummy := dummy) [] prefixReplay)
  subst before
  have afterShape := Prefix.applies_stateOf_snoc applies
  subst after
  exact applies

/-- Every replayed successful Head move has the strict Head/Tail count gap
in its exact record prefix. -/
theorem advanceHead_prefixGap
    {Value : Type}
    {dummy : NodeId}
    {records : List (Record Value)}
    {focus : Record Value}
    {leading trailing : List (Record Value)}
    {expected desired : NodeId}
    {payload : Value}
    (recordsShape : records = leading ++ focus :: trailing)
    (replayed : Replay (Chain.State.initial dummy) records
      (Prefix.stateOf dummy records))
    (actionShape :
      focus.action = .advanceHead expected desired payload) :
    (Prefix.headMoves leading).length <
      (Prefix.tailMoves leading).length := by
  have applies := replayed.applies_at recordsShape
  rw [Record.Applies, actionShape] at applies
  simpa [Prefix.stateOf] using applies.2.2.1

end Replay

namespace AtomSchedule

/-- Local obligation consumed by the generic atom-prefix induction. -/
def RecordReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution) : Prop :=
  ∀ (focus : Record Value)
    (_focusMember : focus ∈ structuralRecords trace),
    Prefix.Rep dummy (schedule.recordsBefore focus) →
      Replay (Chain.State.initial dummy)
          (schedule.recordsBefore focus)
          (Prefix.stateOf dummy (schedule.recordsBefore focus)) →
      focus.Applies
          (Prefix.stateOf dummy (schedule.recordsBefore focus))
          (Prefix.stateOf dummy
            (schedule.recordsBefore focus ++ [focus])) ∧
        Prefix.Rep dummy
          (schedule.recordsBefore focus ++ [focus])

/-- Any per-record readiness theorem over exact schedule prefixes lifts to a
complete canonical structural replay. -/
theorem replay_of_ready
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (ready : RecordReady schedule) :
    Prefix.Rep dummy (recordsOn trace schedule.atoms) ∧
      Replay (Chain.State.initial dummy)
        (recordsOn trace schedule.atoms)
        (Prefix.stateOf dummy (recordsOn trace schedule.atoms)) := by
  have prefixResult :
      ∀ prefixLength,
        prefixLength ≤ schedule.atoms.length →
          Prefix.Rep dummy
              (recordsOn trace (schedule.atoms.take prefixLength)) ∧
            Replay (Chain.State.initial dummy)
              (recordsOn trace (schedule.atoms.take prefixLength))
              (Prefix.stateOf dummy
                (recordsOn trace (schedule.atoms.take prefixLength))) := by
    intro prefixLength bound
    induction prefixLength with
    | zero =>
        simp [recordsOn]
        exact ⟨Prefix.Rep.nil dummy,
          Replay.nil (Chain.State.initial dummy)⟩
    | succ priorLength inductionHypothesis =>
        have priorBound : priorLength < schedule.atoms.length := by
          omega
        obtain ⟨priorRep, priorReplay⟩ :=
          inductionHypothesis (Nat.le_of_lt priorBound)
        let atom := schedule.atoms[priorLength]
        have atomAt : schedule.atoms[priorLength]? = some atom :=
          List.getElem?_eq_some_iff.mpr ⟨priorBound, rfl⟩
        have takeShape :
            schedule.atoms.take (priorLength + 1) =
              schedule.atoms.take priorLength ++ [atom] := by
          rw [List.take_succ_eq_append_getElem priorBound]
        rcases recordBucket_nil_or_singleton
            execution.sourceWellFormed atom with
          bucketEmpty | ⟨focus, bucketSingleton,
            focusMember, focusPoint⟩
        · have recordsSame :
              recordsOn trace
                  (schedule.atoms.take (priorLength + 1)) =
                recordsOn trace (schedule.atoms.take priorLength) := by
            rw [takeShape]
            simp [recordsOn, bucketEmpty]
          rw [recordsSame]
          exact ⟨priorRep, priorReplay⟩
        · have idAt : schedule.ids[priorLength]? = some focus.point := by
            have mapped := congrArg
              (Option.map MultiLocationRC11.Atom.id) atomAt
            simpa [AtomSchedule.ids, atom, focusPoint] using mapped
          have focusIndex :
              schedule.ids.idxOf focus.point = priorLength :=
            idxOf_eq_of_getElem?_eq_some schedule.idsNodup idAt
          have priorIsRecordsBefore :
              recordsOn trace (schedule.atoms.take priorLength) =
                schedule.recordsBefore focus := by
            simp [AtomSchedule.recordsBefore, focusIndex]
          have currentShape :
              recordsOn trace
                  (schedule.atoms.take (priorLength + 1)) =
                schedule.recordsBefore focus ++ [focus] := by
            rw [takeShape]
            simp only [recordsOn, List.flatMap_append,
              List.flatMap_singleton]
            rw [bucketSingleton]
            change
              recordsOn trace (schedule.atoms.take priorLength) ++ [focus] =
                schedule.recordsBefore focus ++ [focus]
            rw [priorIsRecordsBefore]
          have priorRepExact :
              Prefix.Rep dummy (schedule.recordsBefore focus) := by
            rw [← priorIsRecordsBefore]
            exact priorRep
          have replayExact :
              Replay (Chain.State.initial dummy)
                (schedule.recordsBefore focus)
                (Prefix.stateOf dummy
                  (schedule.recordsBefore focus)) := by
            rw [← priorIsRecordsBefore]
            exact priorReplay
          obtain ⟨applies, currentRep⟩ :=
            ready focus focusMember priorRepExact replayExact
          rw [currentShape]
          refine ⟨currentRep, ?_⟩
          exact replayExact.snoc applies
  have full := prefixResult schedule.atoms.length (Nat.le_refl _)
  simpa using full

/-- Exact source certificate obtained without a separately supplied replay. -/
def certificateOfReady
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (ready : RecordReady schedule) : Certificate execution :=
  Certificate.ofReplay execution schedule
    (Prefix.stateOf dummy (recordsOn trace schedule.atoms))
    (schedule.replay_of_ready ready).2

/-- FIFO safety follows directly from local readiness for all four structural
record kinds. -/
theorem fifoLegal_of_ready
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (ready : RecordReady schedule) :
    QueueSpec.Legal []
      (completedHistory (schedule.certificateOfReady ready).commits)
      (schedule.certificateOfReady ready).finalState.contents :=
  (schedule.certificateOfReady ready).fifoLegal

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
