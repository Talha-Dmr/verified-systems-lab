import WeakMemory.TreiberRealTime

namespace WeakMemory.TreiberRC11

/-!
# Executable client real-time compatibility checking

The logical compatibility predicate quantifies over completed operations.
This module decides it by enumerating only the finite
`scheduledOperations` list.  It does not request a `Decidable` instance for
that quantified predicate or enumerate the (possibly infinite) element type.
-/

namespace ClientCompatibilityCheck

/--
Executable strict-order lookup in a finite list.

The recursive alternative is necessary when the first equal occurrence has
no later `second`, but another occurrence does.
-/
def before
    [DecidableEq β]
    (first second : β) :
    List β → Bool
  | [] =>
      false
  | item :: rest =>
      (decide (item = first) &&
          rest.any fun later => decide (later = second)) ||
        before first second rest

private theorem before_cons_iff
    {first second item : β}
    {rest : List β} :
    HerlihyWing.Before first second (item :: rest) ↔
      (item = first ∧ second ∈ rest) ∨
        HerlihyWing.Before first second rest := by
  constructor
  · rintro ⟨earlier, between, later, shape⟩
    cases earlier with
    | nil =>
        change
          item :: rest =
            first :: between ++ second :: later
          at shape
        have itemShape := (List.cons.inj shape).1
        have restShape := (List.cons.inj shape).2
        exact Or.inl ⟨itemShape, by
          rw [restShape]
          simp⟩
    | cons headItem remaining =>
        change
          item :: rest =
            headItem ::
              remaining ++ first :: between ++ second :: later
          at shape
        have restShape := (List.cons.inj shape).2
        exact Or.inr
          ⟨remaining, between, later, restShape⟩
  · rintro (⟨rfl, secondMember⟩ | beforeRest)
    · obtain ⟨between, later, restShape⟩ :=
        List.append_of_mem secondMember
      exact ⟨[], between, later, by
        simp [restShape]⟩
    · obtain ⟨earlier, between, later, restShape⟩ :=
        beforeRest
      exact ⟨item :: earlier, between, later, by
        simp [restShape]⟩

/-- The finite Boolean order lookup exactly implements `HerlihyWing.Before`. -/
theorem before_eq_true_iff
    [DecidableEq β]
    (first second : β)
    (items : List β) :
    before first second items = true ↔
      HerlihyWing.Before first second items := by
  induction items with
  | nil =>
      simp [before, HerlihyWing.Before]
  | cons item rest inductionHypothesis =>
      rw [before_cons_iff]
      simp [before, List.any_eq_true, inductionHypothesis]

/-- The false result is exactly the absence of strict list order. -/
theorem before_eq_false_iff
    [DecidableEq β]
    (first second : β)
    (items : List β) :
    before first second items = false ↔
      ¬HerlihyWing.Before first second items := by
  constructor
  · intro checkedFalse ordered
    have checkedTrue :=
      (before_eq_true_iff first second items).mpr ordered
    rw [checkedFalse] at checkedTrue
    contradiction
  · intro notOrdered
    cases checked : before first second items with
    | false =>
        rfl
    | true =>
        exact False.elim
          (notOrdered
            ((before_eq_true_iff first second items).mp
              checked))

/-- Check one possible cross-thread real-time edge. -/
def pairCompatible
    [DecidableEq α]
    (history : HerlihyWing.History α)
    (operations :
      List (HerlihyWing.IdentifiedCompleted α))
    (first second : HerlihyWing.IdentifiedCompleted α) :
    Bool :=
  decide (first.thread = second.thread) ||
    !before
      (HerlihyWing.HistoryEvent.respond first.returned)
      (HerlihyWing.HistoryEvent.invoke second.invocation)
      history ||
    before first second operations

/-- One pair passes exactly when every required implication for it holds. -/
theorem pairCompatible_eq_true_iff
    [DecidableEq α]
    (history : HerlihyWing.History α)
    (operations :
      List (HerlihyWing.IdentifiedCompleted α))
    (first second : HerlihyWing.IdentifiedCompleted α) :
    pairCompatible history operations first second = true ↔
      (first.thread ≠ second.thread →
        HerlihyWing.RealTimePrecedes history first second →
        HerlihyWing.Before first second operations) := by
  rw [show
    HerlihyWing.RealTimePrecedes history first second =
      HerlihyWing.Before
        (HerlihyWing.HistoryEvent.respond first.returned)
        (HerlihyWing.HistoryEvent.invoke second.invocation)
        history by rfl]
  simp only [pairCompatible, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true',
    before_eq_true_iff, before_eq_false_iff]
  constructor
  · rintro ((sameThread | notRealTime) | ordered)
      differentThread realTime
    · exact False.elim (differentThread sameThread)
    · exact False.elim (notRealTime realTime)
    · exact ordered
  · intro compatible
    by_cases sameThread : first.thread = second.thread
    · exact Or.inl (Or.inl sameThread)
    · by_cases realTime :
          HerlihyWing.Before
            (HerlihyWing.HistoryEvent.respond first.returned)
            (HerlihyWing.HistoryEvent.invoke second.invocation)
            history
      · exact Or.inr
          (compatible sameThread realTime)
      · exact Or.inl (Or.inr realTime)

/--
Finite executable checker for the external cross-thread client-order
obligation.
-/
def crossThreadRealTimeCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) :
    Bool :=
  let history :=
    sourceHistory execution.source.skeleton
  let operations :=
    scheduledOperations execution schedule
  operations.all fun first =>
    operations.all fun second =>
      pairCompatible history operations first second

/-- The Boolean checker is sound and complete for the logical predicate. -/
theorem crossThreadRealTimeCompatible_eq_true_iff
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) :
    crossThreadRealTimeCompatible execution schedule = true ↔
      CrossThreadRealTimeCompatible execution schedule := by
  simp only [crossThreadRealTimeCompatible,
    List.all_eq_true, pairCompatible_eq_true_iff]
  constructor
  · intro checked first second firstMember secondMember
      differentThread realTime
    exact checked first firstMember second secondMember
      differentThread realTime
  · intro compatible first firstMember second secondMember
      differentThread realTime
    exact compatible firstMember secondMember
      differentThread realTime

/-- Soundness projection convenient for checked execution pipelines. -/
theorem crossThreadRealTimeCompatible_sound
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    {schedule : List (Event α)}
    (checked :
      crossThreadRealTimeCompatible execution schedule = true) :
    CrossThreadRealTimeCompatible execution schedule :=
  (crossThreadRealTimeCompatible_eq_true_iff
    execution schedule).mp checked

/--
An executable `Decidable` value obtained from the finite checker, without
asking Lean to decide the original universally quantified proposition.
-/
def decideCrossThreadRealTimeCompatible
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (schedule : List (Event α)) :
    Decidable
      (CrossThreadRealTimeCompatible execution schedule) :=
  if checked :
      crossThreadRealTimeCompatible execution schedule = true
  then
    isTrue
      ((crossThreadRealTimeCompatible_eq_true_iff
        execution schedule).mp checked)
  else
    isFalse fun compatible =>
      checked
        ((crossThreadRealTimeCompatible_eq_true_iff
          execution schedule).mpr compatible)

end ClientCompatibilityCheck

end WeakMemory.TreiberRC11
