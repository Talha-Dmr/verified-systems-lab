import WeakMemory.TreiberControlFlow

namespace WeakMemory.TreiberRC11.ControlFlow

/-!
# Executable checking of local Treiber traces

`LocalStep` is the proof-facing source-control relation.  This module gives
the same relation an executable presentation.  The checker consumes the
entire source label, including observed values and weak-CAS outcomes, and
returns the unique next local state exactly when a `LocalStep` exists.
-/

/--
Proof-carrying implementation of one fully observed local source step.

The proof component is erased by compilation; retaining it here makes the
soundness boundary definitionally auditable.
-/
private def checkedStep?
    [DecidableEq α]
    (thread : Nat)
    (before : LocalState α)
    (label : Label α) :
    Option {after : LocalState α //
      LocalStep thread before label after} :=
  match before, label with
  | .idle, .invokePush operation reserved value =>
      some ⟨.pushLoading operation reserved value,
        .beginPush operation reserved value⟩
  | .idle, .invokePop operation =>
      some ⟨.popLoading operation, .beginPop operation⟩
  | .idle, .invokeIsEmpty operation =>
      some ⟨.checkingEmpty operation,
        .beginIsEmpty operation⟩
  | .pushLoading operation reserved value,
      .atomic labelOperation (.pushLoad actionThread observed) =>
      if h :
          labelOperation = operation ∧
            actionThread = thread then
        some ⟨.pushWriting operation reserved value observed, by
          rcases h with ⟨rfl, rfl⟩
          exact .pushLoad _ _ _ _⟩
      else
        none
  | .pushWriting operation reserved value expected,
      .writeNext labelOperation labelNode labelNext =>
      if h :
          labelOperation = operation ∧
          labelNode = reserved ∧
          labelNext = expected then
        some ⟨.pushing operation reserved value expected, by
          rcases h with ⟨rfl, rfl, rfl⟩
          exact .writeNext _ _ _ _⟩
      else
        none
  | .pushing operation reserved value expected,
      .atomic labelOperation
        (.pushFailure actionThread actionNode actionValue
          actionExpected actual) =>
      if h :
          labelOperation = operation ∧
          actionThread = thread ∧
          actionNode = reserved ∧
          actionValue = value ∧
          actionExpected = expected then
        some ⟨.pushWriting operation reserved value actual, by
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          exact .pushFailure _ _ _ _ _⟩
      else
        none
  | .pushing operation reserved value expected,
      .atomic labelOperation
        (.pushSuccess actionThread actionNode actionValue
          actionExpected) =>
      if h :
          labelOperation = operation ∧
          actionThread = thread ∧
          actionNode = reserved ∧
          actionValue = value ∧
          actionExpected = expected then
        some ⟨.returning operation (.push value), by
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          exact .pushSuccess _ _ _ _⟩
      else
        none
  | .popLoading operation,
      .atomic labelOperation (.popLoad actionThread observed) =>
      if h :
          labelOperation = operation ∧
            actionThread = thread then
        match observed with
        | none =>
            some ⟨.returning operation .popEmpty, by
              rcases h with ⟨rfl, rfl⟩
              exact .popLoadEmpty _⟩
        | some node =>
            some ⟨.popReading operation node, by
              rcases h with ⟨rfl, rfl⟩
              exact .popLoadNonempty _ _⟩
      else
        none
  | .popReading operation observed,
      .readNext labelOperation labelNode next =>
      if h :
          labelOperation = operation ∧
            labelNode = observed then
        some ⟨.popping operation observed next, by
          rcases h with ⟨rfl, rfl⟩
          exact .readNext _ _ _⟩
      else
        none
  | .popping operation expected next,
      .atomic labelOperation
        (.popFailure actionThread actionExpected actual) =>
      if h :
          labelOperation = operation ∧
          actionThread = thread ∧
          actionExpected = some expected then
        match actual with
        | none =>
            some ⟨.returning operation .popEmpty, by
              rcases h with ⟨rfl, rfl, rfl⟩
              exact .popFailureEmpty _ _ _⟩
        | some node =>
            some ⟨.popReading operation node, by
              rcases h with ⟨rfl, rfl, rfl⟩
              exact .popFailureRetry _ _ _ _⟩
      else
        none
  | .popping operation expected next,
      .atomic labelOperation
        (.popSuccess actionThread actionNode value actionNext) =>
      if h :
          labelOperation = operation ∧
          actionThread = thread ∧
          actionNode = expected ∧
          actionNext = next then
        some ⟨.returning operation (.popValue value), by
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          exact .popSuccess _ _ _ _⟩
      else
        none
  | .checkingEmpty operation,
      .atomic labelOperation (.isEmptyLoad actionThread observed) =>
      if h :
          labelOperation = operation ∧
            actionThread = thread then
        some ⟨.returning operation
          (match observed with
          | none => .isEmpty true
          | some _ => .isEmpty false), by
            rcases h with ⟨rfl, rfl⟩
            exact .isEmptyLoad _ _⟩
      else
        none
  | .returning operation commit,
      .respond labelOperation response =>
      if h :
          labelOperation = operation ∧
          response = commit.completed.response then
        some ⟨.idle, by
          rcases h with ⟨rfl, rfl⟩
          exact .respond _ _⟩
      else
        none
  | _, _ =>
      none

/-- Execute one fully observed local source step, rejecting shape mismatches. -/
def step?
    [DecidableEq α]
    (thread : Nat)
    (before : LocalState α)
    (label : Label α) :
    Option (LocalState α) :=
  (checkedStep? thread before label).map Subtype.val

/-- Every accepted executable step is an inductive source step. -/
theorem step?_sound
    [DecidableEq α]
    {thread : Nat}
    {before after : LocalState α}
    {label : Label α}
    (accepted : step? thread before label = some after) :
    LocalStep thread before label after := by
  unfold step? at accepted
  cases checked :
      checkedStep? thread before label with
  | none =>
      simp [checked] at accepted
  | some result =>
      simp only [checked, Option.map_some,
        Option.some.injEq] at accepted
      subst after
      exact result.property

/-- Every inductive source step is accepted by the executable checker. -/
theorem step?_complete
    [DecidableEq α]
    {thread : Nat}
    {before after : LocalState α}
    {label : Label α}
    (step : LocalStep thread before label after) :
    step? thread before label = some after := by
  cases step <;> simp [step?, checkedStep?] <;> rfl

/-- The executable checker characterizes `LocalStep` exactly. -/
theorem step?_eq_some_iff
    [DecidableEq α]
    {thread : Nat}
    {before after : LocalState α}
    {label : Label α} :
    step? thread before label = some after ↔
      LocalStep thread before label after :=
  ⟨step?_sound, step?_complete⟩

/-- A source label has at most one successor from a fixed local state. -/
theorem LocalStep.deterministic
    [DecidableEq α]
    {thread : Nat}
    {before firstAfter secondAfter : LocalState α}
    {label : Label α}
    (first :
      LocalStep thread before label firstAfter)
    (second :
      LocalStep thread before label secondAfter) :
    firstAfter = secondAfter := by
  exact Option.some.inj
    ((step?_complete first).symm.trans
      (step?_complete second))

/-- Execute a finite list of fully observed source labels. -/
def run?
    [DecidableEq α]
    (thread : Nat) :
    LocalState α → List (Label α) → Option (LocalState α)
  | state, [] =>
      some state
  | state, label :: rest =>
      (step? thread state label).bind
        (fun next => run? thread next rest)

/-- A nonempty inductive execution exposes its first step and remaining run. -/
private theorem execution_cons_iff
    {thread : Nat}
    {initial final : LocalState α}
    {label : Label α}
    {rest : List (Label α)} :
    Execution thread initial (label :: rest) final ↔
      ∃ middle,
        LocalStep thread initial label middle ∧
          Execution thread middle rest final := by
  constructor
  · intro execution
    cases execution with
    | cons _ _ first later =>
        exact ⟨_, first, later⟩
  · rintro ⟨middle, first, later⟩
    exact .cons label rest first later

/-- The list runner accepts exactly the inductively valid local executions. -/
theorem run?_eq_some_iff
    [DecidableEq α]
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)} :
    run? thread initial labels = some final ↔
      Execution thread initial labels final := by
  induction labels generalizing initial with
  | nil =>
      constructor
      · intro accepted
        simp only [run?, Option.some.injEq] at accepted
        subst final
        exact .nil initial
      · intro execution
        cases execution
        rfl
  | cons label rest inductionHypothesis =>
      rw [execution_cons_iff]
      unfold run?
      cases checked : step? thread initial label with
      | none =>
          simp only [Option.bind_none, reduceCtorEq, false_iff]
          rintro ⟨middle, first, later⟩
          have accepted := step?_complete first
          rw [checked] at accepted
          contradiction
      | some middle =>
          simp only [Option.bind_some]
          constructor
          · intro accepted
            refine ⟨middle, step?_sound checked, ?_⟩
            exact (inductionHypothesis
              (initial := middle)).mp accepted
          · rintro ⟨actualMiddle, first, later⟩
            have middleShape :
                actualMiddle = middle := by
              apply Option.some.inj
              calc
                some actualMiddle =
                    step? thread initial label :=
                  (step?_complete first).symm
                _ = some middle := checked
            subst actualMiddle
            exact (inductionHypothesis
              (initial := middle)).mpr later

/-- Accepted list runs directly expose their inductive execution witness. -/
theorem run?_sound
    [DecidableEq α]
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)}
    (accepted : run? thread initial labels = some final) :
    Execution thread initial labels final :=
  run?_eq_some_iff.mp accepted

/-- Every inductive execution is accepted by the list runner. -/
theorem run?_complete
    [DecidableEq α]
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)}
    (execution : Execution thread initial labels final) :
    run? thread initial labels = some final :=
  run?_eq_some_iff.mpr execution

end WeakMemory.TreiberRC11.ControlFlow
