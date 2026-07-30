import WeakMemory.TreiberRC11

namespace WeakMemory.TreiberRC11

/-!
# Executable replay for RC11-style Treiber graphs

The relational graph conditions determine atomic-head observations, but they
do not by themselves validate Treiber-specific heap facts. For example, a
candidate event can name the correct head node while attaching the wrong
payload to a successful pop.

This module makes that remaining boundary executable and auditable:

1. `applyAction?` checks one algorithm action against a concrete RA state;
2. `replay?` checks a finite event order;
3. `applyAction?_sound` and `replay?_sound` prove that acceptance produces the
   corresponding inductive operational execution;
4. `AcceptedExecution.certifiedSchedule` constructs the certificate required
   by the graph-to-linearizability theorem.

The accepted-execution interface below uses the finite graph enumeration as
its event order and certifies that it respects `po` and all of `eco`.
`WeakMemory.TreiberSchedule` separately constructs an arbitrary respecting
order from explicit acyclicity of the combined scheduling relation.
`WeakMemory.TreiberOrderAcyclic` later derives that acyclicity from
well-formedness and coherence.
`WeakMemory.TreiberInvariant` then derives replay acceptance for that order
from explicit allocation and publication invariants.
-/

/--
Check one Treiber action against the current operational state.

The checker validates successful-CAS expectations, fresh push allocation,
failed weak-CAS observations (including spurious failures), published node
contents, and empty-stack reads.
-/
def applyAction? [DecidableEq α]
    (state : TreiberRA.State α)
    (action : TreiberRA.Action α) : Option (TreiberRA.State α) :=
  match action with
  | .pushSuccess _ nodeId value expected =>
      if expected = state.head then
        match state.heap nodeId with
        | none =>
            some {
              heap := state.heap.insert nodeId
                { value := value, next := state.head }
              head := some nodeId
            }
        | some _ => none
      else
        none
  | .pushFailure _ _ _ _ actual =>
      if actual = state.head then
        some state
      else
        none
  | .popSuccess _ nodeId value next =>
      if state.head = some nodeId then
        match state.heap nodeId with
        | none => none
        | some node =>
            if node.value = value then
              if node.next = next then
                some { heap := state.heap, head := next }
              else
                none
            else
              none
      else
        none
  | .popFailure _ _ actual =>
      if actual = state.head then
        some state
      else
        none
  | .popEmpty _ =>
      if state.head = none then some state else none

/--
A weak push compare-exchange may fail spuriously even when its expected value
equals the current head.
-/
@[simp] theorem applyAction?_pushFailure_spurious
    [DecidableEq α]
    (state : TreiberRA.State α)
    (thread nodeId : Nat)
    (value : α) :
    applyAction? state
        (.pushFailure thread nodeId value state.head state.head) =
      some state := by
  simp [applyAction?]

/--
A weak pop compare-exchange may likewise fail spuriously without changing the
shared head.
-/
@[simp] theorem applyAction?_popFailure_spurious
    [DecidableEq α]
    (state : TreiberRA.State α)
    (thread : Nat) :
    applyAction? state
        (.popFailure thread state.head state.head) =
      some state := by
  simp [applyAction?]

/-- Every state transition accepted by `applyAction?` is an RA step. -/
theorem applyAction?_sound [DecidableEq α]
    {state final : TreiberRA.State α}
    {action : TreiberRA.Action α}
    (accepted : applyAction? state action = some final) :
    TreiberRA.Step state action final := by
  cases state with
  | mk heap head =>
      cases action with
      | pushSuccess thread nodeId value expected =>
          simp only [applyAction?] at accepted
          split at accepted
          next expectedMatches =>
            split at accepted
            next lookup =>
              cases accepted
              subst expected
              exact TreiberRA.Step.pushSuccess
                { heap := heap, head := head }
                thread nodeId value lookup
            next lookup =>
              contradiction
          next expectedDiffers =>
            contradiction
      | pushFailure thread nodeId value expected actual =>
          simp only [applyAction?] at accepted
          split at accepted
          next actualMatches =>
            cases accepted
            subst actual
            exact TreiberRA.Step.pushFailure
              { heap := heap, head := head }
              thread nodeId value expected
          next actualDiffers =>
            contradiction
      | popSuccess thread nodeId value next =>
          simp only [applyAction?] at accepted
          split at accepted
          next headMatches =>
            split at accepted
            next lookup =>
              contradiction
            next node lookup =>
              split at accepted
              next valueMatches =>
                split at accepted
                next nextMatches =>
                  cases accepted
                  subst head
                  subst value
                  subst next
                  exact TreiberRA.Step.popSuccess
                    heap thread nodeId node lookup
                next nextDiffers =>
                  contradiction
              next valueDiffers =>
                contradiction
          next headDiffers =>
            contradiction
      | popFailure thread expected actual =>
          simp only [applyAction?] at accepted
          split at accepted
          next actualMatches =>
            cases accepted
            subst actual
            exact TreiberRA.Step.popFailure
              { heap := heap, head := head }
              thread expected
          next actualDiffers =>
            contradiction
      | popEmpty thread =>
          simp only [applyAction?] at accepted
          split at accepted
          next empty =>
            cases accepted
            subst head
            exact TreiberRA.Step.popEmpty heap thread
          next notEmpty =>
            contradiction

/-- Every relational RA step is accepted by the executable checker. -/
theorem applyAction?_complete [DecidableEq α]
    {state final : TreiberRA.State α}
    {action : TreiberRA.Action α}
    (transition : TreiberRA.Step state action final) :
    applyAction? state action = some final := by
  cases transition with
  | pushSuccess state thread nodeId value fresh =>
      simp [applyAction?, fresh]
  | pushFailure state thread nodeId value expected =>
      simp [applyAction?]
  | popSuccess heap thread nodeId node lookup =>
      simp [applyAction?, lookup]
  | popFailure state thread expected =>
      simp [applyAction?]
  | popEmpty heap thread =>
      simp [applyAction?]

/-- The executable checker characterizes exactly one operational RA step. -/
theorem applyAction?_eq_some_iff [DecidableEq α]
    {state final : TreiberRA.State α}
    {action : TreiberRA.Action α} :
    applyAction? state action = some final ↔
      TreiberRA.Step state action final :=
  ⟨applyAction?_sound, applyAction?_complete⟩

/-- Replay graph events in the supplied finite order, skipping the initializer. -/
def replay? [DecidableEq α] :
    TreiberRA.State α →
    List (Event α) →
    Option (TreiberRA.State α)
  | state, [] => some state
  | state, event :: rest =>
      match event.kind with
      | .initial => replay? state rest
      | .algorithm action =>
          match applyAction? state action with
          | none => none
          | some next => replay? next rest

/--
Successful executable replay produces the relational scheduled execution used
by the previous RC11 bridge.
-/
theorem replay?_sound [DecidableEq α]
    (graph : Graph α)
    {initial final : TreiberRA.State α}
    {schedule : List (Event α)}
    (contained :
      ∀ event, event ∈ schedule → event ∈ graph.events)
    (accepted : replay? initial schedule = some final) :
    ScheduledExecution graph initial schedule final := by
  induction schedule generalizing initial with
  | nil =>
      simp only [replay?] at accepted
      cases accepted
      exact ScheduledExecution.nil _
  | cons event rest inductionHypothesis =>
      have member : event ∈ graph.events :=
        contained event (by simp)
      cases event with
      | mk id kind =>
          cases kind with
          | initial =>
              simp only [replay?] at accepted
              apply ScheduledExecution.initial
                { id := id, kind := .initial } rest member
              · trivial
              · apply inductionHypothesis
                · intro later laterMember
                  exact contained later (by simp [laterMember])
                · exact accepted
          | algorithm action =>
              simp only [replay?] at accepted
              cases stepEquation :
                  applyAction? initial action with
              | none =>
                  simp [stepEquation] at accepted
              | some middle =>
                  rw [stepEquation] at accepted
                  apply ScheduledExecution.algorithm
                    { id := id, kind := .algorithm action }
                    rest action member
                  · rfl
                  · exact applyAction?_sound stepEquation
                  · apply inductionHypothesis
                    · intro later laterMember
                      exact contained later (by simp [laterMember])
                    · exact accepted

/-- Every relational scheduled execution is accepted by executable replay. -/
theorem replay?_complete [DecidableEq α]
    {graph : Graph α}
    {initial final : TreiberRA.State α}
    {schedule : List (Event α)}
    (execution : ScheduledExecution graph initial schedule final) :
    replay? initial schedule = some final := by
  induction execution with
  | nil state =>
      rfl
  | initial event rest member isInitial later inductionHypothesis =>
      cases event with
      | mk id kind =>
          cases kind with
          | initial =>
              exact inductionHypothesis
          | algorithm action =>
              simp [Event.IsInitial] at isInitial
  | algorithm event rest action member projects first later
      inductionHypothesis =>
      cases event with
      | mk id kind =>
          cases kind with
          | initial =>
              simp [Event.action?] at projects
          | algorithm projected =>
              simp [Event.action?] at projects
              cases projects
              simp only [replay?, applyAction?_complete first]
              exact inductionHypothesis

/--
For schedules contained in the graph, executable replay and the relational
execution judgment are equivalent.
-/
theorem replay?_eq_some_iff [DecidableEq α]
    (graph : Graph α)
    {initial final : TreiberRA.State α}
    {schedule : List (Event α)}
    (contained :
      ∀ event, event ∈ schedule → event ∈ graph.events) :
    replay? initial schedule = some final ↔
      ScheduledExecution graph initial schedule final :=
  ⟨replay?_sound graph contained, replay?_complete⟩

/--
The graph's stored enumeration is a linear witness for its required ordering
relations. It is deliberately separate from operational replay.
-/
structure Chronological (graph : Graph α) : Prop where
  programOrderBefore :
    ∀ {source target},
      graph.programOrder source target →
      Before source target graph.events
  extendedCoherenceBefore :
    ∀ {source target},
      graph.ExtendedCoherence source target →
      Before source target graph.events

theorem Chronological.respectsGraph
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (chronological : Chronological graph) :
    RespectsGraph graph graph.events where
  covers _ := Iff.rfl
  noDuplicates := wellFormed.noDuplicateEvents
  programOrder edge := chronological.programOrderBefore edge
  extendedCoherence edge := chronological.extendedCoherenceBefore edge

/--
An accepted execution combines relational RC11-style well-formedness, an
explicit linear-order witness, and successful deterministic operational
replay. Unlike `CertifiedSchedule`, the operational component is a computable
equation rather than an assumed inductive execution derivation.
-/
structure AcceptedExecution [DecidableEq α]
    (graph : Graph α)
    (initial final : TreiberRA.State α) : Prop where
  consistent :
    CoreConsistent graph
  chronological :
    Chronological graph
  replayAccepted :
    replay? initial graph.events = some final

/-- Every accepted graph execution yields the previous bridge certificate. -/
theorem AcceptedExecution.certifiedSchedule [DecidableEq α]
    {graph : Graph α}
    {initial final : TreiberRA.State α}
    (accepted : AcceptedExecution graph initial final) :
    CertifiedSchedule graph initial graph.events final where
  consistent := accepted.consistent
  respectsGraph := accepted.chronological.respectsGraph
    accepted.consistent.toWellFormed
  executes := replay?_sound graph
    (fun _ member => member)
    accepted.replayAccepted

/--
End-to-end theorem for an accepted, executable RC11-style graph.

The abstract history contains exactly the successful operations obtained by
projecting the graph's finite event enumeration.
-/
theorem acceptedExecution_linearizable [DecidableEq α]
    {graph : Graph α}
    {initial final : TreiberRA.State α}
    {initialValues : List α}
    (accepted : AcceptedExecution graph initial final)
    (initialRepresentation :
      TreiberRA.Represents initial.heap initial.head initialValues) :
    ∃ finalValues,
      TreiberRA.Represents final.heap final.head finalValues ∧
      StackSpec.Legal initialValues
        (Treiber.completedHistory
          (TreiberRA.commits (projectedActions graph.events)))
        finalValues :=
  certifiedSchedule_linearizable accepted.certifiedSchedule
    initialRepresentation

namespace ReplayExample

def emptyHeap : TreiberRA.Heap Nat :=
  fun _ => none

def initialState : TreiberRA.State Nat where
  heap := emptyHeap
  head := none

def pushedState : TreiberRA.State Nat where
  heap := emptyHeap.insert 7 { value := 42, next := none }
  head := some 7

def finalState : TreiberRA.State Nat where
  heap := pushedState.heap
  head := none

def pushThenPop : List (Event Nat) :=
  [
    { id := 0, kind := .initial },
    {
      id := 1
      kind := .algorithm (.pushSuccess 0 7 42 none)
    },
    {
      id := 2
      kind := .algorithm (.popSuccess 1 7 42 none)
    }
  ]

/-- A concrete push followed by a pop is accepted by executable replay. -/
theorem pushThenPop_replays :
    replay? initialState pushThenPop = some finalState := by
  rfl

end ReplayExample

end WeakMemory.TreiberRC11
