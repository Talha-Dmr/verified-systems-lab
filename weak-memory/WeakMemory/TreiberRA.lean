import WeakMemory

namespace WeakMemory.TreiberRA

/-!
# A release-acquire operational fragment for Treiber's stack

This module closes one layer of the gap recorded in `WeakMemory.lean`.
It models:

* an immutable heap of nodes;
* a single atomic `head` pointer;
* successful and failed compare-exchange attempts;
* release publication by `push`;
* acquire observation by `pop`;
* executions as finite sequences of those atomic steps.

Nodes enter the shared heap only at a successful release `push` CAS. A `pop`
may dereference only a node already in that heap, and every pop observation is
acquiring. This is a small operational release-acquire fragment, not the full
RC11 axiomatic model and not yet a semantics of arbitrary C syntax.

The main theorem, `allowedExecution_linearizable`, states that every execution
allowed by this fragment produces a legal sequential stack history.
-/

abbrev NodeId := Nat

/-- Nodes never change after their successful release publication. -/
structure Node (α : Type) where
  value : α
  next : Option NodeId
  deriving Repr, DecidableEq

/-- A partial immutable map from node IDs to published nodes. -/
abbrev Heap (α : Type) := NodeId → Option (Node α)

namespace Heap

def insert (heap : Heap α) (id : NodeId) (node : Node α) : Heap α :=
  fun query => if query = id then some node else heap query

@[simp] theorem insert_same (heap : Heap α) (id : NodeId) (node : Node α) :
    insert heap id node id = some node := by
  simp [insert]

theorem insert_other (heap : Heap α) (id query : NodeId) (node : Node α)
    (different : query ≠ id) :
    insert heap id node query = heap query := by
  simp [insert, different]

/-- Every old heap binding is preserved by an extension. -/
def Extends (old new : Heap α) : Prop :=
  ∀ ⦃id node⦄, old id = some node → new id = some node

theorem insert_extends (heap : Heap α) (id : NodeId) (node : Node α)
    (fresh : heap id = none) :
    Extends heap (insert heap id node) := by
  intro query oldNode oldBinding
  by_cases same : query = id
  · subst query
    simp [fresh] at oldBinding
  · simpa [insert_other, same] using oldBinding

end Heap

/--
`Represents heap head values` means that following immutable `next` pointers
from `head` yields exactly `values`.
-/
inductive Represents (heap : Heap α) : Option NodeId → List α → Prop where
  | empty : Represents heap none []
  | node {id : NodeId} {entry : Node α} {rest : List α}
      (lookup : heap id = some entry)
      (tail : Represents heap entry.next rest) :
      Represents heap (some id) (entry.value :: rest)

namespace Represents

/-- Heap extension cannot invalidate an existing linked-list representation. -/
theorem mono {old new : Heap α} {head : Option NodeId} {values : List α}
    (heapExtension : Heap.Extends old new)
    (representation : Represents old head values) :
    Represents new head values := by
  induction representation with
  | empty =>
      exact .empty
  | node lookup tail inductionHypothesis =>
      exact .node (heapExtension lookup) inductionHypothesis

end Represents

structure State (α : Type) where
  heap : Heap α
  head : Option NodeId

/--
One observable atomic action of the reclamation-free algorithm.

Failure constructors retain both the expected and observed head. Because the
C implementation uses weak compare-exchange, these values may be equal when a
failure is spurious.
-/
inductive Action (α : Type) where
  | pushLoad
      (thread : Nat)
      (observed : Option NodeId)
  | popLoad
      (thread : Nat)
      (observed : Option NodeId)
  | isEmptyLoad
      (thread : Nat)
      (observed : Option NodeId)
  | pushSuccess
      (thread : Nat) (nodeId : NodeId) (value : α)
      (expected : Option NodeId)
  | pushFailure
      (thread : Nat) (nodeId : NodeId) (value : α)
      (expected actual : Option NodeId)
  | popSuccess
      (thread : Nat) (nodeId : NodeId) (value : α)
      (next : Option NodeId)
  | popFailure
      (thread : Nat) (expected actual : Option NodeId)
  | popEmpty
      (thread : Nat)
  deriving Repr, DecidableEq

namespace Action

/-- Memory orders used by the C implementation in `c/treiber.c`. -/
def order : Action α → MemoryOrder
  | .pushLoad .. => .relaxed
  | .popLoad .. => .acquire
  | .isEmptyLoad .. => .acquire
  | .pushSuccess .. => .release
  | .pushFailure .. => .relaxed
  | .popSuccess .. => .acquire
  | .popFailure .. => .acquire
  | .popEmpty .. => .acquire

/-- Only linearization-point actions produce abstract commits. -/
def commit? : Action α → Option (Treiber.Commit α)
  | .pushLoad .. => none
  | .popLoad _ none => some .popEmpty
  | .popLoad _ (some _) => none
  | .isEmptyLoad _ none => some (.isEmpty true)
  | .isEmptyLoad _ (some _) => some (.isEmpty false)
  | .pushSuccess _ _ value _ => some (.push value)
  | .pushFailure .. => none
  | .popSuccess _ _ value _ => some (.popValue value)
  | .popFailure _ _ none => some .popEmpty
  | .popFailure _ _ (some _) => none
  | .popEmpty _ => some .popEmpty

/--
A failed pop compare-exchange that observes null is the empty-pop
linearization point: the C loop returns without issuing another atomic read.
-/
@[simp] theorem popFailure_none_commits
    (thread : Nat)
    (expected : Option NodeId) :
    commit? (.popFailure thread expected none : Action α) =
      some .popEmpty :=
  rfl

/-- A failed pop compare-exchange that observes a node only retries. -/
@[simp] theorem popFailure_some_stutters
    (thread : Nat)
    (expected : Option NodeId)
    (actual : NodeId) :
    commit? (.popFailure thread expected (some actual) : Action α) =
      none :=
  rfl

@[simp] theorem pushSuccess_hasRelease (thread nodeId : Nat) (value : α)
    (expected : Option NodeId) :
    (order (.pushSuccess thread nodeId value expected)).hasRelease = true := rfl

@[simp] theorem popSuccess_hasAcquire (thread nodeId : Nat) (value : α)
    (next : Option NodeId) :
    (order (.popSuccess thread nodeId value next)).hasAcquire = true := rfl

@[simp] theorem popEmpty_hasAcquire (thread : Nat) :
    (order (.popEmpty thread : Action α)).hasAcquire = true := rfl

@[simp] theorem pushLoad_isRelaxed
    (thread : Nat)
    (observed : Option NodeId) :
    order (.pushLoad thread observed : Action α) = .relaxed :=
  rfl

@[simp] theorem popLoad_hasAcquire
    (thread : Nat)
    (observed : Option NodeId) :
    (order (.popLoad thread observed : Action α)).hasAcquire = true :=
  rfl

@[simp] theorem isEmptyLoad_hasAcquire
    (thread : Nat)
    (observed : Option NodeId) :
    (order (.isEmptyLoad thread observed : Action α)).hasAcquire = true :=
  rfl

end Action

/--
Atomic transition relation for the small RA fragment.

The successful push constructor enforces fresh allocation. Successful pop can
only use the node currently at `head`; failed weak-CAS steps record the current
head and do not change shared state, including on spurious failure.
-/
inductive Step : State α → Action α → State α → Prop where
  | pushLoad
      (state : State α)
      (thread : Nat) :
      Step state
        (.pushLoad thread state.head)
        state
  | popLoad
      (state : State α)
      (thread : Nat) :
      Step state
        (.popLoad thread state.head)
        state
  | isEmptyLoad
      (state : State α)
      (thread : Nat) :
      Step state
        (.isEmptyLoad thread state.head)
        state
  | pushSuccess
      (state : State α)
      (thread : Nat)
      (nodeId : NodeId)
      (value : α)
      (fresh : state.heap nodeId = none) :
      Step state
        (.pushSuccess thread nodeId value state.head)
        { heap := state.heap.insert nodeId
            { value := value, next := state.head },
          head := some nodeId }
  | pushFailure
      (state : State α)
      (thread : Nat)
      (nodeId : NodeId)
      (value : α)
      (expected : Option NodeId) :
      Step state
        (.pushFailure thread nodeId value expected state.head)
        state
  | popSuccess
      (heap : Heap α)
      (thread : Nat)
      (nodeId : NodeId)
      (node : Node α)
      (lookup : heap nodeId = some node) :
      Step
        { heap := heap, head := some nodeId }
        (.popSuccess thread nodeId node.value node.next)
        { heap := heap, head := node.next }
  | popFailure
      (state : State α)
      (thread : Nat)
      (expected : Option NodeId) :
      Step state
        (.popFailure thread expected state.head)
        state
  | popEmpty
      (heap : Heap α)
      (thread : Nat) :
      Step
        { heap := heap, head := none }
        (.popEmpty thread)
        { heap := heap, head := none }

/--
CAS failures leave the concrete state unchanged. A pop failure that observes
null nevertheless commits an abstract empty pop because the C loop then
returns immediately.
-/
def ProjectedStep (before : List α) (action : Action α)
    (after : List α) : Prop :=
  match action.commit? with
  | none => after = before
  | some commit => Treiber.CommitStep before commit after

/--
The local bridge lemma. One concrete heap/CAS transition preserves the linked
list invariant and either stutters or performs exactly one abstract commit.
-/
theorem step_refines {beforeState afterState : State α}
    {action : Action α} {beforeValues : List α}
    (transition : Step beforeState action afterState)
    (representation :
      Represents beforeState.heap beforeState.head beforeValues) :
    ∃ afterValues,
      Represents afterState.heap afterState.head afterValues ∧
      ProjectedStep beforeValues action afterValues := by
  cases transition with
  | pushLoad thread =>
      exact ⟨beforeValues, representation, rfl⟩
  | popLoad thread =>
      cases beforeState with
      | mk heap head =>
          cases head with
          | none =>
              cases representation
              exact ⟨[], Represents.empty,
                Treiber.CommitStep.popEmpty⟩
          | some nodeId =>
              exact ⟨beforeValues, representation, rfl⟩
  | isEmptyLoad thread =>
      cases beforeState with
      | mk heap head =>
          cases head with
          | none =>
              cases representation
              exact ⟨[], Represents.empty,
                Treiber.CommitStep.isEmptyTrue⟩
          | some nodeId =>
              cases representation with
              | @node representedId entry rest lookup tail =>
                  exact ⟨entry.value :: rest,
                    Represents.node lookup tail,
                    Treiber.CommitStep.isEmptyFalse
                      entry.value rest⟩
  | pushSuccess state thread nodeId value fresh =>
      let node : Node α := { value := value, next := beforeState.head }
      have heapExtension :
          Heap.Extends beforeState.heap
            (beforeState.heap.insert nodeId node) :=
        Heap.insert_extends beforeState.heap nodeId node fresh
      have oldTail :
          Represents (beforeState.heap.insert nodeId node)
            beforeState.head beforeValues :=
        representation.mono heapExtension
      refine ⟨value :: beforeValues, ?_, ?_⟩
      · exact Represents.node
          (Heap.insert_same beforeState.heap nodeId node)
          oldTail
      · exact Treiber.CommitStep.push value beforeValues
  | pushFailure state thread nodeId value expected =>
      exact ⟨beforeValues, representation, rfl⟩
  | popSuccess heap thread nodeId node lookup =>
      cases representation with
      | @node representedId representedNode representedRest
          representedLookup tail =>
          have nodesEqual : node = representedNode := by
            exact Option.some.inj (lookup.symm.trans representedLookup)
          subst nodesEqual
          exact ⟨representedRest, tail,
            Treiber.CommitStep.popValue node.value representedRest⟩
  | popFailure thread expected =>
      cases beforeState with
      | mk heap head =>
          cases head with
          | none =>
              cases representation
              exact ⟨[], Represents.empty,
                Treiber.CommitStep.popEmpty⟩
          | some nodeId =>
              exact ⟨beforeValues, representation, rfl⟩
  | popEmpty heap thread =>
      cases representation
      exact ⟨[], Represents.empty, Treiber.CommitStep.popEmpty⟩

/-- A finite execution is a sequence of allowed atomic transitions. -/
inductive AllowedExecution :
    State α → List (Action α) → State α → Prop where
  | nil (state : State α) :
      AllowedExecution state [] state
  | cons {initial middle final : State α}
      (action : Action α)
      (rest : List (Action α))
      (first : Step initial action middle)
      (later : AllowedExecution middle rest final) :
      AllowedExecution initial (action :: rest) final

/-- Retain exactly the actions that serve as linearization-point commits. -/
def commits : List (Action α) → List (Treiber.Commit α)
  | [] => []
  | action :: rest =>
      match action.commit? with
      | none => commits rest
      | some commit => commit :: commits rest

/--
Every allowed concrete execution induces a valid abstract commit trace while
preserving the concrete linked-list representation.
-/
theorem allowedExecution_inducesCommitTrace
    {initial final : State α}
    {actions : List (Action α)}
    {initialValues : List α}
    (execution : AllowedExecution initial actions final)
    (initialRepresentation :
      Represents initial.heap initial.head initialValues) :
    ∃ finalValues,
      Represents final.heap final.head finalValues ∧
      Treiber.CommitTrace initialValues (commits actions) finalValues := by
  induction execution generalizing initialValues with
  | nil state =>
      exact ⟨initialValues, initialRepresentation,
        Treiber.CommitTrace.nil initialValues⟩
  | cons action rest first later inductionHypothesis =>
      obtain ⟨middleValues, middleRepresentation, projected⟩ :=
        step_refines first initialRepresentation
      obtain ⟨finalValues, finalRepresentation, tailTrace⟩ :=
        inductionHypothesis middleRepresentation
      refine ⟨finalValues, finalRepresentation, ?_⟩
      unfold ProjectedStep at projected
      cases commitEquation : action.commit? with
      | none =>
          rw [commitEquation] at projected
          subst middleValues
          simp [commits, commitEquation]
          exact tailTrace
      | some commit =>
          rw [commitEquation] at projected
          simp only [commits, commitEquation]
          exact Treiber.CommitTrace.cons commit (commits rest)
            projected tailTrace

/--
End-to-end theorem for the current formal layer: every allowed execution is
linearizable with respect to the ordinary sequential stack specification.
-/
theorem allowedExecution_linearizable
    {initial final : State α}
    {actions : List (Action α)}
    {initialValues : List α}
    (execution : AllowedExecution initial actions final)
    (initialRepresentation :
      Represents initial.heap initial.head initialValues) :
    ∃ finalValues,
      Represents final.heap final.head finalValues ∧
      StackSpec.Legal initialValues
        (Treiber.completedHistory (commits actions))
        finalValues := by
  obtain ⟨finalValues, finalRepresentation, commitTrace⟩ :=
    allowedExecution_inducesCommitTrace execution initialRepresentation
  exact ⟨finalValues, finalRepresentation,
    Treiber.commitTrace_linearizable commitTrace⟩

end WeakMemory.TreiberRA
