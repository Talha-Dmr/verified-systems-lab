import WeakMemory.TreiberExtractedProgram
import WeakMemory.TreiberControlFlow

namespace WeakMemory.TreiberProgramDescriptor

/-!
# Component check against the formal Treiber program model

The generated descriptor crosses the explicitly trusted Clang-AST extraction
boundary.  This module does not prove a semantics theorem for C.  It proves
the narrower, auditable fact that every generated descriptor component agrees
with the memory-order function and local transition constructors already used
by the Lean model.
-/

open TreiberRC11.ControlFlow

/--
The compact descriptor computed from the existing operational/control-flow
model. Memory-order fields reduce through `TreiberRA.Action.order`; structural
fields name the retry and response shapes witnessed below.
-/
def controlFlowDescriptor : Descriptor where
  initializesHeadToNull :=
    true
  pushLoadOrder :=
    TreiberRA.Action.order
      (.pushLoad 0 none : TreiberRA.Action Unit)
  popLoadOrder :=
    TreiberRA.Action.order
      (.popLoad 0 none : TreiberRA.Action Unit)
  isEmptyLoadOrder :=
    TreiberRA.Action.order
      (.isEmptyLoad 0 none : TreiberRA.Action Unit)
  pushCompareExchange := {
    strength := .weak
    successOrder :=
      TreiberRA.Action.order
        (.pushSuccess 0 0 () none)
    failureOrder :=
      TreiberRA.Action.order
        (.pushFailure 0 0 () none none)
    failureUpdatesExpected := true
  }
  popCompareExchange := {
    strength := .weak
    successOrder :=
      TreiberRA.Action.order
        (.popSuccess 0 0 () none)
    failureOrder :=
      TreiberRA.Action.order
        (.popFailure 0 (some 0) (some 0) :
          TreiberRA.Action Unit)
    failureUpdatesExpected := true
  }
  pushNextBehavior :=
    .pushWritesObservedBeforeEveryAttempt
  popNextBehavior :=
    .popReadsObservedNextBeforeEveryNonNullAttempt
  pushRetryBehavior :=
    .pushUpdatesExpectedThenRewritesNext
  popRetryBehavior :=
    .popUpdatesExpectedThenReadsNextOrReturnsNull
  pushReturnBehavior :=
    .pushReturnsVoidAfterSuccess
  popReturnBehavior :=
    .popReturnsObservedOnSuccessOrNullWhenEmpty
  isEmptyReturnBehavior :=
    .isEmptyReturnsHeadNullTest

/--
The trusted extracted data agrees exactly with the compact descriptor of the
formal program model.

This is data equality after extraction, not a theorem that Clang or C11
implements the Lean transition system.
-/
theorem extractedDescriptor_eq_controlFlowDescriptor :
    Extracted.treiberProgram.descriptor =
      controlFlowDescriptor :=
  rfl

/-! ## Memory-order components -/

@[simp] theorem extracted_pushLoadOrder
    (thread : Nat)
    (observed : Option TreiberRA.NodeId) :
    Extracted.treiberProgram.descriptor.pushLoadOrder =
      TreiberRA.Action.order
        (.pushLoad thread observed : TreiberRA.Action α) :=
  rfl

@[simp] theorem extracted_popLoadOrder
    (thread : Nat)
    (observed : Option TreiberRA.NodeId) :
    Extracted.treiberProgram.descriptor.popLoadOrder =
      TreiberRA.Action.order
        (.popLoad thread observed : TreiberRA.Action α) :=
  rfl

@[simp] theorem extracted_isEmptyLoadOrder
    (thread : Nat)
    (observed : Option TreiberRA.NodeId) :
    Extracted.treiberProgram.descriptor.isEmptyLoadOrder =
      TreiberRA.Action.order
        (.isEmptyLoad thread observed : TreiberRA.Action α) :=
  rfl

@[simp] theorem extracted_pushCompareExchangeOrders
    (thread node : Nat)
    (value : α)
    (expected actual : Option TreiberRA.NodeId) :
    (CompareExchange.successOrder
        Extracted.treiberProgram.descriptor.pushCompareExchange,
      CompareExchange.failureOrder
        Extracted.treiberProgram.descriptor.pushCompareExchange) =
      (TreiberRA.Action.order
          (.pushSuccess thread node value expected),
        TreiberRA.Action.order
          (.pushFailure
            thread node value expected actual)) :=
  rfl

@[simp] theorem extracted_popCompareExchangeOrders
    (thread node : Nat)
    (value : α)
    (next actual : Option TreiberRA.NodeId) :
    (CompareExchange.successOrder
        Extracted.treiberProgram.descriptor.popCompareExchange,
      CompareExchange.failureOrder
        Extracted.treiberProgram.descriptor.popCompareExchange) =
      (TreiberRA.Action.order
          (.popSuccess thread node value next),
        TreiberRA.Action.order
          (.popFailure thread (some node) actual :
            TreiberRA.Action α)) :=
  rfl

@[simp] theorem extracted_compareExchanges_areWeak :
    (CompareExchange.strength
        Extracted.treiberProgram.descriptor.pushCompareExchange,
      CompareExchange.strength
        Extracted.treiberProgram.descriptor.popCompareExchange) =
      (CompareExchangeStrength.weak,
        CompareExchangeStrength.weak) :=
  rfl

/-! ## Initialization and field-access components -/

@[simp] theorem extracted_initializesHeadToNull :
    Extracted.treiberProgram.descriptor.initializesHeadToNull =
      true :=
  rfl

/--
The formal model represents the extracted initializer fact by beginning with
a null head. The heap remains an independent initialization input.
-/
@[simp] theorem initializedModelState_head
    (heap : TreiberRA.Heap α) :
    ({ heap := heap, head := none } :
      TreiberRA.State α).head = none :=
  rfl

/-- From the write-ready state, the only next step writes the expected link. -/
theorem pushWriting_onlyWritesNext
    {thread operation reserved : Nat}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.pushWriting operation reserved value expected)
        label after) :
    label = .writeNext operation reserved expected ∧
      after = .pushing operation reserved value expected :=
  step.fromPushWriting

/-- From the read-ready state, the only next step reads that node's link. -/
theorem popReading_onlyReadsNext
    {thread operation observed : Nat}
    {label : Label α}
    {after : LocalState α}
    (step :
      LocalStep thread
        (.popReading operation observed)
        label after) :
    ∃ next,
      label = .readNext operation observed next ∧
        after = .popping operation observed next :=
  step.fromPopReading

/-! ## Weak-failure and retry components -/

/-- Equal expected/actual values are admitted as a weak push-CAS failure. -/
theorem push_allowsSpuriousFailure
    (thread operation reserved : Nat)
    (value : α)
    (expected : Option TreiberRA.NodeId) :
    LocalStep thread
      (.pushing operation reserved value expected)
      (.atomic operation
        (.pushFailure
          thread reserved value expected expected))
      (.pushWriting operation reserved value expected) :=
  pushSpuriousFailure
    thread operation reserved value expected

/-- Equal expected/actual values are admitted as a weak pop-CAS failure. -/
theorem pop_allowsSpuriousFailure
    (thread operation expected : Nat)
    (next : Option TreiberRA.NodeId) :
    LocalStep thread
      (.popping operation expected next : LocalState α)
      (.atomic operation
        (.popFailure
          thread (some expected) (some expected)))
      (.popReading operation expected) :=
  popSpuriousFailure thread operation expected next

/--
A failed push CAS installs the actual head as the next expectation, then the
only source-shaped retry writes that value to `node->next`.
-/
theorem pushFailure_updatesExpected_thenRewritesNext
    (thread operation reserved : Nat)
    (value : α)
    (expected actual : Option TreiberRA.NodeId) :
    ∃ retryState,
      LocalStep thread
        (.pushing operation reserved value expected)
        (.atomic operation
          (.pushFailure
            thread reserved value expected actual))
        retryState ∧
      LocalStep thread retryState
        (.writeNext operation reserved actual)
        (.pushing operation reserved value actual) := by
  refine
    ⟨.pushWriting operation reserved value actual,
      ?_, ?_⟩
  · exact .pushFailure
      operation reserved value expected actual
  · exact .writeNext operation reserved value actual

/--
A failed non-null pop CAS installs the actual node as the next expectation,
then reads that node's `next` field before another attempt.
-/
theorem popFailure_updatesExpected_thenReadsNext
    (thread operation expected actual : Nat)
    (oldNext newNext : Option TreiberRA.NodeId) :
    ∃ retryState,
      LocalStep thread
        (.popping operation expected oldNext : LocalState α)
        (.atomic operation
          (.popFailure
            thread (some expected) (some actual)))
        retryState ∧
      LocalStep thread retryState
        (.readNext operation actual newNext)
        (.popping operation actual newNext) := by
  refine ⟨.popReading operation actual, ?_, ?_⟩
  · exact .popFailureRetry
      operation expected actual oldNext
  · exact .readNext operation actual newNext

/--
A failed pop CAS that updates the expected operand to null completes empty
instead of reading a node or attempting another CAS.
-/
theorem popFailure_null_returnsEmpty
    (thread operation expected : Nat)
    (next : Option TreiberRA.NodeId) :
    ∃ returning,
      LocalStep thread
        (.popping operation expected next : LocalState α)
        (.atomic operation
          (.popFailure thread (some expected) none))
        returning ∧
      LocalStep thread returning
        (.respond operation (.popped none))
        .idle := by
  refine
    ⟨.returning operation (.popEmpty : Treiber.Commit α),
      ?_, ?_⟩
  · exact .popFailureEmpty operation expected next
  · exact .respond operation .popEmpty

/-! ## Return components -/

/-- A successful push enters and then emits its pushed response. -/
theorem pushSuccess_responds
    (thread operation reserved : Nat)
    (value : α)
    (expected : Option TreiberRA.NodeId) :
    ∃ returning,
      LocalStep thread
        (.pushing operation reserved value expected)
        (.atomic operation
          (.pushSuccess thread reserved value expected))
        returning ∧
      LocalStep thread returning
        (.respond operation .pushed)
        .idle := by
  refine
    ⟨.returning operation (.push value),
      ?_, ?_⟩
  · exact .pushSuccess
      operation reserved value expected
  · exact .respond operation (.push value)

/--
A successful pop retains the observed node identifier in its atomic action
and emits the corresponding payload response.
-/
theorem popSuccess_responds
    (thread operation observed : Nat)
    (value : α)
    (next : Option TreiberRA.NodeId) :
    ∃ returning,
      LocalStep thread
        (.popping operation observed next)
        (.atomic operation
          (.popSuccess thread observed value next))
        returning ∧
      LocalStep thread returning
        (.respond operation (.popped (some value)))
        .idle := by
  refine
    ⟨.returning operation (.popValue value),
      ?_, ?_⟩
  · exact .popSuccess
      operation observed value next
  · exact .respond operation (.popValue value)

/-- An initially null pop load emits the null/empty response. -/
theorem emptyPopLoad_respondsNull
    (thread operation : Nat) :
    ∃ returning,
      LocalStep thread
        (.popLoading operation : LocalState α)
        (.atomic operation (.popLoad thread none))
        returning ∧
      LocalStep thread returning
        (.respond operation (.popped none))
        .idle := by
  refine
    ⟨.returning operation (.popEmpty : Treiber.Commit α),
      ?_, ?_⟩
  · exact .popLoadEmpty operation
  · exact .respond operation .popEmpty

/-- A null `isEmpty` load emits `checkedEmpty true`. -/
theorem isEmpty_null_respondsTrue
    (thread operation : Nat) :
    ∃ returning,
      LocalStep thread
        (.checkingEmpty operation : LocalState α)
        (.atomic operation (.isEmptyLoad thread none))
        returning ∧
      LocalStep thread returning
        (.respond operation (.checkedEmpty true))
        .idle := by
  refine
    ⟨.returning operation (.isEmpty true : Treiber.Commit α),
      ?_, ?_⟩
  · exact .isEmptyLoad operation none
  · exact .respond operation (.isEmpty true)

/-- A non-null `isEmpty` load emits `checkedEmpty false`. -/
theorem isEmpty_nonNull_respondsFalse
    (thread operation observed : Nat) :
    ∃ returning,
      LocalStep thread
        (.checkingEmpty operation : LocalState α)
        (.atomic operation
          (.isEmptyLoad thread (some observed)))
        returning ∧
      LocalStep thread returning
        (.respond operation (.checkedEmpty false))
        .idle := by
  refine
    ⟨.returning operation (.isEmpty false : Treiber.Commit α),
      ?_, ?_⟩
  · exact .isEmptyLoad operation (some observed)
  · exact .respond operation (.isEmpty false)

end WeakMemory.TreiberProgramDescriptor
