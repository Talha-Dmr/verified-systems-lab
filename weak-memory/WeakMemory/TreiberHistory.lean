import WeakMemory.TreiberNodeAccess

namespace WeakMemory.HerlihyWing

/-!
# Finite Herlihy–Wing histories

This module defines a generic, identity-preserving history layer for the
sequential stack specification. It is deliberately independent of Treiber's
control-flow and graph-event generation: no theorem in this file claims that
an RC11 event has a particular operation owner or source response.

A completion is represented by the finite list of completed operations
selected from a history. An operation whose return is already present must be
selected. A pending invocation may either be selected with a proposed return
(corresponding to appending that return) or omitted (corresponding to removing
the still-pending invocation). This is the usual completion/removal step in
the Herlihy–Wing definition, expressed without constructing a second raw
event list.

Classical real-time precedence is intentionally kept separate from RC11
happens-before. Under weak memory, a return in one thread preceding an
invocation in another thread does not by itself create C11 happens-before.
A future source-to-history bridge must therefore prove that its chosen
linearization order is compatible with client real time; core RC11 graph
consistency alone does not discharge that obligation.
-/

/-- Identity of one source-level method invocation. -/
abbrev OperationId := TreiberRC11.ControlFlow.OperationId

/-- One invocation event, including the client thread and abstract method. -/
structure Invocation (α : Type) where
  thread : Nat
  id : OperationId
  operation : StackSpec.Operation α
  deriving Repr, DecidableEq

/-- One method-return event, including the client thread and abstract result. -/
structure Return (α : Type) where
  thread : Nat
  id : OperationId
  response : StackSpec.Response α
  deriving Repr, DecidableEq

/-- Invocation and return events in one finite concurrent history. -/
inductive HistoryEvent (α : Type) where
  | invoke : Invocation α → HistoryEvent α
  | respond : Return α → HistoryEvent α
  deriving Repr, DecidableEq

/-- A finite history in observed client-event order. -/
abbrev History (α : Type) := List (HistoryEvent α)

/--
A completed operation with the identity and thread information erased by the
ordinary sequential stack specification.
-/
structure IdentifiedCompleted (α : Type) where
  thread : Nat
  id : OperationId
  operation : StackSpec.Operation α
  response : StackSpec.Response α
  deriving Repr, DecidableEq

namespace HistoryEvent

/-- The client thread that owns a history event. -/
def thread : HistoryEvent α → Nat
  | .invoke invocation => invocation.thread
  | .respond returned => returned.thread

/-- The operation identity carried by a history event. -/
def operationId : HistoryEvent α → OperationId
  | .invoke invocation => invocation.id
  | .respond returned => returned.id

/-- Extract an invocation identity and discard return events. -/
def invocationId? : HistoryEvent α → Option OperationId
  | .invoke invocation => some invocation.id
  | .respond _ => none

/-- Extract a return identity and discard invocation events. -/
def returnId? : HistoryEvent α → Option OperationId
  | .invoke _ => none
  | .respond returned => some returned.id

end HistoryEvent

/-- Invocation identities in history order. -/
def invocationIds (history : History α) : List OperationId :=
  history.filterMap HistoryEvent.invocationId?

/-- Return identities in history order. -/
def returnIds (history : History α) : List OperationId :=
  history.filterMap HistoryEvent.returnId?

/-- Keep exactly one thread's client events, preserving their order. -/
def eventsForThread
    (thread : Nat) :
    History α → History α
  | [] => []
  | event :: rest =>
      if event.thread = thread then
        event :: eventsForThread thread rest
      else
        eventsForThread thread rest

/-- Thread projection keeps exactly the events owned by the selected thread. -/
theorem mem_eventsForThread
    {thread : Nat}
    {history : History α}
    {event : HistoryEvent α} :
    event ∈ eventsForThread thread history ↔
      event ∈ history ∧ event.thread = thread := by
  induction history with
  | nil =>
      simp [eventsForThread]
  | cons first rest inductionHypothesis =>
      by_cases firstThread : first.thread = thread
      · simp only [eventsForThread, firstThread, ↓reduceIte,
          List.mem_cons]
        constructor
        · intro member
          rcases member with isFirst | inRest
          · subst event
            exact ⟨Or.inl rfl, firstThread⟩
          · have restMember :=
              inductionHypothesis.mp inRest
            exact ⟨Or.inr restMember.1, restMember.2⟩
        · rintro ⟨member, eventThread⟩
          rcases member with isFirst | inRest
          · exact Or.inl isFirst
          · exact Or.inr
              (inductionHypothesis.mpr
                ⟨inRest, eventThread⟩)
      · simp only [eventsForThread, firstThread, ↓reduceIte]
        constructor
        · intro projectedMember
          have restMember :=
            inductionHypothesis.mp projectedMember
          exact ⟨by simp [restMember.1], restMember.2⟩
        · rintro ⟨member, eventThread⟩
          have eventNeFirst : event ≠ first := by
            intro same
            subst first
            exact firstThread eventThread
          have inRest :=
            (List.mem_cons.mp member).resolve_left
              eventNeFirst
          exact inductionHypothesis.mpr
            ⟨inRest, eventThread⟩

/--
One list element occurs strictly before another. Decomposition witnesses are
used instead of numeric positions so the definition remains purely finite.
-/
def Before (first second : β) (items : List β) : Prop :=
  ∃ earlier between later,
    items = earlier ++ first :: between ++ second :: later

namespace Before

/-- The first endpoint of a before witness belongs to the list. -/
theorem first_mem
    {first second : β}
    {items : List β}
    (before : Before first second items) :
    first ∈ items := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  simp

/-- The second endpoint of a before witness belongs to the list. -/
theorem second_mem
    {first second : β}
    {items : List β}
    (before : Before first second items) :
    second ∈ items := by
  rcases before with ⟨earlier, between, later, shape⟩
  subst items
  simp

end Before

/-- An invocation and return belong to the same operation occurrence. -/
def Matches (invocation : Invocation α) (returned : Return α) : Prop :=
  invocation.thread = returned.thread ∧
    invocation.id = returned.id

/--
An invocation is pending when it occurs in the history and has no matching
return anywhere in that finite history.
-/
def Pending
    (history : History α)
    (invocation : Invocation α) : Prop :=
  HistoryEvent.invoke invocation ∈ history ∧
    ∀ returned,
      Matches invocation returned →
      HistoryEvent.respond returned ∉ history

namespace Pending

/-- A pending invocation has no matching return in the base history. -/
theorem no_matching_return
    {history : History α}
    {invocation : Invocation α}
    (pending : Pending history invocation)
    {returned : Return α}
    (matching : Matches invocation returned) :
    HistoryEvent.respond returned ∉ history :=
  pending.2 returned matching

end Pending

namespace IdentifiedCompleted

/-- Recover the invocation event represented by a completed operation. -/
def invocation (entry : IdentifiedCompleted α) : Invocation α where
  thread := entry.thread
  id := entry.id
  operation := entry.operation

/-- Recover the return event represented by a completed operation. -/
def returned (entry : IdentifiedCompleted α) : Return α where
  thread := entry.thread
  id := entry.id
  response := entry.response

/-- Erase identity and thread metadata for the sequential specification. -/
def erase (entry : IdentifiedCompleted α) :
    StackSpec.CompletedOperation α where
  operation := entry.operation
  response := entry.response

/-- Both endpoints of an identified operation occur in the proper order. -/
def Present
    (history : History α)
    (entry : IdentifiedCompleted α) : Prop :=
  Before
    (HistoryEvent.invoke entry.invocation)
    (HistoryEvent.respond entry.returned)
    history

end IdentifiedCompleted

/--
Structural well-formedness of a finite client history.

Operation identifiers are globally fresh, returns are unique, every return
matches an earlier invocation, and one thread cannot invoke its next operation
before returning from its previous one.
-/
structure WellFormed (history : History α) : Prop where
  invocationIdsNodup :
    (invocationIds history).Nodup
  returnIdsNodup :
    (returnIds history).Nodup
  returnHasInvocation :
    ∀ {returned},
      HistoryEvent.respond returned ∈ history →
      ∃ invocation,
        Matches invocation returned ∧
          Before
            (HistoryEvent.invoke invocation)
            (HistoryEvent.respond returned)
            history
  threadSequential :
    ∀ {first second},
      HistoryEvent.invoke first ∈ history →
      HistoryEvent.invoke second ∈ history →
      first.thread = second.thread →
      Before
        (HistoryEvent.invoke first)
        (HistoryEvent.invoke second)
        history →
      ∃ returned,
        Matches first returned ∧
          Before
            (HistoryEvent.invoke first)
            (HistoryEvent.respond returned)
            history ∧
          Before
            (HistoryEvent.respond returned)
            (HistoryEvent.invoke second)
            history

/--
A finite completion choice for a history.

Every chosen entry was invoked and is either already returned or pending.
Every return already visible in the base history is retained. Pending
invocations absent from `operations` are precisely the invocations removed
when taking the complete part of the extended history.
-/
structure Completion
    (history : History α)
    (operations : List (IdentifiedCompleted α)) : Prop where
  operationIdsNodup :
    (operations.map IdentifiedCompleted.id).Nodup
  selected :
    ∀ {entry},
      entry ∈ operations →
      HistoryEvent.invoke entry.invocation ∈ history ∧
        (entry.Present history ∨
          Pending history entry.invocation)
  retainsReturns :
    ∀ {returned},
      HistoryEvent.respond returned ∈ history →
      ∃ entry,
        entry ∈ operations ∧
          entry.returned = returned ∧
          entry.Present history
  threadOrder :
    ∀ {first second},
      first ∈ operations →
      second ∈ operations →
      first.thread = second.thread →
      Before
        (HistoryEvent.invoke first.invocation)
        (HistoryEvent.invoke second.invocation)
        history →
      Before first second operations

namespace Completion

/-- Every selected completed operation has an invocation in the base history. -/
theorem invocation_mem
    {history : History α}
    {operations : List (IdentifiedCompleted α)}
    (completion : Completion history operations)
    {entry : IdentifiedCompleted α}
    (member : entry ∈ operations) :
    HistoryEvent.invoke entry.invocation ∈ history :=
  (completion.selected member).1

/-- A return already present in the history cannot be removed by completion. -/
theorem exists_of_return_mem
    {history : History α}
    {operations : List (IdentifiedCompleted α)}
    (completion : Completion history operations)
    {returned : Return α}
    (member : HistoryEvent.respond returned ∈ history) :
    ∃ entry,
      entry ∈ operations ∧
        entry.returned = returned ∧
        entry.Present history :=
  completion.retainsReturns member

end Completion

/-- Keep one thread's completed operations, preserving their order. -/
def operationsForThread
    (thread : Nat) :
    List (IdentifiedCompleted α) →
      List (IdentifiedCompleted α)
  | [] => []
  | entry :: rest =>
      if entry.thread = thread then
        entry :: operationsForThread thread rest
      else
        operationsForThread thread rest

/--
Completed-operation projection keeps exactly the entries owned by the
selected thread.
-/
theorem mem_operationsForThread
    {thread : Nat}
    {operations : List (IdentifiedCompleted α)}
    {entry : IdentifiedCompleted α} :
    entry ∈ operationsForThread thread operations ↔
      entry ∈ operations ∧ entry.thread = thread := by
  induction operations with
  | nil =>
      simp [operationsForThread]
  | cons first rest inductionHypothesis =>
      by_cases firstThread : first.thread = thread
      · simp only [operationsForThread, firstThread, ↓reduceIte,
          List.mem_cons]
        constructor
        · intro member
          rcases member with isFirst | inRest
          · subst entry
            exact ⟨Or.inl rfl, firstThread⟩
          · have restMember :=
              inductionHypothesis.mp inRest
            exact ⟨Or.inr restMember.1, restMember.2⟩
        · rintro ⟨member, entryThread⟩
          rcases member with isFirst | inRest
          · exact Or.inl isFirst
          · exact Or.inr
              (inductionHypothesis.mpr
                ⟨inRest, entryThread⟩)
      · simp only [operationsForThread, firstThread, ↓reduceIte]
        constructor
        · intro projectedMember
          have restMember :=
            inductionHypothesis.mp projectedMember
          exact ⟨by simp [restMember.1], restMember.2⟩
        · rintro ⟨member, entryThread⟩
          have entryNeFirst : entry ≠ first := by
            intro same
            subst first
            exact firstThread entryThread
          have inRest :=
            (List.mem_cons.mp member).resolve_left
              entryNeFirst
          exact inductionHypothesis.mpr
            ⟨inRest, entryThread⟩

/--
Completed histories are equivalent when they contain the same identified
operations and every client thread observes those operations in the same
order.
-/
def Equivalent
    (left right : List (IdentifiedCompleted α)) : Prop :=
  left.Perm right ∧
    ∀ thread,
      operationsForThread thread left =
        operationsForThread thread right

namespace Equivalent

/-- Per-thread history equivalence is reflexive. -/
theorem refl
    (operations : List (IdentifiedCompleted α)) :
    Equivalent operations operations :=
  ⟨List.Perm.refl operations, fun _ => rfl⟩

/-- Per-thread history equivalence is symmetric. -/
theorem symm
    {left right : List (IdentifiedCompleted α)}
    (equivalent : Equivalent left right) :
    Equivalent right left :=
  ⟨equivalent.1.symm,
    fun thread => (equivalent.2 thread).symm⟩

/-- Per-thread history equivalence is transitive. -/
theorem trans
    {first second third : List (IdentifiedCompleted α)}
    (firstSecond : Equivalent first second)
    (secondThird : Equivalent second third) :
    Equivalent first third :=
  ⟨firstSecond.1.trans secondThird.1,
    fun thread =>
      (firstSecond.2 thread).trans
        (secondThird.2 thread)⟩

end Equivalent

/--
Classical real-time precedence: the first operation returns before the second
operation is invoked in the observed client history.
-/
def RealTimePrecedes
    (history : History α)
    (first second : IdentifiedCompleted α) : Prop :=
  Before
    (HistoryEvent.respond first.returned)
    (HistoryEvent.invoke second.invocation)
    history

/-- A sequential order contains every required real-time precedence edge. -/
def PreservesRealTime
    (history : History α)
    (sequential : List (IdentifiedCompleted α)) : Prop :=
  ∀ {first second},
    first ∈ sequential →
    second ∈ sequential →
    RealTimePrecedes history first second →
    Before first second sequential

/-- Erase operation identities and client threads for the sequential spec. -/
def eraseIdentities
    (operations : List (IdentifiedCompleted α)) :
    List (StackSpec.CompletedOperation α) :=
  operations.map IdentifiedCompleted.erase

@[simp] theorem eraseIdentities_nil :
    eraseIdentities ([] : List (IdentifiedCompleted α)) = [] :=
  rfl

@[simp] theorem eraseIdentities_cons
    (entry : IdentifiedCompleted α)
    (rest : List (IdentifiedCompleted α)) :
    eraseIdentities (entry :: rest) =
      entry.erase :: eraseIdentities rest :=
  rfl

/-- Legality of an identity-preserving sequential history. -/
def SequentiallyLegal
    (initial : List α)
    (operations : List (IdentifiedCompleted α))
    (final : List α) : Prop :=
  StackSpec.Legal initial (eraseIdentities operations) final

/-- The empty identified history is legal and leaves the stack unchanged. -/
theorem sequentiallyLegal_nil (stack : List α) :
    SequentiallyLegal stack [] stack :=
  StackSpec.Legal.nil stack

/-- Prepend one specification-valid operation to a legal identified history. -/
theorem sequentiallyLegal_cons
    {before after final : List α}
    (entry : IdentifiedCompleted α)
    (rest : List (IdentifiedCompleted α))
    (headIsLegal :
      StackSpec.step before entry.operation =
        (entry.response, after))
    (tailIsLegal :
      SequentiallyLegal after rest final) :
    SequentiallyLegal before (entry :: rest) final :=
  StackSpec.Legal.cons
    entry.erase
    (eraseIdentities rest)
    headIsLegal
    tailIsLegal

/--
Finite data witnessing Herlihy–Wing linearizability for the stack
specification.

`completionOperations` performs the standard completion/removal choice.
`sequentialOperations` is an equivalent per-thread sequential history whose
identity-erased form is legal and whose order preserves client real time.
-/
structure Linearization
    (initial : List α)
    (history : History α) where
  wellFormed :
    WellFormed history
  completionOperations :
    List (IdentifiedCompleted α)
  completion :
    Completion history completionOperations
  sequentialOperations :
    List (IdentifiedCompleted α)
  equivalent :
    Equivalent completionOperations sequentialOperations
  preservesRealTime :
    PreservesRealTime history sequentialOperations
  final :
    List α
  legal :
    SequentiallyLegal initial sequentialOperations final

/-- Existence of a finite Herlihy–Wing linearization witness. -/
def Linearizable
    (initial : List α)
    (history : History α) : Prop :=
  Nonempty (Linearization initial history)

namespace Linearization

/-- Expose the ordinary identity-erased sequential legality witness. -/
theorem legal_erased
    {initial : List α}
    {history : History α}
    (linearization : Linearization initial history) :
    StackSpec.Legal initial
      (eraseIdentities linearization.sequentialOperations)
      linearization.final :=
  linearization.legal

/-- The selected completion and sequential witness contain the same entries. -/
theorem completion_perm_sequential
    {initial : List α}
    {history : History α}
    (linearization : Linearization initial history) :
    linearization.completionOperations.Perm
      linearization.sequentialOperations :=
  linearization.equivalent.1

/-- The sequential witness preserves each client's completed-operation order. -/
theorem thread_projection
    {initial : List α}
    {history : History α}
    (linearization : Linearization initial history)
    (thread : Nat) :
    operationsForThread thread
        linearization.completionOperations =
      operationsForThread thread
        linearization.sequentialOperations :=
  linearization.equivalent.2 thread

end Linearization

namespace Linearizable

/-- A linearizable history has a legal identity-erased sequential witness. -/
theorem exists_legal_erased
    {initial : List α}
    {history : History α}
    (linearizable : Linearizable initial history) :
    ∃ operations final,
      StackSpec.Legal initial
        (eraseIdentities operations) final := by
  rcases linearizable with ⟨linearization⟩
  exact ⟨linearization.sequentialOperations,
    linearization.final, linearization.legal⟩

end Linearizable

end WeakMemory.HerlihyWing
