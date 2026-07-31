import WeakMemory.MSQueueSource
import WeakMemory.TreiberHistory

namespace WeakMemory.MSQueue.HW

/-!
# Finite Herlihy--Wing histories for Michael--Scott queue

This module instantiates the finite, identity-preserving history layer for the
FIFO queue specification.  It remains independent of the source-to-history
bridge: operation identities, client events, completion choices, per-thread
equivalence, and real-time order are represented here, while later modules
must connect source executions and abstract commits to these objects.

The generic strict list order is reused from `WeakMemory.HerlihyWing.Before`.
As in the stack history layer, client real-time precedence is intentionally
separate from RC11 happens-before.
-/

/-- One invocation event, including the client thread and abstract method. -/
structure Invocation (Value : Type) where
  thread : Source.ThreadId
  id : Source.OperationId
  operation : QueueSpec.Operation Value
  deriving Repr, DecidableEq

/-- One method-return event, including the client thread and abstract result. -/
structure Return (Value : Type) where
  thread : Source.ThreadId
  id : Source.OperationId
  response : QueueSpec.Response Value
  deriving Repr, DecidableEq

/-- Invocation and return events in one finite concurrent history. -/
inductive HistoryEvent (Value : Type) where
  | invoke : Invocation Value → HistoryEvent Value
  | respond : Return Value → HistoryEvent Value
  deriving Repr, DecidableEq

/-- A finite history in observed client-event order. -/
abbrev History (Value : Type) := List (HistoryEvent Value)

/--
A completed operation retaining source identity and thread information.
-/
structure IdentifiedCompleted (Value : Type) where
  thread : Source.ThreadId
  id : Source.OperationId
  operation : QueueSpec.Operation Value
  response : QueueSpec.Response Value
  deriving Repr, DecidableEq

namespace HistoryEvent

/-- The client thread that owns a history event. -/
def thread : HistoryEvent Value → Source.ThreadId
  | .invoke invocation => invocation.thread
  | .respond returned => returned.thread

/-- The operation identity carried by a history event. -/
def operationId : HistoryEvent Value → Source.OperationId
  | .invoke invocation => invocation.id
  | .respond returned => returned.id

/-- Extract an invocation identity and discard return events. -/
def invocationId? : HistoryEvent Value → Option Source.OperationId
  | .invoke invocation => some invocation.id
  | .respond _ => none

/-- Extract a return identity and discard invocation events. -/
def returnId? : HistoryEvent Value → Option Source.OperationId
  | .invoke _ => none
  | .respond returned => some returned.id

end HistoryEvent

/-- Invocation identities in history order. -/
def invocationIds (history : History Value) : List Source.OperationId :=
  history.filterMap HistoryEvent.invocationId?

/-- Return identities in history order. -/
def returnIds (history : History Value) : List Source.OperationId :=
  history.filterMap HistoryEvent.returnId?

/-- Keep exactly one thread's client events, preserving their order. -/
def eventsForThread
    (thread : Source.ThreadId) :
    History Value → History Value
  | [] => []
  | event :: rest =>
      if event.thread = thread then
        event :: eventsForThread thread rest
      else
        eventsForThread thread rest

/-- Thread projection keeps exactly the events owned by the selected thread. -/
theorem mem_eventsForThread
    {thread : Source.ThreadId}
    {history : History Value}
    {event : HistoryEvent Value} :
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
          · have restMember := inductionHypothesis.mp inRest
            exact ⟨Or.inr restMember.1, restMember.2⟩
        · rintro ⟨member, eventThread⟩
          rcases member with isFirst | inRest
          · exact Or.inl isFirst
          · exact Or.inr
              (inductionHypothesis.mpr ⟨inRest, eventThread⟩)
      · simp only [eventsForThread, firstThread, ↓reduceIte]
        constructor
        · intro projectedMember
          have restMember := inductionHypothesis.mp projectedMember
          exact ⟨by simp [restMember.1], restMember.2⟩
        · rintro ⟨member, eventThread⟩
          have eventNeFirst : event ≠ first := by
            intro same
            subst first
            exact firstThread eventThread
          have inRest :=
            (List.mem_cons.mp member).resolve_left eventNeFirst
          exact inductionHypothesis.mpr ⟨inRest, eventThread⟩

/-- An invocation and return belong to the same operation occurrence. -/
def Matches (invocation : Invocation Value) (returned : Return Value) : Prop :=
  invocation.thread = returned.thread ∧
    invocation.id = returned.id

/--
An invocation is pending when it occurs in the history and has no matching
return anywhere in that finite history.
-/
def Pending
    (history : History Value)
    (invocation : Invocation Value) : Prop :=
  HistoryEvent.invoke invocation ∈ history ∧
    ∀ returned,
      Matches invocation returned →
      HistoryEvent.respond returned ∉ history

namespace Pending

/-- A pending invocation has no matching return in the base history. -/
theorem no_matching_return
    {history : History Value}
    {invocation : Invocation Value}
    (pending : Pending history invocation)
    {returned : Return Value}
    (matching : Matches invocation returned) :
    HistoryEvent.respond returned ∉ history :=
  pending.2 returned matching

end Pending

namespace IdentifiedCompleted

/-- Recover the invocation event represented by a completed operation. -/
def invocation (entry : IdentifiedCompleted Value) : Invocation Value where
  thread := entry.thread
  id := entry.id
  operation := entry.operation

/-- Recover the return event represented by a completed operation. -/
def returned (entry : IdentifiedCompleted Value) : Return Value where
  thread := entry.thread
  id := entry.id
  response := entry.response

/-- Erase identity and thread metadata for the sequential specification. -/
def erase (entry : IdentifiedCompleted Value) :
    QueueSpec.CompletedOperation Value where
  operation := entry.operation
  response := entry.response

/-- Both endpoints of an identified operation occur in the proper order. -/
def Present
    (history : History Value)
    (entry : IdentifiedCompleted Value) : Prop :=
  HerlihyWing.Before
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
structure WellFormed (history : History Value) : Prop where
  invocationIdsNodup :
    (invocationIds history).Nodup
  returnIdsNodup :
    (returnIds history).Nodup
  returnHasInvocation :
    ∀ {returned},
      HistoryEvent.respond returned ∈ history →
      ∃ invocation,
        Matches invocation returned ∧
          HerlihyWing.Before
            (HistoryEvent.invoke invocation)
            (HistoryEvent.respond returned)
            history
  threadSequential :
    ∀ {first second},
      HistoryEvent.invoke first ∈ history →
      HistoryEvent.invoke second ∈ history →
      first.thread = second.thread →
      HerlihyWing.Before
        (HistoryEvent.invoke first)
        (HistoryEvent.invoke second)
        history →
      ∃ returned,
        Matches first returned ∧
          HerlihyWing.Before
            (HistoryEvent.invoke first)
            (HistoryEvent.respond returned)
            history ∧
          HerlihyWing.Before
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
    (history : History Value)
    (operations : List (IdentifiedCompleted Value)) : Prop where
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
      HerlihyWing.Before
        (HistoryEvent.invoke first.invocation)
        (HistoryEvent.invoke second.invocation)
        history →
      HerlihyWing.Before first second operations

namespace Completion

/-- Every selected completed operation has an invocation in the base history. -/
theorem invocation_mem
    {history : History Value}
    {operations : List (IdentifiedCompleted Value)}
    (completion : Completion history operations)
    {entry : IdentifiedCompleted Value}
    (member : entry ∈ operations) :
    HistoryEvent.invoke entry.invocation ∈ history :=
  (completion.selected member).1

/-- A return already present in the history cannot be removed by completion. -/
theorem exists_of_return_mem
    {history : History Value}
    {operations : List (IdentifiedCompleted Value)}
    (completion : Completion history operations)
    {returned : Return Value}
    (member : HistoryEvent.respond returned ∈ history) :
    ∃ entry,
      entry ∈ operations ∧
        entry.returned = returned ∧
        entry.Present history :=
  completion.retainsReturns member

end Completion

/-- Keep one thread's completed operations, preserving their order. -/
def operationsForThread
    (thread : Source.ThreadId) :
    List (IdentifiedCompleted Value) →
      List (IdentifiedCompleted Value)
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
    {thread : Source.ThreadId}
    {operations : List (IdentifiedCompleted Value)}
    {entry : IdentifiedCompleted Value} :
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
          · have restMember := inductionHypothesis.mp inRest
            exact ⟨Or.inr restMember.1, restMember.2⟩
        · rintro ⟨member, entryThread⟩
          rcases member with isFirst | inRest
          · exact Or.inl isFirst
          · exact Or.inr
              (inductionHypothesis.mpr ⟨inRest, entryThread⟩)
      · simp only [operationsForThread, firstThread, ↓reduceIte]
        constructor
        · intro projectedMember
          have restMember := inductionHypothesis.mp projectedMember
          exact ⟨by simp [restMember.1], restMember.2⟩
        · rintro ⟨member, entryThread⟩
          have entryNeFirst : entry ≠ first := by
            intro same
            subst first
            exact firstThread entryThread
          have inRest :=
            (List.mem_cons.mp member).resolve_left entryNeFirst
          exact inductionHypothesis.mpr ⟨inRest, entryThread⟩

/--
Completed histories are equivalent when they contain the same identified
operations and every client thread observes those operations in the same
order.
-/
def Equivalent
    (left right : List (IdentifiedCompleted Value)) : Prop :=
  left.Perm right ∧
    ∀ thread,
      operationsForThread thread left =
        operationsForThread thread right

namespace Equivalent

/-- Per-thread history equivalence is reflexive. -/
theorem refl
    (operations : List (IdentifiedCompleted Value)) :
    Equivalent operations operations :=
  ⟨List.Perm.refl operations, fun _ => rfl⟩

/-- Per-thread history equivalence is symmetric. -/
theorem symm
    {left right : List (IdentifiedCompleted Value)}
    (equivalent : Equivalent left right) :
    Equivalent right left :=
  ⟨equivalent.1.symm,
    fun thread => (equivalent.2 thread).symm⟩

/-- Per-thread history equivalence is transitive. -/
theorem trans
    {first second third : List (IdentifiedCompleted Value)}
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
    (history : History Value)
    (first second : IdentifiedCompleted Value) : Prop :=
  HerlihyWing.Before
    (HistoryEvent.respond first.returned)
    (HistoryEvent.invoke second.invocation)
    history

/-- A sequential order contains every required real-time precedence edge. -/
def PreservesRealTime
    (history : History Value)
    (sequential : List (IdentifiedCompleted Value)) : Prop :=
  ∀ {first second},
    first ∈ sequential →
    second ∈ sequential →
    RealTimePrecedes history first second →
    HerlihyWing.Before first second sequential

/-- Erase operation identities and client threads for the sequential spec. -/
def eraseIdentities
    (operations : List (IdentifiedCompleted Value)) :
    List (QueueSpec.CompletedOperation Value) :=
  operations.map IdentifiedCompleted.erase

@[simp] theorem eraseIdentities_nil :
    eraseIdentities ([] : List (IdentifiedCompleted Value)) = [] :=
  rfl

@[simp] theorem eraseIdentities_cons
    (entry : IdentifiedCompleted Value)
    (rest : List (IdentifiedCompleted Value)) :
    eraseIdentities (entry :: rest) =
      entry.erase :: eraseIdentities rest :=
  rfl

/-- Legality of an identity-preserving sequential queue history. -/
def SequentiallyLegal
    (initial : List Value)
    (operations : List (IdentifiedCompleted Value))
    (final : List Value) : Prop :=
  QueueSpec.Legal initial (eraseIdentities operations) final

/-- The empty identified history is legal and leaves the queue unchanged. -/
theorem sequentiallyLegal_nil (queue : List Value) :
    SequentiallyLegal queue [] queue :=
  QueueSpec.Legal.nil queue

/-- Prepend one specification-valid operation to a legal identified history. -/
theorem sequentiallyLegal_cons
    {before after final : List Value}
    (entry : IdentifiedCompleted Value)
    (rest : List (IdentifiedCompleted Value))
    (headIsLegal :
      QueueSpec.step before entry.operation =
        (entry.response, after))
    (tailIsLegal :
      SequentiallyLegal after rest final) :
    SequentiallyLegal before (entry :: rest) final :=
  QueueSpec.Legal.cons
    entry.erase
    (eraseIdentities rest)
    headIsLegal
    tailIsLegal

/--
Finite data witnessing Herlihy--Wing linearizability for the queue
specification.

`completionOperations` performs the standard completion/removal choice.
`sequentialOperations` is an equivalent per-thread sequential history whose
identity-erased form is FIFO-legal and whose order preserves client real time.
-/
structure Linearization
    (initial : List Value)
    (history : History Value) where
  wellFormed :
    WellFormed history
  completionOperations :
    List (IdentifiedCompleted Value)
  completion :
    Completion history completionOperations
  sequentialOperations :
    List (IdentifiedCompleted Value)
  equivalent :
    Equivalent completionOperations sequentialOperations
  preservesRealTime :
    PreservesRealTime history sequentialOperations
  final :
    List Value
  legal :
    SequentiallyLegal initial sequentialOperations final

/-- Existence of a finite Herlihy--Wing linearization witness. -/
def Linearizable
    (initial : List Value)
    (history : History Value) : Prop :=
  Nonempty (Linearization initial history)

namespace Linearization

/-- Expose the ordinary identity-erased sequential legality witness. -/
theorem legal_erased
    {initial : List Value}
    {history : History Value}
    (linearization : Linearization initial history) :
    QueueSpec.Legal initial
      (eraseIdentities linearization.sequentialOperations)
      linearization.final :=
  linearization.legal

/-- The selected completion and sequential witness contain the same entries. -/
theorem completion_perm_sequential
    {initial : List Value}
    {history : History Value}
    (linearization : Linearization initial history) :
    linearization.completionOperations.Perm
      linearization.sequentialOperations :=
  linearization.equivalent.1

/-- The sequential witness preserves each client's completed-operation order. -/
theorem thread_projection
    {initial : List Value}
    {history : History Value}
    (linearization : Linearization initial history)
    (thread : Source.ThreadId) :
    operationsForThread thread
        linearization.completionOperations =
      operationsForThread thread
        linearization.sequentialOperations :=
  linearization.equivalent.2 thread

end Linearization

namespace Linearizable

/-- A linearizable history has a legal identity-erased sequential witness. -/
theorem exists_legal_erased
    {initial : List Value}
    {history : History Value}
    (linearizable : Linearizable initial history) :
    ∃ operations final,
      QueueSpec.Legal initial
        (eraseIdentities operations) final := by
  rcases linearizable with ⟨linearization⟩
  exact ⟨linearization.sequentialOperations,
    linearization.final, linearization.legal⟩

end Linearizable

end WeakMemory.MSQueue.HW
