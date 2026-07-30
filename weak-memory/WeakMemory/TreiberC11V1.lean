import WeakMemory

namespace WeakMemory.TreiberC11V1

/-!
# Independent source semantics for the pinned Treiber program

This file describes only the source control flow of `c/treiber.c`.  It does
not import the Treiber validator, execution graph, or supported-model types.
Atomic results and non-atomic field-read values are recorded but deliberately
not justified here; RF/MO and C11 definedness belong to the next layer.
-/

abbrev ThreadId := Nat
abbrev OperationId := Nat
abbrev NodeId := Nat
abbrev EventId := Nat

/-- Pointer values in the source-specific C fragment. -/
inductive Ptr where
  | null
  | node (id : NodeId)
  deriving Repr, DecidableEq

/--
One source atomic action.

Compare-exchanges retain the old local `expected`, the value actually
observed, and the success bit.  On success the small-step rules force those
values to agree.  On weak failure they may also agree, representing a
spurious failure.
-/
inductive AtomicAction (α : Type) where
  | pushLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | pushCas
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (value : α)
      (expected observed : Ptr)
      (succeeded : Bool)
  | popLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | popCas
      (thread : ThreadId)
      (operation : OperationId)
      (expected : NodeId)
      (value : α)
      (next observed : Ptr)
      (succeeded : Bool)
  | isEmptyLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  deriving Repr, DecidableEq

namespace AtomicAction

def thread : AtomicAction α → ThreadId
  | .pushLoad thread _ _
  | .pushCas thread _ _ _ _ _ _
  | .popLoad thread _ _
  | .popCas thread _ _ _ _ _ _
  | .isEmptyLoad thread _ _ => thread

def operation : AtomicAction α → OperationId
  | .pushLoad _ operation _
  | .pushCas _ operation _ _ _ _ _
  | .popLoad _ operation _
  | .popCas _ operation _ _ _ _ _
  | .isEmptyLoad _ operation _ => operation

def readValue : AtomicAction α → Ptr
  | .pushLoad _ _ observed
  | .pushCas _ _ _ _ _ observed _
  | .popLoad _ _ observed
  | .popCas _ _ _ _ _ observed _
  | .isEmptyLoad _ _ observed => observed

def writtenValue : AtomicAction α → Option Ptr
  | .pushCas _ _ node _ _ _ true => some (.node node)
  | .popCas _ _ _ _ next _ true => some next
  | _ => none

/-- Orders are exactly those in the pinned `treiber.c`. -/
def order : AtomicAction α → MemoryOrder
  | .pushLoad .. => .relaxed
  | .pushCas _ _ _ _ _ _ true => .release
  | .pushCas _ _ _ _ _ _ false => .relaxed
  | .popLoad .. => .acquire
  | .popCas .. => .acquire
  | .isEmptyLoad .. => .acquire

def isRMW : AtomicAction α → Bool
  | .pushCas _ _ _ _ _ _ true
  | .popCas _ _ _ _ _ _ true => true
  | _ => false

end AtomicAction

/-- A numbered source atomic occurrence; identifier zero is reserved later. -/
structure AtomicOccurrence (α : Type) where
  id : EventId
  action : AtomicAction α
  deriving Repr, DecidableEq

/-- Source trace events, including calls, field accesses, atomics, and returns. -/
inductive TraceEvent (α : Type) where
  | invokePush
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (value : α)
  | invokePop
      (thread : ThreadId)
      (operation : OperationId)
  | invokeIsEmpty
      (thread : ThreadId)
      (operation : OperationId)
  | writeNext
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (next : Ptr)
  | readNext
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (next : Ptr)
  | atomic
      (occurrence : AtomicOccurrence α)
  | respondPush
      (thread : ThreadId)
      (operation : OperationId)
  | respondPop
      (thread : ThreadId)
      (operation : OperationId)
      (result : Ptr)
  | respondIsEmpty
      (thread : ThreadId)
      (operation : OperationId)
      (result : Bool)
  deriving Repr, DecidableEq

namespace TraceEvent

def thread : TraceEvent α → ThreadId
  | .invokePush thread ..
  | .invokePop thread _
  | .invokeIsEmpty thread _
  | .writeNext thread ..
  | .readNext thread ..
  | .respondPush thread _
  | .respondPop thread _ _
  | .respondIsEmpty thread _ _ => thread
  | .atomic occurrence => occurrence.action.thread

def operation : TraceEvent α → OperationId
  | .invokePush _ operation ..
  | .invokePop _ operation
  | .invokeIsEmpty _ operation
  | .writeNext _ operation ..
  | .readNext _ operation ..
  | .respondPush _ operation
  | .respondPop _ operation _
  | .respondIsEmpty _ operation _ => operation
  | .atomic occurrence => occurrence.action.operation

end TraceEvent

/-- Local variables and source program counter of one client thread. -/
inductive LocalState (α : Type) where
  | idle
  | pushLoading (operation : OperationId) (node : NodeId) (value : α)
  | pushWriting
      (operation : OperationId) (node : NodeId) (value : α) (expected : Ptr)
  | pushing
      (operation : OperationId) (node : NodeId) (value : α) (expected : Ptr)
  | popLoading (operation : OperationId)
  | popReading (operation : OperationId) (observed : NodeId)
  | popping
      (operation : OperationId) (expected : NodeId) (value : α) (next : Ptr)
  | checkingEmpty (operation : OperationId)
  | returningPush (operation : OperationId) (value : α)
  | returningPop (operation : OperationId) (result : Ptr)
  | returningIsEmpty (operation : OperationId) (result : Bool)
  deriving Repr, DecidableEq

/-- One exact source-control step for a fixed thread. -/
inductive LocalStep (thread : ThreadId) :
    LocalState α → TraceEvent α → LocalState α → Prop where
  | beginPush (operation node) (value : α) :
      LocalStep thread .idle
        (.invokePush thread operation node value)
        (.pushLoading operation node value)
  | pushLoad (id operation node) (value : α) (observed : Ptr) :
      LocalStep thread
        (.pushLoading operation node value)
        (.atomic ⟨id, .pushLoad thread operation observed⟩)
        (.pushWriting operation node value observed)
  | writeNext (operation node) (value : α) (expected : Ptr) :
      LocalStep thread
        (.pushWriting operation node value expected)
        (.writeNext thread operation node expected)
        (.pushing operation node value expected)
  | pushSuccess (id operation node) (value : α) (expected : Ptr) :
      LocalStep thread
        (.pushing operation node value expected)
        (.atomic
          ⟨id, .pushCas thread operation node value
            expected expected true⟩)
        (.returningPush operation value)
  | pushFailure
      (id operation node) (value : α) (expected actual : Ptr) :
      LocalStep thread
        (.pushing operation node value expected)
        (.atomic
          ⟨id, .pushCas thread operation node value
            expected actual false⟩)
        (.pushWriting operation node value actual)
  | finishPush (operation) (value : α) :
      LocalStep thread
        (.returningPush operation value)
        (.respondPush thread operation)
        .idle
  | beginPop (operation) :
      LocalStep thread .idle
        (.invokePop thread operation)
        (.popLoading operation)
  | popLoadEmpty (id operation) :
      LocalStep thread
        (.popLoading operation)
        (.atomic ⟨id, .popLoad thread operation .null⟩)
        (.returningPop operation .null)
  | popLoadNode (id operation observed) :
      LocalStep thread
        (.popLoading operation)
        (.atomic ⟨id, .popLoad thread operation (.node observed)⟩)
        (.popReading operation observed)
  | readNext (operation observed) (value : α) (next : Ptr) :
      LocalStep thread
        (.popReading operation observed)
        (.readNext thread operation observed next)
        (.popping operation observed value next)
  | popSuccess (id operation expected) (value : α) (next : Ptr) :
      LocalStep thread
        (.popping operation expected value next)
        (.atomic
          ⟨id, .popCas thread operation expected value next
            (.node expected) true⟩)
        (.returningPop operation (.node expected))
  | popFailureRetry
      (id operation expected actual) (value : α) (next : Ptr) :
      LocalStep thread
        (.popping operation expected value next)
        (.atomic
          ⟨id, .popCas thread operation expected value next
            (.node actual) false⟩)
        (.popReading operation actual)
  | popFailureEmpty
      (id operation expected) (value : α) (next : Ptr) :
      LocalStep thread
        (.popping operation expected value next)
        (.atomic
          ⟨id, .popCas thread operation expected value next .null false⟩)
        (.returningPop operation .null)
  | finishPop (operation) (result : Ptr) :
      LocalStep thread
        (.returningPop operation result)
        (.respondPop thread operation result)
        .idle
  | beginIsEmpty (operation) :
      LocalStep thread .idle
        (.invokeIsEmpty thread operation)
        (.checkingEmpty operation)
  | isEmptyLoadNull (id operation) :
      LocalStep thread
        (.checkingEmpty operation)
        (.atomic ⟨id, .isEmptyLoad thread operation .null⟩)
        (.returningIsEmpty operation true)
  | isEmptyLoadNode (id operation observed) :
      LocalStep thread
        (.checkingEmpty operation)
        (.atomic ⟨id, .isEmptyLoad thread operation (.node observed)⟩)
        (.returningIsEmpty operation false)
  | finishIsEmpty (operation) (result : Bool) :
      LocalStep thread
        (.returningIsEmpty operation result)
        (.respondIsEmpty thread operation result)
        .idle

/-- Weak push CAS permits an equal-value (spurious) failure. -/
theorem push_spuriousFailure
    (thread id operation node : Nat)
    (value : α)
    (expected : Ptr) :
    LocalStep thread
      (.pushing operation node value expected)
      (.atomic
        ⟨id, .pushCas thread operation node value
          expected expected false⟩)
      (.pushWriting operation node value expected) :=
  .pushFailure id operation node value expected expected

/-- Weak pop CAS permits an equal-value (spurious) failure. -/
theorem pop_spuriousFailure
    (thread id operation expected : Nat)
    (value : α)
    (next : Ptr) :
    LocalStep thread
      (.popping operation expected value next)
      (.atomic
        ⟨id, .popCas thread operation expected value next
          (.node expected) false⟩)
      (.popReading operation expected) :=
  .popFailureRetry id operation expected expected value next

/-- A finite per-thread source prefix; the final local state may be pending. -/
inductive Run (thread : ThreadId) :
    LocalState α → List (TraceEvent α) → LocalState α → Prop where
  | nil (state : LocalState α) :
      Run thread state [] state
  | cons
      {initial middle final : LocalState α}
      (event : TraceEvent α)
      (rest : List (TraceEvent α))
      (first : LocalStep thread initial event middle)
      (later : Run thread middle rest final) :
      Run thread initial (event :: rest) final

/-- The empty trace is a valid idle finite prefix for every thread. -/
theorem emptyRun (thread : ThreadId) :
    Run thread (.idle : LocalState α) [] .idle :=
  .nil .idle

@[simp] theorem empty_run (thread : ThreadId) :
    Run thread (.idle : LocalState α) [] .idle :=
  emptyRun thread

/-- Keep exactly one thread's source events in global-trace order. -/
def eventsForThread
    (thread : ThreadId) :
    List (TraceEvent α) → List (TraceEvent α)
  | [] =>
      []
  | event :: rest =>
      if event.thread = thread then
        event :: eventsForThread thread rest
      else
        eventsForThread thread rest

/--
A globally interleaved finite source prefix.

Each thread projection must be generated by the independent local machine.
No final idle-state requirement is imposed, so an invocation may remain
pending at the end of the finite prefix.
-/
def GlobalRun (trace : List (TraceEvent α)) : Prop :=
  ∀ thread,
    ∃ final,
      Run thread .idle
        (eventsForThread thread trace)
        final

/-- The empty global trace is a source-generated finite prefix. -/
theorem emptyGlobalRun :
    GlobalRun ([] : List (TraceEvent α)) := by
  intro thread
  exact ⟨.idle, emptyRun thread⟩

/-- A complete single-thread push prefix generated by the independent source. -/
def singlePushTrace (value : α) : List (TraceEvent α) := [
  .invokePush 0 1 1 value,
  .atomic ⟨1, .pushLoad 0 1 .null⟩,
  .writeNext 0 1 1 .null,
  .atomic
    ⟨2, .pushCas 0 1 1 value .null .null true⟩,
  .respondPush 0 1
]

/-- The independent source semantics is inhabited by a nonempty execution. -/
theorem singlePushGlobalRun (value : α) :
    GlobalRun (singlePushTrace value) := by
  intro thread
  by_cases owner : thread = 0
  · subst thread
    refine ⟨.idle, ?_⟩
    exact
      .cons _ _
        (.beginPush 1 1 value)
        (.cons _ _
          (.pushLoad 1 1 1 value .null)
          (.cons _ _
            (.writeNext 1 1 value .null)
            (.cons _ _
              (.pushSuccess 2 1 1 value .null)
              (.cons _ _ (.finishPush 1 value) (.nil .idle)))))
  · refine ⟨.idle, ?_⟩
    have projection :
        eventsForThread thread (singlePushTrace value) = [] := by
      simp [singlePushTrace, eventsForThread,
        TraceEvent.thread, AtomicAction.thread,
        Ne.symm owner]
    rw [projection]
    exact emptyRun thread

end WeakMemory.TreiberC11V1
