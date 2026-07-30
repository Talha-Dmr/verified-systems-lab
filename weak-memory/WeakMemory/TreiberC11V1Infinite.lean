import WeakMemory.InfiniteExecution
import WeakMemory.TreiberC11V1

namespace WeakMemory.TreiberC11V1

/-!
# Infinite source executions

This module extends the finite `TreiberC11V1` source semantics with an
explicit infinite global state trajectory.  It deliberately adds no RC11
reads-from or modification-order data: those belong to a separate infinite
memory-model layer.

Every finite prefix of an `InfiniteExecution` is proved to be an existing
`GlobalRun`.  This is the integration boundary through which later liveness
results can reuse the finite safety development.
-/

/-- The source-control state of every client thread at one instant. -/
abbrev GlobalState (α : Type) :=
  ThreadId → LocalState α

/--
One globally interleaved source step.

The event owner takes exactly one existing `LocalStep`; every other thread
retains its local state.
-/
structure GlobalStep
    (before : GlobalState α)
    (event : TraceEvent α)
    (after : GlobalState α) : Prop where
  owner :
    LocalStep event.thread
      (before event.thread) event (after event.thread)
  frame :
    ∀ thread,
      thread ≠ event.thread →
        after thread = before thread

/--
An infinite execution of a fixed finite family of source threads.

`state time` is the global state before `event time`; the event leads to
`state (time + 1)`.  States are total on natural thread identifiers so they
match the existing source semantics, while `ownerBound` ensures that only the
declared finite family can emit events.
-/
structure InfiniteExecution (α : Type) (threadCount : Nat) where
  state : Nat → GlobalState α
  event : Nat → TraceEvent α
  initial :
    ∀ thread,
      state 0 thread = .idle
  ownerBound :
    ∀ time,
      (event time).thread < threadCount
  valid :
    ∀ time,
      GlobalStep
        (state time)
        (event time)
        (state (time + 1))

namespace InfiniteExecution

/-- Forget the finite thread bound and expose the generic infinite-run view. -/
def toInfiniteRun
    (execution : InfiniteExecution α threadCount) :
    Liveness.InfiniteRun (GlobalStep (α := α)) where
  state :=
    execution.state
  action :=
    execution.event
  valid :=
    execution.valid

/-- The first `length` source events, in their global chronological order. -/
def tracePrefix
    (execution : InfiniteExecution α threadCount)
    (length : Nat) :
    List (TraceEvent α) :=
  (List.range length).map execution.event

@[simp] theorem tracePrefix_zero
    (execution : InfiniteExecution α threadCount) :
    execution.tracePrefix 0 = [] :=
  rfl

/-- Extending a finite prefix by one position appends exactly that event. -/
theorem tracePrefix_succ
    (execution : InfiniteExecution α threadCount)
    (length : Nat) :
    execution.tracePrefix (length + 1) =
      execution.tracePrefix length ++ [execution.event length] := by
  simp [tracePrefix, List.range_succ]

end InfiniteExecution

namespace Run

/-- Append one local source step to an already generated finite local run. -/
theorem snoc
    {thread : ThreadId}
    {initial middle final : LocalState α}
    {events : List (TraceEvent α)}
    {event : TraceEvent α}
    (run : Run thread initial events middle)
    (last : LocalStep thread middle event final) :
    Run thread initial (events ++ [event]) final := by
  induction run with
  | nil state =>
      exact .cons event [] last (.nil final)
  | @cons initial next middle first rest head tail
      inductionHypothesis =>
      exact
        .cons first (rest ++ [event]) head
          (inductionHypothesis last)

end Run

/-- Thread projection distributes over concatenation of global traces. -/
theorem eventsForThread_append
    (thread : ThreadId)
    (first second : List (TraceEvent α)) :
    eventsForThread thread (first ++ second) =
      eventsForThread thread first ++
        eventsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, eventsForThread]
      split
      · simp [inductionHypothesis]
      · exact inductionHypothesis

namespace InfiniteExecution

/--
The projection of every finite global prefix is the corresponding existing
per-thread `Run`, ending in the explicitly recorded state at that time.
-/
theorem prefix_run
    (execution : InfiniteExecution α threadCount)
    (thread : ThreadId)
    (length : Nat) :
    Run thread .idle
      (eventsForThread thread (execution.tracePrefix length))
      (execution.state length thread) := by
  induction length with
  | zero =>
      change
        Run thread (.idle : LocalState α) []
          (execution.state 0 thread)
      rw [execution.initial thread]
      exact emptyRun thread
  | succ length inductionHypothesis =>
      rw [tracePrefix_succ, eventsForThread_append]
      by_cases owned :
          (execution.event length).thread = thread
      · have localStep :
          LocalStep thread
            (execution.state length thread)
            (execution.event length)
            (execution.state (length + 1) thread) := by
          simpa [owned] using
            (execution.valid length).owner
        simpa [eventsForThread, owned] using
          inductionHypothesis.snoc localStep
      · have unchanged :
          execution.state (length + 1) thread =
            execution.state length thread :=
          (execution.valid length).frame thread
            (Ne.symm owned)
        rw [unchanged]
        simpa [eventsForThread, owned] using
          inductionHypothesis

/--
Every finite prefix of an infinite source execution is admitted by the
existing finite global source semantics.
-/
theorem prefix_globalRun
    (execution : InfiniteExecution α threadCount)
    (length : Nat) :
    GlobalRun (execution.tracePrefix length) := by
  intro thread
  exact
    ⟨execution.state length thread,
      execution.prefix_run thread length⟩

end InfiniteExecution

end WeakMemory.TreiberC11V1
