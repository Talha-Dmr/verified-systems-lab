import WeakMemory.TreiberClientHistory

namespace WeakMemory.TreiberRC11

/-!
# A source method trace around each linearization point

The client history erases implementation steps, while the RC11 replay erases
operation identities.  This intermediate trace retains the three events that
both sides need:

```text
invocation ; abstract commit ; response
```

Every local Treiber step refines either one transition of this method machine
or a silent transition that preserves its state.  In particular, a finite
source prefix may stop in `committed`, after its linearization point but before
the client-visible response.
-/

namespace MethodTrace

/-- Client-method state for one fixed thread. -/
inductive State (α : Type) where
  | idle
  | pending
      (invocation : HerlihyWing.Invocation α)
  | committed
      (entry : HerlihyWing.IdentifiedCompleted α)
  deriving Repr, DecidableEq

/-- Identity-preserving method events, including the abstract commit. -/
inductive Event (α : Type) where
  | invoke
      (invocation : HerlihyWing.Invocation α)
  | commit
      (entry : HerlihyWing.IdentifiedCompleted α)
  | respond
      (returned : HerlihyWing.Return α)
  deriving Repr, DecidableEq

namespace Event

/-- The client thread shared by every method event's payload. -/
def thread : Event α → Nat
  | .invoke invocation =>
      invocation.thread
  | .commit entry =>
      entry.thread
  | .respond returned =>
      returned.thread

/-- The operation identifier shared by every method event's payload. -/
def operationId : Event α → ControlFlow.OperationId
  | .invoke invocation =>
      invocation.id
  | .commit entry =>
      entry.id
  | .respond returned =>
      returned.id

/-- Erase commit events and retain the client-visible endpoint events. -/
def historyEvent? :
    Event α → Option (HerlihyWing.HistoryEvent α)
  | .invoke invocation =>
      some (.invoke invocation)
  | .commit _ =>
      none
  | .respond returned =>
      some (.respond returned)

/-- Retain only the identity-preserving abstract commit. -/
def completed? :
    Event α → Option (HerlihyWing.IdentifiedCompleted α)
  | .invoke _ =>
      none
  | .commit entry =>
      some entry
  | .respond _ =>
      none

end Event

/-- The only three visible transitions of one sequential client thread. -/
inductive Step :
    State α → Event α → State α → Prop where
  | invoke
      (invocation : HerlihyWing.Invocation α) :
      Step .idle (.invoke invocation) (.pending invocation)
  | commit
      (entry : HerlihyWing.IdentifiedCompleted α) :
      Step
        (.pending entry.invocation)
        (.commit entry)
        (.committed entry)
  | respond
      (entry : HerlihyWing.IdentifiedCompleted α) :
      Step
        (.committed entry)
        (.respond entry.returned)
        .idle

/-- A finite method execution; the final operation may remain pending. -/
inductive Execution :
    State α → List (Event α) → State α → Prop where
  | nil (state : State α) :
      Execution state [] state
  | cons
      {initial middle final : State α}
      (event : Event α)
      (rest : List (Event α))
      (first : Step initial event middle)
      (later : Execution middle rest final) :
      Execution initial (event :: rest) final

/--
Constructor-level trace shape from any method state.

Unlike `Execution`, this predicate forgets the final state. Its indexed
constructors still enforce `invoke ; commit ; respond` for every thread and
permit a finite prefix to stop after either of the first two events.
-/
inductive ValidFrom :
    State α → List (Event α) → Prop where
  | nil
      (state : State α) :
      ValidFrom state []
  | invoke
      {invocation : HerlihyWing.Invocation α}
      {rest : List (Event α)} :
      ValidFrom (.pending invocation) rest →
      ValidFrom .idle (.invoke invocation :: rest)
  | commit
      {entry : HerlihyWing.IdentifiedCompleted α}
      {rest : List (Event α)} :
      ValidFrom (.committed entry) rest →
      ValidFrom
        (.pending entry.invocation)
        (.commit entry :: rest)
  | respond
      {entry : HerlihyWing.IdentifiedCompleted α}
      {rest : List (Event α)} :
      ValidFrom .idle rest →
      ValidFrom
        (.committed entry)
        (.respond entry.returned :: rest)

/-- Canonical trace shape for a method machine starting idle. -/
abbrev ThreadForm (events : List (Event α)) : Prop :=
  ValidFrom .idle events

namespace Execution

/-- Every method execution has the corresponding constructor-level shape. -/
theorem toValidFrom
    {initial final : State α}
    {events : List (Event α)}
    (execution : Execution initial events final) :
    ValidFrom initial events := by
  induction execution with
  | nil state =>
      exact .nil state
  | cons event rest first later inductionHypothesis =>
      cases first with
      | invoke =>
          exact .invoke inductionHypothesis
      | commit =>
          exact .commit inductionHypothesis
      | respond =>
          exact .respond inductionHypothesis

/-- Every method execution starting idle has the canonical thread form. -/
theorem toThreadForm
    {events : List (Event α)}
    {final : State α}
    (execution : Execution .idle events final) :
    ThreadForm events :=
  execution.toValidFrom

end Execution

end MethodTrace

namespace ControlFlow

/-- Erase implementation detail from a local state but retain its method. -/
def LocalState.methodState
    (thread : Nat) :
    LocalState α → MethodTrace.State α
  | .idle =>
      .idle
  | .pushLoading operation _ value
  | .pushWriting operation _ value _
  | .pushing operation _ value _ =>
      .pending {
        thread := thread
        id := operation
        operation := .push value
      }
  | .popLoading operation
  | .popReading operation _
  | .popping operation _ _ =>
      .pending {
        thread := thread
        id := operation
        operation := .pop
      }
  | .checkingEmpty operation =>
      .pending {
        thread := thread
        id := operation
        operation := .isEmpty
      }
  | .returning operation commit =>
      .committed
        (identifiedCommit thread operation commit)

/-- Keep invocations, abstract commits, and responses from one local label. -/
def localMethodEvent?
    (thread : Nat) :
    Label α → Option (MethodTrace.Event α)
  | .invokePush operation _ value =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .push value
      })
  | .invokePop operation =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .pop
      })
  | .invokeIsEmpty operation =>
      some (.invoke {
        thread := thread
        id := operation
        operation := .isEmpty
      })
  | .atomic operation action =>
      action.commit?.map fun commit =>
        .commit
          (identifiedCommit thread operation commit)
  | .respond operation response =>
      some (.respond {
        thread := thread
        id := operation
        response := response
      })
  | .writeNext .. | .readNext .. =>
      none

/-- Project a local source-label list to its method trace. -/
def localMethodTrace
    (thread : Nat) :
    List (Label α) → List (MethodTrace.Event α)
  | [] => []
  | label :: rest =>
      match localMethodEvent? thread label with
      | none =>
          localMethodTrace thread rest
      | some event =>
          event :: localMethodTrace thread rest

/-- Every projected method event retains the supplied local thread. -/
theorem localMethodEvent?_thread
    {thread : Nat}
    {label : Label α}
    {event : MethodTrace.Event α}
    (projects :
      localMethodEvent? thread label = some event) :
    event.thread = thread := by
  cases label with
  | invokePush =>
      simpa [localMethodEvent?, MethodTrace.Event.thread] using
        (congrArg
          (Option.map MethodTrace.Event.thread)
          projects).symm
  | invokePop =>
      simpa [localMethodEvent?, MethodTrace.Event.thread] using
        (congrArg
          (Option.map MethodTrace.Event.thread)
          projects).symm
  | invokeIsEmpty =>
      simpa [localMethodEvent?, MethodTrace.Event.thread] using
        (congrArg
          (Option.map MethodTrace.Event.thread)
          projects).symm
  | writeNext =>
      simp [localMethodEvent?] at projects
  | readNext =>
      simp [localMethodEvent?] at projects
  | atomic operation action =>
      cases commitShape : action.commit? with
      | none =>
          simp [localMethodEvent?, commitShape] at projects
      | some commit =>
          simp [localMethodEvent?, commitShape] at projects
          subst event
          rfl
  | respond =>
      simpa [localMethodEvent?, MethodTrace.Event.thread] using
        (congrArg
          (Option.map MethodTrace.Event.thread)
          projects).symm

/--
Every source step is either one exact method transition or a silent step that
preserves the method state.
-/
theorem LocalStep.refinesMethod
    {thread : Nat}
    {before after : LocalState α}
    {label : Label α}
    (step : LocalStep thread before label after) :
    match localMethodEvent? thread label with
    | none =>
        before.methodState thread =
          after.methodState thread
    | some event =>
        MethodTrace.Step
          (before.methodState thread)
          event
          (after.methodState thread) := by
  cases step with
  | beginPush =>
      exact MethodTrace.Step.invoke _
  | pushLoad =>
      rfl
  | writeNext =>
      rfl
  | beginPop =>
      exact MethodTrace.Step.invoke _
  | popLoadEmpty operation =>
      simpa [localMethodEvent?, LocalState.methodState,
        TreiberRA.Action.commit?, identifiedCommit,
        Treiber.Commit.completed,
        HerlihyWing.IdentifiedCompleted.invocation] using
        (MethodTrace.Step.commit
          (identifiedCommit thread operation
            (.popEmpty : Treiber.Commit α)))
  | popLoadNonempty =>
      rfl
  | readNext =>
      rfl
  | beginIsEmpty =>
      exact MethodTrace.Step.invoke _
  | isEmptyLoad operation observed =>
      cases observed with
      | none =>
          simpa [localMethodEvent?, LocalState.methodState,
            TreiberRA.Action.commit?, identifiedCommit,
            Treiber.Commit.completed,
            HerlihyWing.IdentifiedCompleted.invocation] using
            (MethodTrace.Step.commit
              (identifiedCommit thread operation
                (.isEmpty true : Treiber.Commit α)))
      | some node =>
          simpa [localMethodEvent?, LocalState.methodState,
            TreiberRA.Action.commit?, identifiedCommit,
            Treiber.Commit.completed,
            HerlihyWing.IdentifiedCompleted.invocation] using
            (MethodTrace.Step.commit
              (identifiedCommit thread operation
                (.isEmpty false : Treiber.Commit α)))
  | pushFailure =>
      rfl
  | pushSuccess operation reserved value expected =>
      simpa [localMethodEvent?, LocalState.methodState,
        TreiberRA.Action.commit?, identifiedCommit,
        Treiber.Commit.completed,
        HerlihyWing.IdentifiedCompleted.invocation] using
        (MethodTrace.Step.commit
          (identifiedCommit thread operation
            (.push value : Treiber.Commit α)))
  | popFailureRetry =>
      rfl
  | popFailureEmpty operation expected next =>
      simpa [localMethodEvent?, LocalState.methodState,
        TreiberRA.Action.commit?, identifiedCommit,
        Treiber.Commit.completed,
        HerlihyWing.IdentifiedCompleted.invocation] using
        (MethodTrace.Step.commit
          (identifiedCommit thread operation
            (.popEmpty : Treiber.Commit α)))
  | popSuccess operation expected value next =>
      simpa [localMethodEvent?, LocalState.methodState,
        TreiberRA.Action.commit?, identifiedCommit,
        Treiber.Commit.completed,
        HerlihyWing.IdentifiedCompleted.invocation] using
        (MethodTrace.Step.commit
          (identifiedCommit thread operation
            (.popValue value : Treiber.Commit α)))
  | respond =>
      exact MethodTrace.Step.respond _

/-- Project an entire locally valid source execution to the method machine. -/
theorem Execution.toMethodExecution
    {thread : Nat}
    {initial final : LocalState α}
    {labels : List (Label α)}
    (execution : Execution thread initial labels final) :
    MethodTrace.Execution
      (initial.methodState thread)
      (localMethodTrace thread labels)
      (final.methodState thread) := by
  induction execution with
  | nil state =>
      exact .nil _
  | @cons initial middle final label rest first later
      inductionHypothesis =>
      have refinement := first.refinesMethod
      cases projected : localMethodEvent? thread label with
      | none =>
          rw [projected] at refinement
          simpa [localMethodTrace, projected, refinement] using
            inductionHypothesis
      | some event =>
          rw [projected] at refinement
          simpa [localMethodTrace, projected] using
            MethodTrace.Execution.cons
              event
              (localMethodTrace thread rest)
              refinement
              inductionHypothesis

end ControlFlow

namespace MethodTrace

/-- Project global owned source labels to identity-preserving method events. -/
def eventsFrom :
    List (EventGraph.OwnedLabel α) →
      List (Event α)
  | [] =>
      []
  | owned :: rest =>
      match
        ControlFlow.localMethodEvent?
          owned.thread owned.label
      with
      | none =>
          eventsFrom rest
      | some event =>
          event :: eventsFrom rest

/-- The method trace of one global source skeleton. -/
def ofSkeleton
    (skeleton : EventGraph.Skeleton α) :
    List (Event α) :=
  eventsFrom skeleton.labels

/-- Erase commits from a method trace to obtain its client history. -/
def history
    (events : List (Event α)) :
    HerlihyWing.History α :=
  events.filterMap Event.historyEvent?

/-- Retain the completed operations represented by commit events. -/
def completedOperations
    (events : List (Event α)) :
    List (HerlihyWing.IdentifiedCompleted α) :=
  events.filterMap Event.completed?

/-- Keep exactly one client thread's method events. -/
def eventsForThread
    (thread : Nat) :
    List (Event α) → List (Event α)
  | [] =>
      []
  | event :: rest =>
      if event.thread = thread then
        event :: eventsForThread thread rest
      else
        eventsForThread thread rest

/--
Global source projection and per-thread projection commute. Thus the locally
valid control-flow execution supplies the exact method trace seen by each
client thread.
-/
theorem eventsForThread_eventsFrom
    (thread : Nat)
    (labels : List (EventGraph.OwnedLabel α)) :
    eventsForThread thread (eventsFrom labels) =
      ControlFlow.localMethodTrace thread
        (Interleaving.labelsForThread thread labels) := by
  induction labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      by_cases ownedThread : owned.thread = thread
      · subst thread
        cases projects :
            ControlFlow.localMethodEvent?
              owned.thread owned.label with
        | none =>
            simp [eventsFrom, ControlFlow.localMethodTrace,
              Interleaving.labelsForThread, projects,
              inductionHypothesis]
        | some event =>
            have eventThread :
                event.thread = owned.thread :=
              ControlFlow.localMethodEvent?_thread projects
            simp [eventsFrom, eventsForThread,
              ControlFlow.localMethodTrace,
              Interleaving.labelsForThread, projects,
              eventThread, inductionHypothesis]
      · cases projects :
            ControlFlow.localMethodEvent?
              owned.thread owned.label with
        | none =>
            simp [eventsFrom, Interleaving.labelsForThread, projects,
              ownedThread, inductionHypothesis]
        | some event =>
            have eventThread :
                event.thread = owned.thread :=
              ControlFlow.localMethodEvent?_thread projects
            have eventNotThread :
                event.thread ≠ thread := by
              rw [eventThread]
              exact ownedThread
            simp [eventsFrom, eventsForThread,
              Interleaving.labelsForThread, projects,
              ownedThread, eventNotThread,
              inductionHypothesis]

/-- The method trace's client projection is the direct source history. -/
theorem history_ofSkeleton
    (skeleton : EventGraph.Skeleton α) :
    history (ofSkeleton skeleton) =
      sourceHistory skeleton := by
  change
    history (eventsFrom skeleton.labels) =
      skeleton.labels.filterMap sourceHistoryEvent?
  induction skeleton.labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      change
        (eventsFrom rest).filterMap Event.historyEvent? =
          rest.filterMap sourceHistoryEvent?
        at inductionHypothesis
      cases label with
      | invokePush =>
          simp [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?,
            inductionHypothesis]
      | invokePop =>
          simp [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?,
            inductionHypothesis]
      | invokeIsEmpty =>
          simp [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?,
            inductionHypothesis]
      | writeNext =>
          simpa [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?] using
            inductionHypothesis
      | readNext =>
          simpa [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?] using
            inductionHypothesis
      | atomic operation action =>
          cases commits : action.commit? <;>
            simp [eventsFrom, history, Event.historyEvent?,
              ControlFlow.localMethodEvent?, sourceHistoryEvent?,
              commits, inductionHypothesis]
      | respond =>
          simp [eventsFrom, history, Event.historyEvent?,
            ControlFlow.localMethodEvent?, sourceHistoryEvent?,
            inductionHypothesis]

/-- The method trace's commit projection is the direct source commit list. -/
theorem completedOperations_ofSkeleton
    (skeleton : EventGraph.Skeleton α) :
    completedOperations (ofSkeleton skeleton) =
      sourceCommittedOperations skeleton := by
  change
    completedOperations (eventsFrom skeleton.labels) =
      skeleton.labels.filterMap sourceCommit?
  induction skeleton.labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      change
        (eventsFrom rest).filterMap Event.completed? =
          rest.filterMap sourceCommit?
        at inductionHypothesis
      cases label with
      | invokePush =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis
      | invokePop =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis
      | invokeIsEmpty =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis
      | writeNext =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis
      | readNext =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis
      | atomic operation action =>
          cases commits : action.commit? <;>
            simp [eventsFrom, completedOperations,
              Event.completed?, ControlFlow.localMethodEvent?,
              sourceCommit?, commits, inductionHypothesis]
      | respond =>
          simpa [eventsFrom, completedOperations,
            Event.completed?, ControlFlow.localMethodEvent?,
            sourceCommit?] using inductionHypothesis

end MethodTrace

namespace Interleaving.SourceSkeleton

/-- Every thread projection of a certified source skeleton is a method run. -/
theorem methodExecution
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate :
      Interleaving.SourceSkeleton initial skeleton)
    (thread : Nat) :
    ∃ final,
      MethodTrace.Execution
        .idle
        (MethodTrace.eventsForThread thread
          (MethodTrace.ofSkeleton skeleton))
        final := by
  obtain ⟨sourceFinal, sourceExecution⟩ :=
    certificate.exists_execution thread
  refine ⟨sourceFinal.methodState thread, ?_⟩
  rw [MethodTrace.ofSkeleton,
    MethodTrace.eventsForThread_eventsFrom]
  simpa [ControlFlow.LocalState.methodState] using
    sourceExecution.toMethodExecution

end Interleaving.SourceSkeleton

end WeakMemory.TreiberRC11
