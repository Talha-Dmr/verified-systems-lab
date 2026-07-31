import WeakMemory.MSQueueSourceHistory

namespace WeakMemory.MSQueue.Source

/-!
# Per-thread method traces for the Michael--Scott source machine

The source program counter does not by itself determine an abstract method
state: `LocalState.enqueueReturning` retains the operation identifier but no
longer retains the enqueued value.  Consequently this module deliberately
uses the relation `MethodTrace.Relates` rather than a function from local
states to method states.  The relation carries that value as ghost data from
the successful link CAS through the enqueue response.

The resulting trace records exactly

```text
invocation ; abstract commit ; response
```

for each completed call of one thread.  Internal loads, helping steps, and
failed weak CAS attempts are silent.  This is only the per-thread control-flow
bridge; no global completion or real-time-order claim is made here.
-/

namespace MethodTrace

/-- Canonical identified enqueue result used by the method machine. -/
def enqueueEntry
    (thread : ThreadId)
    (operation : OperationId)
    (value : Value) : MSQueue.HW.IdentifiedCompleted Value where
  thread := thread
  id := operation
  operation := .enqueue value
  response := .enqueued

/-- Canonical identified dequeue result used by the method machine. -/
def dequeueEntry
    (thread : ThreadId)
    (operation : OperationId)
    (result : Option Value) : MSQueue.HW.IdentifiedCompleted Value where
  thread := thread
  id := operation
  operation := .dequeue
  response := .dequeued result

/-- Ghost state of one sequential client thread. -/
inductive State (Value : Type) where
  | idle
  | pending (invocation : MSQueue.HW.Invocation Value)
  | committed (entry : MSQueue.HW.IdentifiedCompleted Value)
  deriving Repr, DecidableEq

/-- Identity-preserving method events, including the abstract commit. -/
inductive Event (Value : Type) where
  | invoke (invocation : MSQueue.HW.Invocation Value)
  | commit (entry : MSQueue.HW.IdentifiedCompleted Value)
  | respond (returned : MSQueue.HW.Return Value)
  deriving Repr, DecidableEq

namespace Event

def thread : Event Value → ThreadId
  | .invoke invocation => invocation.thread
  | .commit entry => entry.thread
  | .respond returned => returned.thread

def operationId : Event Value → OperationId
  | .invoke invocation => invocation.id
  | .commit entry => entry.id
  | .respond returned => returned.id

/-- Erase commits and retain the client-visible endpoints. -/
def historyEvent? : Event Value → Option (MSQueue.HW.HistoryEvent Value)
  | .invoke invocation => some (.invoke invocation)
  | .commit _ => none
  | .respond returned => some (.respond returned)

/-- Retain only the identity-preserving abstract commit. -/
def completed? : Event Value → Option (MSQueue.HW.IdentifiedCompleted Value)
  | .invoke _ => none
  | .commit entry => some entry
  | .respond _ => none

end Event

/-- The three visible transitions of one sequential method machine. -/
inductive Step : State Value → Event Value → State Value → Prop where
  | invoke (invocation : MSQueue.HW.Invocation Value) :
      Step .idle (.invoke invocation) (.pending invocation)
  | commit (entry : MSQueue.HW.IdentifiedCompleted Value) :
      Step
        (.pending entry.invocation)
        (.commit entry)
        (.committed entry)
  | respond (entry : MSQueue.HW.IdentifiedCompleted Value) :
      Step
        (.committed entry)
        (.respond entry.returned)
        .idle

/-- A finite method execution; its final call may remain pending or committed. -/
inductive Execution : State Value → List (Event Value) → State Value → Prop where
  | nil (state : State Value) : Execution state [] state
  | cons
      {initial middle final : State Value}
      (event : Event Value)
      (rest : List (Event Value))
      (first : Step initial event middle)
      (later : Execution middle rest final) :
      Execution initial (event :: rest) final

/-- Constructor-level well-bracketed trace shape from any method state. -/
inductive ValidFrom : State Value → List (Event Value) → Prop where
  | nil (state : State Value) : ValidFrom state []
  | invoke
      {invocation : MSQueue.HW.Invocation Value}
      {rest : List (Event Value)} :
      ValidFrom (.pending invocation) rest →
      ValidFrom .idle (.invoke invocation :: rest)
  | commit
      {entry : MSQueue.HW.IdentifiedCompleted Value}
      {rest : List (Event Value)} :
      ValidFrom (.committed entry) rest →
      ValidFrom (.pending entry.invocation) (.commit entry :: rest)
  | respond
      {entry : MSQueue.HW.IdentifiedCompleted Value}
      {rest : List (Event Value)} :
      ValidFrom .idle rest →
      ValidFrom (.committed entry) (.respond entry.returned :: rest)

/-- Canonical well-bracketed shape for a method machine starting idle. -/
abbrev ThreadForm (events : List (Event Value)) : Prop :=
  ValidFrom .idle events

namespace Execution

theorem toValidFrom
    {initial final : State Value}
    {events : List (Event Value)}
    (execution : Execution initial events final) :
    ValidFrom initial events := by
  induction execution with
  | nil state => exact .nil state
  | cons event rest first later inductionHypothesis =>
      cases first with
      | invoke => exact .invoke inductionHypothesis
      | commit => exact .commit inductionHypothesis
      | respond => exact .respond inductionHypothesis

theorem toThreadForm
    {events : List (Event Value)}
    {final : State Value}
    (execution : Execution .idle events final) :
    ThreadForm events :=
  execution.toValidFrom

end Execution

/-- Project one source occurrence to its visible method event, if any. -/
def sourceEvent? (event : TraceEvent Value) : Option (Event Value) :=
  match event with
  | .invokeEnqueue thread operation _ value =>
      some (.invoke (enqueueEntry thread operation value).invocation)
  | .invokeDequeue thread operation =>
      some (.invoke (dequeueEntry (Value := Value) thread operation none).invocation)
  | .atomic occurrence =>
      occurrence.commitRecord?.map fun record =>
        .commit (Source.identifiedCommit record)
  | .respondEnqueue thread operation =>
      some (.respond {
        thread := thread
        id := operation
        response := .enqueued
      })
  | .respondDequeue thread operation result =>
      some (.respond (dequeueEntry thread operation result).returned)
  | .initializePayload .. | .readPayload .. => none

/-- Project a source-occurrence list to identity-preserving method events. -/
def eventsFrom (trace : List (TraceEvent Value)) : List (Event Value) :=
  trace.filterMap sourceEvent?

/-- Erase commits from a method trace to obtain its client history. -/
def history (events : List (Event Value)) : MSQueue.HW.History Value :=
  events.filterMap Event.historyEvent?

/-- Retain the identified completed operations selected by commit events. -/
def completedOperations
    (events : List (Event Value)) :
    List (MSQueue.HW.IdentifiedCompleted Value) :=
  events.filterMap Event.completed?

/-- Keep exactly one thread's method events, preserving their order. -/
def eventsForThread
    (thread : ThreadId) : List (Event Value) → List (Event Value)
  | [] => []
  | event :: rest =>
      if event.thread = thread then
        event :: eventsForThread thread rest
      else
        eventsForThread thread rest

/-!
`Relates` is the essential ghost boundary.  In the enqueue-returning case the
value is an index of the constructor, not data recovered from `LocalState`.
Thus a successful link can choose the value once and silent finish-tail steps
carry the same abstract entry through the value-erasing source state.
-/

/-- Relational refinement from source control state to ghost method state. -/
inductive Relates (thread : ThreadId) :
    LocalState Value → State Value → Prop where
  | idle : Relates thread .idle .idle
  | enqueueWritingPayload (operation node) (value : Value) :
      Relates thread
        (.enqueueWritingPayload operation node value)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueInitializingNext (operation node) (value : Value) :
      Relates thread
        (.enqueueInitializingNext operation node value)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueLoadingTail (operation node) (value : Value) :
      Relates thread
        (.enqueueLoadingTail operation node value)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueLoadingNext (operation node) (value : Value) (tail : NodeId) :
      Relates thread
        (.enqueueLoadingNext operation node value tail)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueValidatingTail
      (operation node) (value : Value) (tail : NodeId) (next : Ptr) :
      Relates thread
        (.enqueueValidatingTail operation node value tail next)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueLinking (operation node) (value : Value) (tail : NodeId) :
      Relates thread
        (.enqueueLinking operation node value tail)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueHelpingTail
      (operation node) (value : Value) (expected desired : NodeId) :
      Relates thread
        (.enqueueHelpingTail operation node value expected desired)
        (.pending (enqueueEntry thread operation value).invocation)
  | enqueueFinishingTail
      (operation node) (value : Value) (expected : NodeId) :
      Relates thread
        (.enqueueFinishingTail operation node value expected)
        (.committed (enqueueEntry thread operation value))
  | enqueueReturning (operation : OperationId) (value : Value) :
      Relates thread
        (.enqueueReturning operation)
        (.committed (enqueueEntry thread operation value))
  | dequeueLoadingHead (operation : OperationId) :
      Relates thread
        (.dequeueLoadingHead operation)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueLoadingTail (operation : OperationId) (head : NodeId) :
      Relates thread
        (.dequeueLoadingTail operation head)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueLoadingNext (operation : OperationId) (head tail : NodeId) :
      Relates thread
        (.dequeueLoadingNext operation head tail)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueValidatingHead
      (operation : OperationId) (head tail nextRead : NodeId) (next : Ptr) :
      Relates thread
        (.dequeueValidatingHead operation head tail nextRead next)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueHelpingTail
      (operation : OperationId) (expected desired : NodeId) :
      Relates thread
        (.dequeueHelpingTail operation expected desired)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueReadingPayload
      (operation : OperationId) (head next : NodeId) :
      Relates thread
        (.dequeueReadingPayload operation head next)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueSwingingHead
      (operation : OperationId) (head next : NodeId) (value : Value) :
      Relates thread
        (.dequeueSwingingHead operation head next value)
        (.pending (dequeueEntry (Value := Value) thread operation none).invocation)
  | dequeueReturning (operation : OperationId) (result : Option Value) :
      Relates thread
        (.dequeueReturning operation result)
        (.committed (dequeueEntry thread operation result))

/-- Every projected method event retains its source occurrence's thread. -/
theorem sourceEvent?_thread
    {event : TraceEvent Value}
    {methodEvent : Event Value}
    (projects : sourceEvent? event = some methodEvent) :
    methodEvent.thread = event.thread := by
  cases event with
  | invokeEnqueue =>
      simpa [sourceEvent?, Event.thread, TraceEvent.thread, enqueueEntry,
        MSQueue.HW.IdentifiedCompleted.invocation] using
        (congrArg (Option.map Event.thread) projects).symm
  | initializePayload => simp [sourceEvent?] at projects
  | invokeDequeue =>
      simpa [sourceEvent?, Event.thread, TraceEvent.thread, dequeueEntry,
        MSQueue.HW.IdentifiedCompleted.invocation] using
        (congrArg (Option.map Event.thread) projects).symm
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded <;>
            simp_all [sourceEvent?, AtomicOccurrence.commitRecord?,
              Event.thread, TraceEvent.thread, Source.identifiedCommit]
          subst methodEvent
          rfl
      | dequeueHeadCAS thread operation expected desired value observed succeeded =>
          cases succeeded <;>
            simp_all [sourceEvent?, AtomicOccurrence.commitRecord?,
              Event.thread, TraceEvent.thread, Source.identifiedCommit]
          subst methodEvent
          rfl
      | dequeueHeadValidateEmpty =>
          simp_all [sourceEvent?, AtomicOccurrence.commitRecord?,
            Event.thread, TraceEvent.thread, Source.identifiedCommit]
          subst methodEvent
          rfl
      | initializeNext | enqueueTailLoad | enqueueNextLoad
        | enqueueTailValidate | enqueueHelpTailCAS | enqueueFinishTailCAS
        | dequeueHeadLoad | dequeueTailLoad | dequeueNextLoad
        | dequeueHeadValidate | dequeueHelpTailCAS =>
          simp [sourceEvent?, AtomicOccurrence.commitRecord?] at projects
  | readPayload => simp [sourceEvent?] at projects
  | respondEnqueue =>
      simpa [sourceEvent?, Event.thread, TraceEvent.thread] using
        (congrArg (Option.map Event.thread) projects).symm
  | respondDequeue =>
      simpa [sourceEvent?, Event.thread, TraceEvent.thread, dequeueEntry,
        MSQueue.HW.IdentifiedCompleted.returned] using
        (congrArg (Option.map Event.thread) projects).symm

/-- Method-event projection commutes with source per-thread projection. -/
theorem eventsForThread_eventsFrom
    (thread : ThreadId)
    (trace : List (TraceEvent Value)) :
    eventsForThread thread (eventsFrom trace) =
      eventsFrom (threadTrace trace thread) := by
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      by_cases sameThread : event.thread = thread
      · cases projects : sourceEvent? event with
        | none =>
            simp [eventsFrom, eventsForThread, threadTrace, projects,
              sameThread]
            exact inductionHypothesis
        | some methodEvent =>
            have projectedThread : methodEvent.thread = thread := by
              rw [sourceEvent?_thread projects, sameThread]
            simp [eventsFrom, eventsForThread, threadTrace, projects,
              sameThread, projectedThread]
            exact inductionHypothesis
      · cases projects : sourceEvent? event with
        | none =>
            simp [eventsFrom, eventsForThread, threadTrace, projects,
              sameThread]
            exact inductionHypothesis
        | some methodEvent =>
            have projectedThread : methodEvent.thread ≠ thread := by
              rw [sourceEvent?_thread projects]
              exact sameThread
            simp [eventsFrom, eventsForThread, threadTrace, projects,
              sameThread, projectedThread]
            exact inductionHypothesis

/-- Erasing a projected method event agrees with direct source-history projection. -/
theorem historyEvent?_sourceEvent?
    (event : TraceEvent Value) :
    (sourceEvent? event).bind Event.historyEvent? =
      Source.sourceHistoryEvent? event := by
  cases event with
  | invokeEnqueue => rfl
  | initializePayload => rfl
  | invokeDequeue => rfl
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action <;>
        simp [sourceEvent?, AtomicOccurrence.commitRecord?,
          Event.historyEvent?, Source.sourceHistoryEvent?]
  | readPayload => rfl
  | respondEnqueue => rfl
  | respondDequeue => rfl

/-- The method trace's client projection is exactly the direct source history. -/
theorem history_eventsFrom (trace : List (TraceEvent Value)) :
    history (eventsFrom trace) = Source.sourceHistory trace := by
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases projects : sourceEvent? event with
      | none =>
          have visibleNone : Source.sourceHistoryEvent? event = none := by
            simpa [projects] using (historyEvent?_sourceEvent? event).symm
          simp [eventsFrom, history, projects, Source.sourceHistory,
            visibleNone]
          exact inductionHypothesis
      | some methodEvent =>
          cases visible : Event.historyEvent? methodEvent with
          | none =>
              have sourceNone : Source.sourceHistoryEvent? event = none := by
                simpa [projects, visible] using
                  (historyEvent?_sourceEvent? event).symm
              simp [eventsFrom, history, projects, visible,
                Source.sourceHistory, sourceNone]
              exact inductionHypothesis
          | some historyEvent =>
              have sourceSome :
                  Source.sourceHistoryEvent? event = some historyEvent := by
                simpa [projects, visible] using
                  (historyEvent?_sourceEvent? event).symm
              simp [eventsFrom, history, projects, visible,
                Source.sourceHistory, sourceSome]
              exact inductionHypothesis

/-- Commit extraction from one projected event agrees with the source record. -/
theorem completed?_sourceEvent?
    (event : TraceEvent Value) :
    (sourceEvent? event).bind Event.completed? =
      event.commitRecord?.map Source.identifiedCommit := by
  cases event with
  | invokeEnqueue => rfl
  | initializePayload => rfl
  | invokeDequeue => rfl
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | enqueueLinkCAS thread operation tail node value observed succeeded =>
          cases succeeded <;>
            simp [sourceEvent?, AtomicOccurrence.commitRecord?,
              TraceEvent.commitRecord?, Event.completed?]
      | dequeueHeadCAS thread operation expected desired value observed succeeded =>
          cases succeeded <;>
            simp [sourceEvent?, AtomicOccurrence.commitRecord?,
              TraceEvent.commitRecord?, Event.completed?]
      | dequeueHeadValidateEmpty =>
          simp [sourceEvent?, AtomicOccurrence.commitRecord?,
            TraceEvent.commitRecord?, Event.completed?]
      | initializeNext | enqueueTailLoad | enqueueNextLoad
        | enqueueTailValidate | enqueueHelpTailCAS | enqueueFinishTailCAS
        | dequeueHeadLoad | dequeueTailLoad | dequeueNextLoad
        | dequeueHeadValidate | dequeueHelpTailCAS =>
          simp [sourceEvent?, AtomicOccurrence.commitRecord?,
            TraceEvent.commitRecord?, Event.completed?]
  | readPayload => rfl
  | respondEnqueue => rfl
  | respondDequeue => rfl

/-- Commit events select exactly the identified source commit records. -/
theorem completedOperations_eventsFrom
    (trace : List (TraceEvent Value)) :
    completedOperations (eventsFrom trace) =
      Source.sourceCompletedOperations trace := by
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases projects : sourceEvent? event with
      | none =>
          have commitNone :
              event.commitRecord?.map Source.identifiedCommit = none := by
            simpa [projects] using (completed?_sourceEvent? event).symm
          cases record : event.commitRecord? <;>
            simp_all [eventsFrom, completedOperations,
              Source.sourceCompletedOperations]
      | some methodEvent =>
          cases selected : Event.completed? methodEvent with
          | none =>
              have commitNone :
                  event.commitRecord?.map Source.identifiedCommit = none := by
                simpa [projects, selected] using
                  (completed?_sourceEvent? event).symm
              cases record : event.commitRecord? <;>
                simp_all [eventsFrom, completedOperations,
                  Source.sourceCompletedOperations]
          | some entry =>
              have commitSome :
                  event.commitRecord?.map Source.identifiedCommit = some entry := by
                simpa [projects, selected] using
                  (completed?_sourceEvent? event).symm
              cases record : event.commitRecord? <;>
                simp_all [eventsFrom, completedOperations,
                  Source.sourceCompletedOperations]

/-- Thread projection commutes with erasing commit events. -/
theorem history_eventsForThread
    (thread : ThreadId)
    (events : List (Event Value)) :
    history (eventsForThread thread events) =
      MSQueue.HW.eventsForThread thread (history events) := by
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases event with
      | invoke invocation =>
          by_cases sameThread : invocation.thread = thread
          · simpa [eventsForThread, Event.thread, sameThread, history,
              Event.historyEvent?, MSQueue.HW.eventsForThread,
              MSQueue.HW.HistoryEvent.thread] using
              congrArg (List.cons (.invoke invocation)) inductionHypothesis
          · simpa [eventsForThread, Event.thread, sameThread, history,
              Event.historyEvent?, MSQueue.HW.eventsForThread,
              MSQueue.HW.HistoryEvent.thread] using inductionHypothesis
      | commit entry =>
          by_cases sameThread : entry.thread = thread <;>
            simpa [eventsForThread, Event.thread, sameThread, history,
              Event.historyEvent?] using inductionHypothesis
      | respond returned =>
          by_cases sameThread : returned.thread = thread
          · simpa [eventsForThread, Event.thread, sameThread, history,
              Event.historyEvent?, MSQueue.HW.eventsForThread,
              MSQueue.HW.HistoryEvent.thread] using
              congrArg (List.cons (.respond returned)) inductionHypothesis
          · simpa [eventsForThread, Event.thread, sameThread, history,
              Event.historyEvent?, MSQueue.HW.eventsForThread,
              MSQueue.HW.HistoryEvent.thread] using inductionHypothesis

end MethodTrace

namespace LocalStep

/--
Every source step is one exact method transition or a silent transition that
preserves the related ghost state.  The result remains relational because an
enqueue-returning source state does not determine its committed value.
-/
theorem refinesMethod
    {thread : ThreadId}
    {before after : LocalState Value}
    {event : TraceEvent Value}
    (step : LocalStep thread before event after)
    {methodBefore : MethodTrace.State Value}
    (related : MethodTrace.Relates thread before methodBefore) :
    ∃ methodAfter,
      MethodTrace.Relates thread after methodAfter ∧
        match MethodTrace.sourceEvent? event with
        | none => methodAfter = methodBefore
        | some methodEvent =>
            MethodTrace.Step methodBefore methodEvent methodAfter := by
  cases step with
  | beginEnqueue =>
      cases related
      exact ⟨_, .enqueueWritingPayload _ _ _, .invoke _⟩
  | initializePayload =>
      cases related
      exact ⟨_, .enqueueInitializingNext _ _ _, rfl⟩
  | initializeNext =>
      cases related
      exact ⟨_, .enqueueLoadingTail _ _ _, rfl⟩
  | enqueueTailLoad =>
      cases related
      exact ⟨_, .enqueueLoadingNext _ _ _ _, rfl⟩
  | enqueueNextLoad =>
      cases related
      exact ⟨_, .enqueueValidatingTail _ _ _ _ _, rfl⟩
  | enqueueTailChanged =>
      cases related
      exact ⟨_, .enqueueLoadingTail _ _ _, rfl⟩
  | enqueueTailStableNull =>
      cases related
      exact ⟨_, .enqueueLinking _ _ _ _, rfl⟩
  | enqueueTailStableNode =>
      cases related
      exact ⟨_, .enqueueHelpingTail _ _ _ _ _, rfl⟩
  | enqueueLinkSuccess =>
      cases related
      exact ⟨_, .enqueueFinishingTail _ _ _ _, .commit _⟩
  | enqueueLinkFailure =>
      cases related
      exact ⟨_, .enqueueLoadingTail _ _ _, rfl⟩
  | enqueueHelpTailSuccess =>
      cases related
      exact ⟨_, .enqueueLoadingTail _ _ _, rfl⟩
  | enqueueHelpTailFailure =>
      cases related
      exact ⟨_, .enqueueLoadingTail _ _ _, rfl⟩
  | enqueueFinishTailSuccess =>
      cases related
      exact ⟨_, .enqueueReturning _ _, rfl⟩
  | enqueueFinishTailFailure =>
      cases related
      exact ⟨_, .enqueueReturning _ _, rfl⟩
  | finishEnqueue =>
      cases related
      exact ⟨_, .idle, .respond _⟩
  | beginDequeue =>
      cases related
      exact ⟨_, .dequeueLoadingHead _, .invoke _⟩
  | dequeueHeadLoad =>
      cases related
      exact ⟨_, .dequeueLoadingTail _ _, rfl⟩
  | dequeueTailLoad =>
      cases related
      exact ⟨_, .dequeueLoadingNext _ _ _, rfl⟩
  | dequeueNextLoad =>
      cases related
      exact ⟨_, .dequeueValidatingHead _ _ _ _ _, rfl⟩
  | dequeueHeadChanged =>
      cases related
      exact ⟨_, .dequeueLoadingHead _, rfl⟩
  | dequeueEmpty =>
      cases related
      exact ⟨_, .dequeueReturning _ _, .commit _⟩
  | dequeueNeedsHelp =>
      cases related
      exact ⟨_, .dequeueHelpingTail _ _ _, rfl⟩
  | dequeueNonempty =>
      cases related
      exact ⟨_, .dequeueReadingPayload _ _ _, rfl⟩
  | dequeueHelpTailSuccess =>
      cases related
      exact ⟨_, .dequeueLoadingHead _, rfl⟩
  | dequeueHelpTailFailure =>
      cases related
      exact ⟨_, .dequeueLoadingHead _, rfl⟩
  | readPayload =>
      cases related
      exact ⟨_, .dequeueSwingingHead _ _ _ _, rfl⟩
  | dequeueHeadSuccess id operation head next value =>
      cases related
      refine ⟨_, .dequeueReturning _ _, ?_⟩
      simpa [MethodTrace.sourceEvent?, AtomicOccurrence.commitRecord?,
        Source.identifiedCommit, MethodTrace.dequeueEntry,
        MSQueue.HW.IdentifiedCompleted.invocation, Commit.completed] using
        (MethodTrace.Step.commit
          (MethodTrace.dequeueEntry thread operation (some value)))
  | dequeueHeadFailure =>
      cases related
      exact ⟨_, .dequeueLoadingHead _, rfl⟩
  | finishDequeue =>
      cases related
      exact ⟨_, .idle, .respond _⟩

end LocalStep

namespace Run

/-- Relational projection of any local source run to the method machine. -/
theorem toMethodExecution
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    {methodInitial : MethodTrace.State Value}
    (initialRelated : MethodTrace.Relates thread initial methodInitial) :
    ∃ methodFinal,
      MethodTrace.Execution methodInitial
          (MethodTrace.eventsFrom events) methodFinal ∧
        MethodTrace.Relates thread final methodFinal := by
  induction run generalizing methodInitial with
  | nil state =>
      exact ⟨methodInitial, .nil methodInitial, initialRelated⟩
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      obtain ⟨methodMiddle, middleRelated, refinement⟩ :=
        first.refinesMethod initialRelated
      obtain ⟨methodFinal, laterExecution, finalRelated⟩ :=
        inductionHypothesis middleRelated
      cases projected : MethodTrace.sourceEvent? event with
      | none =>
          rw [projected] at refinement
          subst methodMiddle
          exact ⟨methodFinal, by
            simpa [MethodTrace.eventsFrom, projected] using laterExecution,
            finalRelated⟩
      | some methodEvent =>
          rw [projected] at refinement
          exact ⟨methodFinal, by
            simpa [MethodTrace.eventsFrom, projected] using
              MethodTrace.Execution.cons methodEvent
                (MethodTrace.eventsFrom rest) refinement laterExecution,
            finalRelated⟩

/-- A local run beginning idle has a canonical well-bracketed method trace. -/
theorem toIdleMethodExecution
    {thread : ThreadId}
    {final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events final) :
    ∃ methodFinal,
      MethodTrace.Execution .idle
          (MethodTrace.eventsFrom events) methodFinal ∧
        MethodTrace.Relates thread final methodFinal :=
  run.toMethodExecution .idle

end Run

namespace SourceWellFormed

/-- Every checked global trace induces one well-bracketed method execution
for each thread projection. -/
theorem methodExecution
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    (thread : ThreadId) :
    ∃ final,
      MethodTrace.Execution .idle
        (MethodTrace.eventsForThread thread
          (MethodTrace.eventsFrom trace)) final := by
  obtain ⟨_, sourceRun⟩ := wellFormed.threadRuns thread
  obtain ⟨methodFinal, methodExecution, _⟩ :=
    sourceRun.toIdleMethodExecution
  refine ⟨methodFinal, ?_⟩
  rw [MethodTrace.eventsForThread_eventsFrom]
  exact methodExecution

end SourceWellFormed

end WeakMemory.MSQueue.Source
