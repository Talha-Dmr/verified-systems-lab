import WeakMemory.MSQueueSourceSchedule
import WeakMemory.WeakCASSiteProgress

namespace WeakMemory.MSQueue.Source

/-!
# Coherent infinite Michael--Scott source executions

This module gives the finite source/RC11 development an infinite carrier and
instantiates the reusable site-indexed weak-CAS progress interface.  Safety is
still checked prefix by prefix; global reads-from and modification-order
relations ensure that those finite witnesses are restrictions of one memory
execution rather than an unrelated family of models.

The liveness theorem is deliberately conditional.  Its two hypotheses are
the algorithm/scheduler/memory obligation selecting one stable retry site and
primitive weak-CAS justice at every logical queue site.
-/

namespace LocalState

/-- A method is active in every source state except the client idle state. -/
def Active : LocalState Value → Prop
  | .idle => False
  | _ => True

end LocalState

namespace TraceEvent

/-- Client-visible method responses in the infinite source stream. -/
def IsResponse : TraceEvent Value → Prop
  | .respondEnqueue .. | .respondDequeue .. => True
  | _ => False

/-- One successful weak CAS at an exact logical queue site. -/
def SucceededAt : TraceEvent Value → Site → Prop
  | .atomic occurrence, site =>
      occurrence.action.site = site ∧
        occurrence.action.succeededCAS = true
  | _, _ => False

/-- Every write or successful RMW that changes one site's write generation. -/
def ModifiedAt : TraceEvent Value → Site → Prop
  | .atomic occurrence, site =>
      occurrence.action.site = site ∧
        occurrence.action.access.IsWrite
  | _, _ => False

/-- A compare-equal weak-CAS attempt by one thread at one exact site. -/
def MatchingAttemptAt :
    TraceEvent Value → ThreadId → Site → Prop
  | .atomic occurrence, thread, site =>
      occurrence.action.thread = thread ∧
        occurrence.action.site = site ∧
        occurrence.action.IsMatchingCAS
  | _, _, _ => False

/-- Every successful source CAS is included in the site's modifications. -/
theorem succeededAt_isModifiedAt
    {event : TraceEvent Value}
    {site : Site}
    (succeeded : event.SucceededAt site) :
    event.ModifiedAt site := by
  cases event with
  | atomic occurrence =>
      rcases succeeded with ⟨sameSite, success⟩
      refine ⟨sameSite, ?_⟩
      have isRMW : occurrence.toRC11Atom.IsRMW := by
        exact occurrence.action.access_isRMW_iff_succeededCAS.mpr success
      exact
        (MultiLocationRC11.Atom.isNoninitialWrite_of_isRMW isRMW).1
  | invokeEnqueue | initializePayload | invokeDequeue |
      readPayload | respondEnqueue | respondDequeue =>
      exact False.elim succeeded

end TraceEvent

/-- The local source state of every client thread at one instant. -/
abbrev GlobalState (Value : Type) := ThreadId → LocalState Value

/-- One globally interleaved source step with the usual frame condition. -/
structure GlobalStep
    (before : GlobalState Value)
    (event : TraceEvent Value)
    (after : GlobalState Value) : Prop where
  owner :
    LocalStep event.thread
      (before event.thread) event (after event.thread)
  frame :
    ∀ thread,
      thread ≠ event.thread →
        after thread = before thread

/--
An infinite source execution of a fixed finite family of client threads.

`state time` is the state before `event time`; that event leads to
`state (time + 1)`.
-/
structure InfiniteExecution (Value : Type) (threadCount : Nat) where
  state : Nat → GlobalState Value
  event : Nat → TraceEvent Value
  initial : ∀ thread, state 0 thread = .idle
  ownerBound : ∀ time, (event time).thread < threadCount
  valid :
    ∀ time,
      GlobalStep (state time) (event time) (state (time + 1))

namespace InfiniteExecution

/-- Forget the finite thread bound and expose the generic infinite-run view. -/
def toInfiniteRun
    (execution : InfiniteExecution Value threadCount) :
    Liveness.InfiniteRun (GlobalStep (Value := Value)) where
  state := execution.state
  action := execution.event
  valid := execution.valid

/-- The first `length` source events in chronological order. -/
def tracePrefix
    (execution : InfiniteExecution Value threadCount)
    (length : Nat) : List (TraceEvent Value) :=
  (List.range length).map execution.event

@[simp] theorem tracePrefix_zero
    (execution : InfiniteExecution Value threadCount) :
    execution.tracePrefix 0 = [] :=
  rfl

/-- Extending a prefix appends exactly the event at its previous length. -/
theorem tracePrefix_succ
    (execution : InfiniteExecution Value threadCount)
    (length : Nat) :
    execution.tracePrefix (length + 1) =
      execution.tracePrefix length ++ [execution.event length] := by
  simp [tracePrefix, List.range_succ]

end InfiniteExecution

namespace Run

/-- Append one local transition to an existing per-thread source run. -/
theorem snoc
    {thread : ThreadId}
    {initial middle final : LocalState Value}
    {events : List (TraceEvent Value)}
    {event : TraceEvent Value}
    (run : Run thread initial events middle)
    (last : LocalStep thread middle event final) :
    Run thread initial (events ++ [event]) final := by
  induction run with
  | nil state =>
      exact .cons event [] last (.nil final)
  | @cons initial next middle first rest head tail
      inductionHypothesis =>
      exact .cons first (rest ++ [event]) head
        (inductionHypothesis last)

end Run

/-- Per-thread source projection distributes over trace concatenation. -/
theorem threadTrace_append
    (thread : ThreadId)
    (first second : List (TraceEvent Value)) :
    threadTrace (first ++ second) thread =
      threadTrace first thread ++ threadTrace second thread := by
  induction first with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, threadTrace, List.filter_cons]
      split <;> simp_all

namespace InfiniteExecution

/--
Every finite global prefix projects to the exact local run ending in the
recorded state at that time.
-/
theorem prefix_run
    (execution : InfiniteExecution Value threadCount)
    (thread : ThreadId)
    (length : Nat) :
    Run thread .idle
      (threadTrace (execution.tracePrefix length) thread)
      (execution.state length thread) := by
  induction length with
  | zero =>
      change Run thread (.idle : LocalState Value) []
        (execution.state 0 thread)
      rw [execution.initial thread]
      exact .nil .idle
  | succ length inductionHypothesis =>
      rw [tracePrefix_succ, threadTrace_append]
      by_cases owned : (execution.event length).thread = thread
      · have localStep :
            LocalStep thread
              (execution.state length thread)
              (execution.event length)
              (execution.state (length + 1) thread) := by
          simpa [owned] using (execution.valid length).owner
        simpa [threadTrace, owned] using
          inductionHypothesis.snoc localStep
      · have unchanged :
            execution.state (length + 1) thread =
              execution.state length thread :=
          (execution.valid length).frame thread (Ne.symm owned)
        rw [unchanged]
        simpa [threadTrace, owned] using inductionHypothesis

end InfiniteExecution

/-!
## One coherent infinite RC11 execution

Each finite prefix is an existing `SupportedExecution`.  The restriction
fields connect its RF and per-site MO data to single global relations.
-/

structure InfiniteRC11Execution
    (Value : Type)
    (threadCount : Nat)
    (dummy : NodeId) where
  source : InfiniteExecution Value threadCount
  readSource : EventId → Option EventId
  modificationOrder : Site → EventId → EventId → Prop
  modificationOrderIrreflexive :
    ∀ site event, ¬ modificationOrder site event event
  modificationOrderTransitive :
    ∀ site {first middle last},
      modificationOrder site first middle →
      modificationOrder site middle last →
      modificationOrder site first last
  finitePrefix :
    (length : Nat) →
      SupportedExecution dummy (source.tracePrefix length)
  prefixReadSource :
    ∀ length
      (atom : MultiLocationRC11.Atom Site Ptr),
      atom ∈ (finitePrefix length).candidate.atoms →
        MultiLocationRC11.sourceFor
            (finitePrefix length).readSources atom.id =
          readSource atom.id
  prefixModificationOrder :
    ∀ length site
      (first second : MultiLocationRC11.Atom Site Ptr),
      first ∈ (finitePrefix length).candidate.atoms →
      second ∈ (finitePrefix length).candidate.atoms →
        (MultiLocationRC11.IdBefore first.id second.id
            ((finitePrefix length).modificationOrder site) ↔
          modificationOrder site first.id second.id)

namespace InfiniteRC11Execution

/-- Expose one finite source-backed RC11 prefix through a named projection. -/
def supportedPrefix
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (length : Nat) :
    SupportedExecution dummy (execution.source.tracePrefix length) :=
  execution.finitePrefix length

/-- The infinite queue execution viewed through site-indexed weak-CAS progress. -/
def progressInterface
    (execution : InfiniteRC11Execution Value threadCount dummy) :
    WeakCAS.SiteProgressRule.Interface ThreadId Site where
  active time thread :=
    LocalState.Active (execution.source.state time thread)
  response time :=
    (execution.source.event time).IsResponse
  succeededAt site time :=
    (execution.source.event time).SucceededAt site
  modifiedAt site time :=
    (execution.source.event time).ModifiedAt site
  success_is_modification := by
    intro site time succeeded
    exact TraceEvent.succeededAt_isModifiedAt succeeded
  matchingAttemptAt thread site time :=
    (execution.source.event time).MatchingAttemptAt thread site

/-- The exact algorithm/scheduler/memory premise used by the generic rule. -/
def ProgressObligations
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  WeakCAS.SiteProgressRule.Obligations execution.progressInterface

/-- Primitive weak-CAS justice independently at Head, Tail, and every `next`. -/
def WeakCASJustice
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  WeakCAS.SiteProgressRule.PrimitiveJustice execution.progressInterface

/-- From every state containing an active call, some later method responds. -/
def SystemResponseProgress
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  WeakCAS.SiteProgressRule.SystemResponseProgress
    execution.progressInterface

/-- The site-indexed generic theorem specialized to Michael--Scott source events. -/
theorem systemResponseProgress_of_siteJustice
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (obligations : execution.ProgressObligations)
    (justice : execution.WeakCASJustice) :
    execution.SystemResponseProgress :=
  WeakCAS.SiteProgressRule.systemResponseProgress_of_siteJustice
    execution.progressInterface obligations justice

/-- Strong compare-equal CAS behavior discharges the primitive-justice premise. -/
theorem systemResponseProgress_of_strongCAS
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (obligations : execution.ProgressObligations)
    (strong :
      ∀ site thread time,
        execution.progressInterface.matchingAttemptAt
            thread site time →
          execution.progressInterface.succeededAt site time) :
    execution.SystemResponseProgress :=
  execution.systemResponseProgress_of_siteJustice obligations
    (WeakCAS.SiteProgressRule.primitiveJustice_of_matchingAttemptsSucceed
      execution.progressInterface strong)

/-- At arbitrarily late states, at least one queue method remains active. -/
def RecurringDemand
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  Liveness.InfinitelyOften fun time =>
    ∃ thread,
      LocalState.Active (execution.source.state time thread)

/-- Method responses occur at arbitrarily late source positions. -/
def InfinitelyManyResponses
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  Liveness.InfinitelyOften fun time =>
    (execution.source.event time).IsResponse

/-- Recurring demand turns one-step system progress into unbounded responses. -/
theorem infinitelyManyResponses_of_systemResponseProgress
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (recurring : execution.RecurringDemand)
    (progress : execution.SystemResponseProgress) :
    execution.InfinitelyManyResponses := by
  intro bound
  obtain ⟨activeTime, afterBound, thread, active⟩ := recurring bound
  obtain ⟨responseTime, afterActive, response⟩ :=
    progress activeTime ⟨thread, active⟩
  exact ⟨responseTime,
    Nat.le_trans afterBound afterActive, response⟩

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
