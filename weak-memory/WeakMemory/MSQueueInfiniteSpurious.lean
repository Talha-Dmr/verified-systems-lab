import WeakMemory.MSQueueInfinite

namespace WeakMemory.MSQueue.Source

/-!
# A concrete infinite all-spurious Michael--Scott execution

One thread starts an enqueue of node one.  After initializing the node, it
repeatedly observes the unchanged dummy tail and its null `next` field.  Every
compare-equal weak CAS at the exact logical site `next 0` fails spuriously.
-/

namespace InfiniteSpurious

inductive RetryPhase where
  | link
  | tail
  | next
  | validate
  deriving Repr, DecidableEq

namespace RetryPhase

def advance : RetryPhase → RetryPhase
  | .link => .tail
  | .tail => .next
  | .next => .validate
  | .validate => .link

end RetryPhase

/-- The four source-control phases repeated after the first validation. -/
def retryPhase : Nat → RetryPhase
  | 0 => .link
  | time + 1 => (retryPhase time).advance

@[simp] theorem retryPhase_add_four (time : Nat) :
    retryPhase (time + 4) = retryPhase time := by
  change
    ((((retryPhase time).advance).advance).advance).advance =
      retryPhase time
  cases retryPhase time <;> rfl

@[simp] theorem retryPhase_four_mul (count : Nat) :
    retryPhase (4 * count) = .link := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Nat.mul_succ]
      calc
        retryPhase (4 * count + 4) = retryPhase (4 * count) :=
          retryPhase_add_four (4 * count)
        _ = .link := inductionHypothesis

/-- One pending enqueue followed by the infinite retry loop. -/
def event : Nat → TraceEvent Unit
  | 0 => .invokeEnqueue 0 1 1 ()
  | 1 => .initializePayload 0 1 1 ()
  | 2 => .atomic ⟨3, .initializeNext 0 1 1⟩
  | 3 => .atomic ⟨4, .enqueueTailLoad 0 1 (.node 0)⟩
  | 4 => .atomic ⟨5, .enqueueNextLoad 0 1 0 .null⟩
  | 5 => .atomic ⟨6, .enqueueTailValidate 0 1 (.node 0)⟩
  | retry + 6 =>
      match retryPhase retry with
      | .link =>
          .atomic
            ⟨retry + 7,
              .enqueueLinkCAS 0 1 0 1 () .null false⟩
      | .tail =>
          .atomic
            ⟨retry + 7, .enqueueTailLoad 0 1 (.node 0)⟩
      | .next =>
          .atomic
            ⟨retry + 7, .enqueueNextLoad 0 1 0 .null⟩
      | .validate =>
          .atomic
            ⟨retry + 7, .enqueueTailValidate 0 1 (.node 0)⟩

/-- Closed form of the sole participating thread's local state. -/
def localState : Nat → LocalState Unit
  | 0 => .idle
  | 1 => .enqueueWritingPayload 1 1 ()
  | 2 => .enqueueInitializingNext 1 1 ()
  | 3 => .enqueueLoadingTail 1 1 ()
  | 4 => .enqueueLoadingNext 1 1 () 0
  | 5 => .enqueueValidatingTail 1 1 () 0 .null
  | retry + 6 =>
      match retryPhase retry with
      | .link => .enqueueLinking 1 1 () 0
      | .tail => .enqueueLoadingTail 1 1 ()
      | .next => .enqueueLoadingNext 1 1 () 0
      | .validate => .enqueueValidatingTail 1 1 () 0 .null

/-- Only thread zero participates. -/
def state (time : Nat) : GlobalState Unit :=
  fun thread => if thread = 0 then localState time else .idle

@[simp] theorem event_thread (time : Nat) :
    (event time).thread = 0 := by
  cases time with
  | zero => rfl
  | succ time =>
      cases time with
      | zero => rfl
      | succ time =>
          cases time with
          | zero => rfl
          | succ time =>
              cases time with
              | zero => rfl
              | succ time =>
                  cases time with
                  | zero => rfl
                  | succ time =>
                      cases time with
                      | zero => rfl
                      | succ retry =>
                          cases phase : retryPhase retry <;>
                            simp [event, phase, TraceEvent.thread,
                              AtomicAction.thread]

@[simp] theorem state_zero (thread : ThreadId) :
    state 0 thread = .idle := by
  simp [state, localState]

/-- Every closed-form event is an exact Michael--Scott source transition. -/
theorem valid_step (time : Nat) :
    GlobalStep (state time) (event time) (state (time + 1)) := by
  have frame
      (owner : LocalStep 0 (localState time) (event time)
        (localState (time + 1))) :
      GlobalStep (state time) (event time) (state (time + 1)) := by
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [state] using owner
    · intro thread different
      have threadNe : thread ≠ 0 := by
        simpa using different
      simp [state, threadNe]
  cases time with
  | zero =>
      exact frame (LocalStep.beginEnqueue 1 1 ())
  | succ time =>
      cases time with
      | zero =>
          exact frame (LocalStep.initializePayload 1 1 ())
      | succ time =>
          cases time with
          | zero =>
              exact frame (LocalStep.initializeNext 3 1 1 ())
          | succ time =>
              cases time with
              | zero =>
                  exact frame (LocalStep.enqueueTailLoad 4 1 1 () 0)
              | succ time =>
                  cases time with
                  | zero =>
                      exact frame
                        (LocalStep.enqueueNextLoad 5 1 1 () 0 .null)
                  | succ time =>
                      cases time with
                      | zero =>
                          exact frame
                            (LocalStep.enqueueTailStableNull 6 1 1 () 0)
                      | succ retry =>
                          cases phase : retryPhase retry with
                          | link =>
                              apply frame
                              simpa [localState, event, phase, retryPhase,
                                RetryPhase.advance] using
                                (enqueueLink_spuriousFailure
                                  (Value := Unit) 0 (retry + 7)
                                  1 1 0 ())
                          | tail =>
                              apply frame
                              simpa [localState, event, phase, retryPhase,
                                RetryPhase.advance] using
                                (LocalStep.enqueueTailLoad
                                  (Value := Unit) (thread := 0)
                                  (retry + 7) 1 1 () 0)
                          | next =>
                              apply frame
                              simpa [localState, event, phase, retryPhase,
                                RetryPhase.advance] using
                                (LocalStep.enqueueNextLoad
                                  (Value := Unit) (thread := 0)
                                  (retry + 7) 1 1 () 0 .null)
                          | validate =>
                              apply frame
                              simpa [localState, event, phase, retryPhase,
                                RetryPhase.advance] using
                                (LocalStep.enqueueTailStableNull
                                  (Value := Unit) (thread := 0)
                                  (retry + 7) 1 1 () 0)

/-- The concrete infinite one-thread source execution. -/
def source : InfiniteExecution Unit 1 where
  state := state
  event := event
  initial := state_zero
  ownerBound := by
    intro time
    simp
  valid := valid_step

/-- No method response occurs anywhere in the source stream. -/
theorem source_noResponse (time : Nat) :
    ¬ (source.event time).IsResponse := by
  cases time with
  | zero => simp [source, event, TraceEvent.IsResponse]
  | succ time =>
      cases time with
      | zero => simp [source, event, TraceEvent.IsResponse]
      | succ time =>
          cases time with
          | zero => simp [source, event, TraceEvent.IsResponse]
          | succ time =>
              cases time with
              | zero => simp [source, event, TraceEvent.IsResponse]
              | succ time =>
                  cases time with
                  | zero => simp [source, event, TraceEvent.IsResponse]
                  | succ time =>
                      cases time with
                      | zero => simp [source, event, TraceEvent.IsResponse]
                      | succ retry =>
                          cases phase : retryPhase retry <;>
                            simp [source, event, phase,
                              TraceEvent.IsResponse]

/-- The target `next 0` generation is never modified. -/
theorem source_noModification_nextDummy (time : Nat) :
    ¬ (source.event time).ModifiedAt (.next 0) := by
  cases time with
  | zero => simp [source, event, TraceEvent.ModifiedAt]
  | succ time =>
      cases time with
      | zero => simp [source, event, TraceEvent.ModifiedAt]
      | succ time =>
          cases time with
          | zero =>
              simp [source, event, TraceEvent.ModifiedAt,
                AtomicAction.site, AtomicAction.access,
                MultiLocationRC11.Access.IsWrite]
          | succ time =>
              cases time with
              | zero =>
                  simp [source, event, TraceEvent.ModifiedAt,
                    AtomicAction.site, AtomicAction.access,
                    MultiLocationRC11.Access.IsWrite]
              | succ time =>
                  cases time with
                  | zero =>
                      simp [source, event, TraceEvent.ModifiedAt,
                        AtomicAction.site, AtomicAction.access,
                        MultiLocationRC11.Access.IsWrite]
                  | succ time =>
                      cases time with
                      | zero =>
                          simp [source, event, TraceEvent.ModifiedAt,
                            AtomicAction.site, AtomicAction.access,
                            MultiLocationRC11.Access.IsWrite]
                      | succ retry =>
                          cases phase : retryPhase retry <;>
                            simp [source, event, phase,
                              TraceEvent.ModifiedAt,
                              AtomicAction.site, AtomicAction.access,
                              MultiLocationRC11.Access.IsWrite]

/-- Retry indices divisible by four are compare-equal attempts at `next 0`. -/
theorem source_matchingAttempt_nextDummy (count : Nat) :
    (source.event (6 + 4 * count)).MatchingAttemptAt 0 (.next 0) := by
  simp [source, event, Nat.add_comm, retryPhase_four_mul,
    TraceEvent.MatchingAttemptAt, AtomicAction.thread,
    AtomicAction.site, AtomicAction.IsMatchingCAS,
    AtomicAction.casView?]

/-- Compare-equal attempts at `next 0` occur arbitrarily late. -/
theorem source_matchingAttempts_nextDummy :
    Liveness.InfinitelyOften fun time =>
      (source.event time).MatchingAttemptAt 0 (.next 0) := by
  intro bound
  refine ⟨6 + 4 * bound, ?_, source_matchingAttempt_nextDummy bound⟩
  omega

/-- The single enqueue remains active at every state after invocation. -/
theorem source_active_from_one
    (time : Nat)
    (afterInvocation : 1 ≤ time) :
    LocalState.Active (source.state time 0) := by
  cases time with
  | zero => omega
  | succ time =>
      cases time with
      | zero => simp [source, state, localState, LocalState.Active]
      | succ time =>
          cases time with
          | zero => simp [source, state, localState, LocalState.Active]
          | succ time =>
              cases time with
              | zero => simp [source, state, localState, LocalState.Active]
              | succ time =>
                  cases time with
                  | zero => simp [source, state, localState, LocalState.Active]
                  | succ time =>
                      cases time with
                      | zero =>
                          simp [source, state, localState, LocalState.Active]
                      | succ retry =>
                          cases phase : retryPhase retry <;>
                            simp [source, state, localState, phase,
                              LocalState.Active]

end InfiniteSpurious

end WeakMemory.MSQueue.Source
