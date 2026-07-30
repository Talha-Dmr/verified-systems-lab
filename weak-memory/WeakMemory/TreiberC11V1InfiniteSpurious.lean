import WeakMemory.TreiberC11V1FairLockFreedom

namespace WeakMemory.TreiberC11V1

/-!
# A concrete infinite all-spurious Treiber execution

This module constructs a one-thread source execution containing one pending
push.  After its initial relaxed load and first `next` write, the thread
alternates forever between a compare-equal failed weak CAS and rewriting the
same immutable `next` value.  The head remains the null initializer.
-/

namespace InfiniteSpurious

/-- The unique operation reserves node one and always expects the null head. -/
def event : Nat → TraceEvent Unit
  | 0 =>
      .invokePush 0 1 1 ()
  | 1 =>
      .atomic ⟨1, .pushLoad 0 1 .null⟩
  | 2 =>
      .writeNext 0 1 1 .null
  | retry + 3 =>
      if retry % 2 = 0 then
        .atomic
          ⟨retry / 2 + 2,
            .pushCas 0 1 1 () .null .null false⟩
      else
        .writeNext 0 1 1 .null

/-- Closed form of the local state before each source event. -/
def localState : Nat → LocalState Unit
  | 0 =>
      .idle
  | 1 =>
      .pushLoading 1 1 ()
  | 2 =>
      .pushWriting 1 1 () .null
  | retry + 3 =>
      if retry % 2 = 0 then
        .pushing 1 1 () .null
      else
        .pushWriting 1 1 () .null

/-- Only thread zero participates. -/
def state (time : Nat) : GlobalState Unit :=
  fun thread =>
    if thread = 0 then localState time else .idle

@[simp] theorem event_thread (time : Nat) :
    (event time).thread = 0 := by
  cases time with
  | zero =>
      rfl
  | succ time =>
      cases time with
      | zero =>
          rfl
      | succ time =>
          cases time with
          | zero =>
              rfl
          | succ retry =>
              simp [event]
              split <;> rfl

@[simp] theorem state_zero (thread : ThreadId) :
    state 0 thread = .idle := by
  simp [state, localState]

/-- Every closed-form source transition is an exact Treiber step. -/
theorem valid_step (time : Nat) :
    GlobalStep (state time) (event time) (state (time + 1)) := by
  cases time with
  | zero =>
      refine {
        owner := ?_
        frame := ?_
      }
      · simpa [state, localState, event, TraceEvent.thread] using
          (LocalStep.beginPush
            (α := Unit) (thread := 0) 1 1 ())
      · intro thread different
        have threadNe : thread ≠ 0 := by
          simpa using different
        simp [state, threadNe]
  | succ time =>
      cases time with
      | zero =>
          refine {
            owner := ?_
            frame := ?_
          }
          · simpa [state, localState, event, TraceEvent.thread,
              AtomicAction.thread] using
              (LocalStep.pushLoad
                (α := Unit) (thread := 0)
                1 1 1 () Ptr.null)
          · intro thread different
            have threadNe : thread ≠ 0 := by
              simpa using different
            simp [state, threadNe]
      | succ time =>
          cases time with
          | zero =>
              refine {
                owner := ?_
                frame := ?_
              }
              · simpa [state, localState, event,
                  TraceEvent.thread] using
                  (LocalStep.writeNext
                    (α := Unit) (thread := 0)
                    1 1 () Ptr.null)
              · intro thread different
                have threadNe : thread ≠ 0 := by
                  simpa using different
                simp [state, threadNe]
          | succ retry =>
              rcases Nat.mod_two_eq_zero_or_one retry with
                  even | odd
              · have nextOdd : (retry + 1) % 2 = 1 := by
                  omega
                refine {
                  owner := ?_
                  frame := ?_
                }
                · simpa [state, localState, event, even, nextOdd,
                    TraceEvent.thread, AtomicAction.thread] using
                    (push_spuriousFailure
                      (α := Unit)
                      0 (retry / 2 + 2) 1 1 () Ptr.null)
                · intro thread different
                  have threadNe : thread ≠ 0 := by
                    simpa using different
                  simp [state, threadNe]
              · have nextEven : (retry + 1) % 2 = 0 := by
                  omega
                refine {
                  owner := ?_
                  frame := ?_
                }
                · simpa [state, localState, event, odd, nextEven,
                    TraceEvent.thread] using
                    (LocalStep.writeNext
                      (α := Unit) (thread := 0)
                      1 1 () Ptr.null)
                · intro thread different
                  have threadNe : thread ≠ 0 := by
                    simpa using different
                  simp [state, threadNe]

/-- The concrete infinite one-thread source execution. -/
def source : InfiniteExecution Unit 1 where
  state := state
  event := event
  initial := state_zero
  ownerBound := by
    intro time
    simp
  valid := valid_step

/-- The only participating thread satisfies weak scheduling fairness. -/
theorem source_threadFair :
    source.WeakThreadFair := by
  intro thread continuouslyEnabled
  by_cases owner : thread = 0
  · subst thread
    exact
      Liveness.InfinitelyOften.of_forall
        (fun time =>
          congrArg some (event_thread time))
  · obtain ⟨start, enabled⟩ := continuouslyEnabled
    have active :
        Active (source.state start thread) :=
      enabled start (Nat.le_refl start)
    have idle :
        source.state start thread = .idle := by
      simp [source, state, owner]
    rw [idle] at active
    simp [Active] at active

/-- Every source event fails to be a successful CAS. -/
theorem source_noSuccessfulCAS (time : Nat) :
    ¬ (source.event time).IsSuccessfulCAS := by
  cases time with
  | zero =>
      simp [source, event, TraceEvent.IsSuccessfulCAS]
  | succ time =>
      cases time with
      | zero =>
          simp [source, event, TraceEvent.IsSuccessfulCAS]
      | succ time =>
          cases time with
          | zero =>
              simp [source, event, TraceEvent.IsSuccessfulCAS]
          | succ retry =>
              by_cases even : retry % 2 = 0
              · simp [source, event, even,
                  TraceEvent.IsSuccessfulCAS]
              · simp [source, event, even,
                  TraceEvent.IsSuccessfulCAS]

/-- No method response occurs anywhere in the source trace. -/
theorem source_noResponse (time : Nat) :
    ¬ (source.event time).IsResponse := by
  cases time with
  | zero =>
      simp [source, event, TraceEvent.IsResponse]
  | succ time =>
      cases time with
      | zero =>
          simp [source, event, TraceEvent.IsResponse]
      | succ time =>
          cases time with
          | zero =>
              simp [source, event, TraceEvent.IsResponse]
          | succ retry =>
              by_cases even : retry % 2 = 0
              · simp [source, event, even,
                  TraceEvent.IsResponse]
              · simp [source, event, even,
                  TraceEvent.IsResponse]

/-- The single push is active at every state after its invocation. -/
theorem source_active_from_one
    (time : Nat)
    (afterInvocation : 1 ≤ time) :
    Active (source.state time 0) := by
  cases time with
  | zero =>
      omega
  | succ time =>
      cases time with
      | zero =>
          simp [source, state, localState, Active]
      | succ time =>
          cases time with
          | zero =>
              simp [source, state, localState, Active]
          | succ retry =>
              by_cases even : retry % 2 = 0
              · simp [source, state, localState, even, Active]
              · simp [source, state, localState, even, Active]

/-- The active call after time one is specifically a pending push. -/
theorem source_pushPopActive_from_one
    (time : Nat)
    (afterInvocation : 1 ≤ time) :
    PushPopActive (source.state time 0) := by
  cases time with
  | zero =>
      omega
  | succ time =>
      cases time with
      | zero =>
          simp [source, state, localState, PushPopActive]
      | succ time =>
          cases time with
          | zero =>
              simp [source, state, localState, PushPopActive]
          | succ retry =>
              by_cases even : retry % 2 = 0
              · simp [source, state, localState, even, PushPopActive]
              · simp [source, state, localState, even, PushPopActive]

/-- Compare-equal weak-CAS failures occur at arbitrarily late positions. -/
theorem source_matchingCASAttempts :
    Liveness.InfinitelyOften
      (fun time =>
        source.event time |>.CASComparesEqual) := by
  intro bound
  let time := 2 * bound + 3
  refine ⟨time, ?_, ?_⟩
  · dsimp [time]
    omega
  · have even : (2 * bound) % 2 = 0 := by
      omega
    simp [source, event, time, even,
      TraceEvent.CASComparesEqual,
      TraceEvent.casExpected?, TraceEvent.casObserved?]

/-- The matching attempts are all owned by thread zero. -/
theorem source_matchingCASAttemptsByZero :
    Liveness.InfinitelyOften
      (fun time =>
        (source.event time).thread = 0 ∧
          (source.event time).CASComparesEqual) := by
  exact
    source_matchingCASAttempts.mono
      (fun time matching => ⟨event_thread time, matching⟩)

end InfiniteSpurious

end WeakMemory.TreiberC11V1
