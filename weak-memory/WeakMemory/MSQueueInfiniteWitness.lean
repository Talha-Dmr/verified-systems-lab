import WeakMemory.MSQueueInfiniteControlProgress

namespace WeakMemory.MSQueue.Source

/-!
# A concrete successful infinite Michael--Scott source execution

This module constructs the source component of a one-thread execution that
repeatedly enqueues `Unit`.  Enqueue number `operation` reserves fresh node
`operation + 1`, observes the current Tail at node `operation`, links the new
node successfully, advances Tail successfully, and returns.

The companion prefix module equips every finite prefix with one coherent RC11
candidate.  Separating the source cycle from that declarative proof keeps the
closed-form control calculation usable on its own.
-/

namespace InfiniteWitness

/-- The nine source events of each successful enqueue repeat forever. -/
def event (time : Nat) : TraceEvent Unit :=
  let operation := time / 9
  match time % 9 with
  | 0 =>
      .invokeEnqueue 0 (operation + 1) (operation + 1) ()
  | 1 =>
      .initializePayload 0 (operation + 1) (operation + 1) ()
  | 2 =>
      .atomic
        ⟨6 * operation + 3,
          .initializeNext 0 (operation + 1) (operation + 1)⟩
  | 3 =>
      .atomic
        ⟨6 * operation + 4,
          .enqueueTailLoad 0 (operation + 1) (.node operation)⟩
  | 4 =>
      .atomic
        ⟨6 * operation + 5,
          .enqueueNextLoad 0 (operation + 1) operation .null⟩
  | 5 =>
      .atomic
        ⟨6 * operation + 6,
          .enqueueTailValidate 0 (operation + 1) (.node operation)⟩
  | 6 =>
      .atomic
        ⟨6 * operation + 7,
          .enqueueLinkCAS 0 (operation + 1) operation (operation + 1)
            () .null true⟩
  | 7 =>
      .atomic
        ⟨6 * operation + 8,
          .enqueueFinishTailCAS 0 (operation + 1) operation
            (operation + 1) (.node operation) true⟩
  | _ =>
      .respondEnqueue 0 (operation + 1)

/-- Closed form of thread zero's local state before each source event. -/
def localState (time : Nat) : LocalState Unit :=
  let operation := time / 9
  match time % 9 with
  | 0 => .idle
  | 1 =>
      .enqueueWritingPayload (operation + 1) (operation + 1) ()
  | 2 =>
      .enqueueInitializingNext (operation + 1) (operation + 1) ()
  | 3 =>
      .enqueueLoadingTail (operation + 1) (operation + 1) ()
  | 4 =>
      .enqueueLoadingNext (operation + 1) (operation + 1) () operation
  | 5 =>
      .enqueueValidatingTail (operation + 1) (operation + 1) ()
        operation .null
  | 6 =>
      .enqueueLinking (operation + 1) (operation + 1) () operation
  | 7 =>
      .enqueueFinishingTail (operation + 1) (operation + 1) () operation
  | _ =>
      .enqueueReturning (operation + 1)

/-- Only thread zero participates; every other local state stays idle. -/
def state (time : Nat) : GlobalState Unit :=
  fun thread => if thread = 0 then localState time else .idle

@[simp] theorem event_thread (time : Nat) :
    (event time).thread = 0 := by
  simp [event]
  split <;> rfl

@[simp] theorem state_zero (thread : ThreadId) :
    state 0 thread = .idle := by
  simp [state, localState]

private theorem phase_cases (time : Nat) :
    time % 9 = 0 ∨
      time % 9 = 1 ∨
      time % 9 = 2 ∨
      time % 9 = 3 ∨
      time % 9 = 4 ∨
      time % 9 = 5 ∨
      time % 9 = 6 ∨
      time % 9 = 7 ∨
      time % 9 = 8 := by
  omega

/-- Every closed-form transition is an exact global queue source step. -/
theorem valid_step (time : Nat) :
    GlobalStep (state time) (event time) (state (time + 1)) := by
  rcases phase_cases time with
      phase | phase | phase | phase | phase | phase | phase | phase | phase
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 1 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread] using
        (LocalStep.beginEnqueue
          (Value := Unit) (thread := 0)
          (time / 9 + 1) (time / 9 + 1) ())
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 2 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread] using
        (LocalStep.initializePayload
          (Value := Unit) (thread := 0)
          (time / 9 + 1) (time / 9 + 1) ())
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 3 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.initializeNext
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 3)
          (time / 9 + 1) (time / 9 + 1) ())
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 4 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.enqueueTailLoad
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 4)
          (time / 9 + 1) (time / 9 + 1) () (time / 9))
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 5 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.enqueueNextLoad
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 5)
          (time / 9 + 1) (time / 9 + 1) () (time / 9) .null)
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 6 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.enqueueTailStableNull
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 6)
          (time / 9 + 1) (time / 9 + 1) () (time / 9))
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 7 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.enqueueLinkSuccess
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 7)
          (time / 9 + 1) (time / 9 + 1) () (time / 9))
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 9 = time / 9 := by omega
    have nextMod : (time + 1) % 9 = 8 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
        (LocalStep.enqueueFinishTailSuccess
          (Value := Unit) (thread := 0)
          (6 * (time / 9) + 8)
          (time / 9 + 1) (time / 9 + 1) () (time / 9))
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
      simp [state, threadNe]
  · have wrapDiv : (time + 1) / 9 = time / 9 + 1 := by omega
    have wrapMod : (time + 1) % 9 = 0 := by omega
    refine { owner := ?_, frame := ?_ }
    · simpa [event, state, localState, phase, wrapDiv, wrapMod,
        TraceEvent.thread] using
        (LocalStep.finishEnqueue
          (thread := 0) (time / 9 + 1))
    · intro thread different
      have threadNe : thread ≠ 0 := by simpa using different
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
    change
      Liveness.InfinitelyOften (fun time =>
        some (source.event time).thread = some 0)
    exact Liveness.InfinitelyOften.of_forall
      (fun time => congrArg some (event_thread time))
  · obtain ⟨start, enabled⟩ := continuouslyEnabled
    have active :
        (source.state start thread).Active :=
      enabled start (Nat.le_refl start)
    have idle : source.state start thread = .idle := by
      simp [source, state, owner]
    rw [idle] at active
    simp [LocalState.Active] at active

/-- Successful queue CAS events occur at arbitrarily late positions. -/
theorem source_successfulCAS_often :
    Liveness.InfinitelyOften (fun time =>
      ∃ site, (source.event time).SucceededAt site) := by
  intro bound
  let time := 9 * bound + 6
  have timeDiv : time / 9 = bound := by
    dsimp [time]
    rw [Nat.mul_add_div (by decide)]
    simp
  refine ⟨time, ?_, .next bound, ?_⟩
  · dsimp [time]
    omega
  · simp [source, event, time, timeDiv,
      TraceEvent.SucceededAt,
      AtomicAction.site, AtomicAction.succeededCAS]

/-- Source-level method responses occur at arbitrarily late positions. -/
theorem source_responses_often :
    Liveness.InfinitelyOften (fun time =>
      (source.event time).IsResponse) := by
  intro bound
  let time := 9 * bound + 8
  refine ⟨time, ?_, ?_⟩
  · dsimp [time]
    omega
  · simp [source, event, time, TraceEvent.IsResponse]

/-- An active enqueue exists at arbitrarily late source states. -/
theorem source_enqueueDemand_often :
    Liveness.InfinitelyOften (fun time =>
      ∃ thread, (source.state time thread).Active) := by
  intro bound
  let time := 9 * bound + 1
  refine ⟨time, ?_, 0, ?_⟩
  · dsimp [time]
    omega
  · simp [source, state, localState, time, LocalState.Active]

end InfiniteWitness

end WeakMemory.MSQueue.Source
