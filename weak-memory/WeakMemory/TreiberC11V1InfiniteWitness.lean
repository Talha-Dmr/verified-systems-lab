import WeakMemory.TreiberC11V1FairLockFreedom

namespace WeakMemory.TreiberC11V1

/-!
# A concrete fair infinite Treiber execution

This module constructs a one-thread execution that repeatedly pushes a fresh
node.  Every operation performs a relaxed head load, writes its immutable
`next` field, succeeds at the weak release CAS, and returns.

The construction is intended to witness joint satisfiability of the infinite
source, RC11, fairness, primitive-progress, and long-run client assumptions.
-/

namespace InfiniteWitness

/-- Pointer stored in `head` before zero-based push number `operation`. -/
def priorHead (operation : Nat) : Ptr :=
  if operation = 0 then .null else .node operation

/-- The five source events of each successful push repeat forever. -/
def event (time : Nat) : TraceEvent Unit :=
  let operation := time / 5
  match time % 5 with
  | 0 =>
      .invokePush 0 (operation + 1) (operation + 1) ()
  | 1 =>
      .atomic
        ⟨2 * operation + 1,
          .pushLoad 0 (operation + 1)
            (priorHead operation)⟩
  | 2 =>
      .writeNext 0 (operation + 1) (operation + 1)
        (priorHead operation)
  | 3 =>
      .atomic
        ⟨2 * operation + 2,
          .pushCas 0 (operation + 1) (operation + 1) ()
            (priorHead operation) (priorHead operation) true⟩
  | _ =>
      .respondPush 0 (operation + 1)

/-- Closed form of the source local state before each event. -/
def localState (time : Nat) : LocalState Unit :=
  let operation := time / 5
  match time % 5 with
  | 0 =>
      .idle
  | 1 =>
      .pushLoading (operation + 1) (operation + 1) ()
  | 2 =>
      .pushWriting (operation + 1) (operation + 1) ()
        (priorHead operation)
  | 3 =>
      .pushing (operation + 1) (operation + 1) ()
        (priorHead operation)
  | _ =>
      .returningPush (operation + 1) ()

/-- Only thread zero participates; all other source states stay idle. -/
def state (time : Nat) : GlobalState Unit :=
  fun thread =>
    if thread = 0 then localState time else .idle

@[simp] theorem event_thread (time : Nat) :
    (event time).thread = 0 := by
  simp [event]
  split <;> rfl

@[simp] theorem state_zero (thread : ThreadId) :
    state 0 thread = .idle := by
  simp [state, localState]

private theorem phase_cases (time : Nat) :
    time % 5 = 0 ∨
      time % 5 = 1 ∨
      time % 5 = 2 ∨
      time % 5 = 3 ∨
      time % 5 = 4 := by
  omega

/-- Every closed-form source transition is an exact global Treiber step. -/
theorem valid_step (time : Nat) :
    GlobalStep (state time) (event time) (state (time + 1)) := by
  rcases phase_cases time with
      phase | phase | phase | phase | phase
  · have nextDiv : (time + 1) / 5 = time / 5 := by
      omega
    have nextMod : (time + 1) % 5 = 1 := by
      omega
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        priorHead, TraceEvent.thread] using
      (LocalStep.beginPush
        (α := Unit) (thread := 0)
        (time / 5 + 1) (time / 5 + 1) ())
    · intro thread different
      have threadNe : thread ≠ 0 := by
        simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 5 = time / 5 := by
      omega
    have nextMod : (time + 1) % 5 = 2 := by
      omega
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
      (LocalStep.pushLoad
        (α := Unit) (thread := 0)
        (2 * (time / 5) + 1)
        (time / 5 + 1) (time / 5 + 1) ()
        (priorHead (time / 5)))
    · intro thread different
      have threadNe : thread ≠ 0 := by
        simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 5 = time / 5 := by
      omega
    have nextMod : (time + 1) % 5 = 3 := by
      omega
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
      (LocalStep.writeNext
        (α := Unit) (thread := 0)
        (time / 5 + 1) (time / 5 + 1) ()
        (priorHead (time / 5)))
    · intro thread different
      have threadNe : thread ≠ 0 := by
        simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 5 = time / 5 := by
      omega
    have nextMod : (time + 1) % 5 = 4 := by
      omega
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread, AtomicAction.thread] using
      (LocalStep.pushSuccess
        (α := Unit) (thread := 0)
        (2 * (time / 5) + 2)
        (time / 5 + 1) (time / 5 + 1) ()
        (priorHead (time / 5)))
    · intro thread different
      have threadNe : thread ≠ 0 := by
        simpa using different
      simp [state, threadNe]
  · have nextDiv : (time + 1) / 5 = time / 5 + 1 := by
      omega
    have nextMod : (time + 1) % 5 = 0 := by
      omega
    refine {
      owner := ?_
      frame := ?_
    }
    · simpa [event, state, localState, phase, nextDiv, nextMod,
        TraceEvent.thread] using
      (LocalStep.finishPush
        (α := Unit) (thread := 0)
        (time / 5 + 1) ())
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
    change
      Liveness.InfinitelyOften (fun time =>
        some (source.event time).thread = some 0)
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

/-- Successful weak CAS events occur at arbitrarily late source positions. -/
theorem source_successfulCAS_often :
    Liveness.InfinitelyOften (fun time =>
      (source.event time).IsSuccessfulCAS) := by
  intro bound
  let time := 5 * bound + 3
  refine ⟨time, ?_, ?_⟩
  · dsimp [time]
    omega
  · simp [source, event, time, TraceEvent.IsSuccessfulCAS]

/-- Source-level method responses occur at arbitrarily late positions. -/
theorem source_responses_often :
    Liveness.InfinitelyOften (fun time =>
      (source.event time).IsResponse) := by
  intro bound
  let time := 5 * bound + 4
  refine ⟨time, ?_, ?_⟩
  · dsimp [time]
    omega
  · simp [source, event, time, TraceEvent.IsResponse]

/-- A pending push exists at arbitrarily late source states. -/
theorem source_pushDemand_often :
    Liveness.InfinitelyOften (fun time =>
      ∃ thread,
        PushPopActive (source.state time thread)) := by
  intro bound
  let time := 5 * bound + 1
  refine ⟨time, ?_, 0, ?_⟩
  · dsimp [time]
    omega
  · simp [source, state, localState, time, PushPopActive]

end InfiniteWitness

end WeakMemory.TreiberC11V1
