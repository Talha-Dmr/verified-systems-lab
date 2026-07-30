import WeakMemory.TreiberVerifiedModel

namespace WeakMemory.TreiberRC11.VerifiedModelClientOrderExamples

/-!
# Cross-thread client-order examples

Both examples use the same high-level operations: thread `0` pushes `7` at
node `1`, while thread `1` observes an empty stack.  Their graph schedules
linearize the empty pop before the successful push.

The overlapping history permits that schedule.  The second history places
the push response before the pop invocation, so the same linearization shape
violates the external cross-thread real-time obligation.
-/

private def owned
    (thread : Nat)
    (label : ControlFlow.Label Nat) :
    InterleavingCheck.RawOwnedLabel Nat where
  thread :=
    thread
  label :=
    label

/--
Expose the last Boolean reached by the production pipeline after every check
that precedes cross-thread client order has passed.

`some false` therefore identifies the client-order branch as the first
failing stage; `none` would identify an earlier failure.
-/
private def clientOrderStage?
    [DecidableEq α]
    (raw : RawTreiberModelExecution α) :
    Option Bool :=
  let initial :=
    (ModelInitial.initialized : TreiberRA.State α)
  match
      InterleavingCheck.validateRaw?
        initial raw.sourceLabels
  with
  | none =>
      none
  | some source =>
      match
          RelationDataCheck.check?
            source.skeleton raw.relationData
      with
      | none =>
          none
      | some relations =>
          match
              EventScheduleInput.resolve?
                source.skeleton.events
                raw.relationSchedule
          with
          | none =>
              none
          | some schedule =>
              match generatedShape :
                  GeneratedEventsCheck.generate?
                    relations initial raw.popPublications
              with
              | none =>
                  none
              | some allocator =>
                  if scheduleChecked :
                      RelationScheduleCheck.check
                        relations schedule = true
                  then
                    let generated :=
                      GeneratedEventsCheck.generate?_sound
                        relations initial raw.popPublications
                        generatedShape
                    let respects :=
                      RelationScheduleCheck.check_sound
                        scheduleChecked
                    let model :
                        ScheduledRelationModelExecution initial := {
                      source :=
                        source
                      relations :=
                        relations
                      allocator :=
                        allocator
                      initialHeadEmpty :=
                        ModelInitial.initialized_head
                      generated :=
                        generated
                      relationSchedule :=
                        schedule
                      scheduleRespectsGraph :=
                        respects
                    }
                    if _nextReadsChecked :
                        NextReadCheck.check
                          model.toSourceAtomicExecution = true
                    then
                      some
                        (ClientCompatibilityCheck.crossThreadRealTimeCompatible
                          model.toSourceAtomicExecution
                          model.relationSchedule)
                    else
                      none
                  else
                    none

/--
The operations overlap: the pop is invoked before the push responds.  Its
null observation may therefore be linearized before the successful push.
-/
def overlapping : RawTreiberModelExecution Nat where
  sourceLabels := [
    owned 0 (.invokePush 1 1 7),
    owned 0 (.atomic 1 (.pushLoad 0 none)),
    owned 0 (.writeNext 1 1 none),
    owned 1 (.invokePop 2),
    owned 1 (.atomic 2 (.popLoad 1 none)),
    owned 1 (.respond 2 (.popped none)),
    owned 0 (.atomic 1 (.pushSuccess 0 1 7 none)),
    owned 0 (.respond 1 .pushed)
  ]
  relationData := {
    writeTail := [3]
    readSources := [
      (1, 0),
      (2, 0),
      (3, 0)
    ]
  }
  relationSchedule := [0, 1, 2, 3]
  popPublications := []

/-- Every prefix check passes and the client-order branch returns true. -/
theorem overlapping_reachesClientOrderSuccess :
    clientOrderStage? overlapping = some true := by
  rfl

/-- The complete production validator accepts the overlapping history. -/
theorem overlapping_isAccepted :
    overlapping.validate?.isSome = true := by
  rfl

/--
Acceptance yields descriptor agreement, node-access safety, and classical
Herlihy--Wing linearizability for the concrete two-thread history.
-/
theorem overlapping_exists_verified :
    ∃ execution : ValidatedTreiberModelExecution Nat,
      overlapping.validate? = some execution ∧
        TreiberProgramDescriptor.Extracted.treiberProgram.descriptor =
          TreiberProgramDescriptor.controlFlowDescriptor ∧
        NodeAccessCertificate
          execution.atomic.toControlledCandidate ∧
        HerlihyWing.Linearizable []
          (sourceHistory execution.atomic.source.skeleton) :=
  overlapping.verified_of_supported overlapping_isAccepted

/--
Here the push completes before thread `1` invokes its pop.  The proposed
graph schedule still puts the null-reading pop event `3` before successful
push event `2`.
-/
def responseBeforeInvocation :
    RawTreiberModelExecution Nat where
  sourceLabels := [
    owned 0 (.invokePush 1 1 7),
    owned 0 (.atomic 1 (.pushLoad 0 none)),
    owned 0 (.writeNext 1 1 none),
    owned 0 (.atomic 1 (.pushSuccess 0 1 7 none)),
    owned 0 (.respond 1 .pushed),
    owned 1 (.invokePop 2),
    owned 1 (.atomic 2 (.popLoad 1 none)),
    owned 1 (.respond 2 (.popped none))
  ]
  relationData := {
    writeTail := [2]
    readSources := [
      (1, 0),
      (2, 0),
      (3, 0)
    ]
  }
  relationSchedule := [0, 1, 3, 2]
  popPublications := []

/--
Every earlier validation stage, including immutable-next checking, passes;
the reached client-order Boolean alone is false.
-/
theorem responseBeforeInvocation_reachesClientOrderFailure :
    clientOrderStage? responseBeforeInvocation = some false := by
  rfl

/-- The production validator rejects at that final client-order branch. -/
theorem responseBeforeInvocation_isRejected :
    responseBeforeInvocation.validate? = none := by
  rfl

end WeakMemory.TreiberRC11.VerifiedModelClientOrderExamples
