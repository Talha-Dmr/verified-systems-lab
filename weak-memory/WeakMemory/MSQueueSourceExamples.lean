import WeakMemory.MSQueueSource

namespace WeakMemory.MSQueue.Source.Example

/-! Concrete local runs for all three abstract queue commits. -/

def enqueueEvents : List (TraceEvent Nat) :=
  [.invokeEnqueue 0 10 1 7,
   .initializePayload 0 10 1 7,
   .atomic ⟨3, .initializeNext 0 10 1⟩,
   .atomic ⟨4, .enqueueTailLoad 0 10 (.node 0)⟩,
   .atomic ⟨5, .enqueueNextLoad 0 10 0 .null⟩,
   .atomic ⟨6, .enqueueTailValidate 0 10 (.node 0)⟩,
   .atomic ⟨7, .enqueueLinkCAS 0 10 0 1 7 .null true⟩,
   .atomic ⟨8, .enqueueFinishTailCAS 0 10 0 1 (.node 0) true⟩,
   .respondEnqueue 0 10]

theorem enqueueRun :
    Run 0 (.idle : LocalState Nat) enqueueEvents .idle := by
  exact
    Run.cons _ _ (LocalStep.beginEnqueue 10 1 7) <|
    Run.cons _ _ (LocalStep.initializePayload 10 1 7) <|
    Run.cons _ _ (LocalStep.initializeNext 3 10 1 7) <|
    Run.cons _ _ (LocalStep.enqueueTailLoad 4 10 1 7 0) <|
    Run.cons _ _ (LocalStep.enqueueNextLoad 5 10 1 7 0 .null) <|
    Run.cons _ _ (LocalStep.enqueueTailStableNull 6 10 1 7 0) <|
    Run.cons _ _ (LocalStep.enqueueLinkSuccess 7 10 1 7 0) <|
    Run.cons _ _ (LocalStep.enqueueFinishTailSuccess 8 10 1 7 0) <|
    Run.cons _ _ (LocalStep.finishEnqueue 10) <|
    Run.nil .idle

theorem enqueueCommits :
    (enqueueEvents.filterMap TraceEvent.commitRecord?).map
        AtomicOccurrence.CommitRecord.commit =
      [.enqueue 7] := by
  rfl

def emptyDequeueEvents : List (TraceEvent Nat) :=
  [.invokeDequeue 1 20,
   .atomic ⟨14, .dequeueHeadLoad 1 20 (.node 1)⟩,
   .atomic ⟨15, .dequeueTailLoad 1 20 (.node 1)⟩,
   .atomic ⟨16, .dequeueNextLoad 1 20 1 .null⟩,
   .atomic ⟨17, .dequeueHeadValidateEmpty 1 20 1 16⟩,
   .respondDequeue 1 20 none]

theorem emptyDequeueRun :
    Run 1 (.idle : LocalState Nat) emptyDequeueEvents .idle := by
  exact
    Run.cons _ _ (LocalStep.beginDequeue 20) <|
    Run.cons _ _ (LocalStep.dequeueHeadLoad 14 20 1) <|
    Run.cons _ _ (LocalStep.dequeueTailLoad 15 20 1 1) <|
    Run.cons _ _ (LocalStep.dequeueNextLoad 16 20 1 1 .null) <|
    Run.cons _ _ (LocalStep.dequeueEmpty 17 20 1 16) <|
    Run.cons _ _ (LocalStep.finishDequeue 20 none) <|
    Run.nil .idle

theorem emptyDequeueCommits :
    (emptyDequeueEvents.filterMap TraceEvent.commitRecord?).map
        AtomicOccurrence.CommitRecord.commit =
      [.dequeueEmpty] := by
  rfl

theorem emptyDequeuePoint_precedesValidation :
    (emptyDequeueEvents.filterMap TraceEvent.commitRecord?).map
        (fun record => (record.point, record.validation)) =
      [(16, 17)] := by
  rfl

def valueDequeueEvents : List (TraceEvent Nat) :=
  [.invokeDequeue 2 30,
   .atomic ⟨9, .dequeueHeadLoad 2 30 (.node 0)⟩,
   .atomic ⟨10, .dequeueTailLoad 2 30 (.node 1)⟩,
   .atomic ⟨11, .dequeueNextLoad 2 30 0 (.node 1)⟩,
   .atomic ⟨12, .dequeueHeadValidate 2 30 (.node 0)⟩,
   .readPayload 2 30 1 7,
   .atomic ⟨13, .dequeueHeadCAS 2 30 0 1 7 (.node 0) true⟩,
   .respondDequeue 2 30 (some 7)]

theorem valueDequeueRun :
    Run 2 (.idle : LocalState Nat) valueDequeueEvents .idle := by
  exact
    Run.cons _ _ (LocalStep.beginDequeue 30) <|
    Run.cons _ _ (LocalStep.dequeueHeadLoad 9 30 0) <|
    Run.cons _ _ (LocalStep.dequeueTailLoad 10 30 0 1) <|
    Run.cons _ _ (LocalStep.dequeueNextLoad 11 30 0 1 (.node 1)) <|
    Run.cons _ _ (LocalStep.dequeueNonempty 12 30 0 1 1 11 (by decide)) <|
    Run.cons _ _ (LocalStep.readPayload 30 0 1 7) <|
    Run.cons _ _ (LocalStep.dequeueHeadSuccess 13 30 0 1 7) <|
    Run.cons _ _ (LocalStep.finishDequeue 30 (some 7)) <|
    Run.nil .idle

theorem valueDequeueCommits :
    (valueDequeueEvents.filterMap TraceEvent.commitRecord?).map
        AtomicOccurrence.CommitRecord.commit =
      [.dequeueValue 7] := by
  rfl

def sequentialEvents : List (TraceEvent Nat) :=
  enqueueEvents ++ valueDequeueEvents ++ emptyDequeueEvents

theorem sequentialCommits :
    (sequentialEvents.filterMap TraceEvent.commitRecord?).map
        AtomicOccurrence.CommitRecord.commit =
      [.enqueue 7, .dequeueValue 7, .dequeueEmpty] := by
  rfl

theorem sequentialCommitTrace :
    CommitTrace [] [.enqueue 7, .dequeueValue 7, .dequeueEmpty] [] := by
  exact
    CommitTrace.cons (.enqueue 7) _
      (CommitStep.enqueue [] 7) <|
    CommitTrace.cons (.dequeueValue 7) _
      (CommitStep.dequeueValue 7 []) <|
    CommitTrace.cons .dequeueEmpty _
      CommitStep.dequeueEmpty <|
    CommitTrace.nil []

theorem sequentialSourceHistoryLegal :
    QueueSpec.Legal []
      (completedHistory
        [.enqueue 7, .dequeueValue 7, .dequeueEmpty]) [] :=
  commitTrace_linearizable sequentialCommitTrace

/-- The audited projection of `head.next` is the dynamic next-field site. -/
example :
    (AtomicAction.dequeueNextLoad 2 30 0 (.node 1) :
      AtomicAction Nat).site = .next 0 :=
  rfl

/-- A compare-equal failed link CAS is a read, not an RC11 RMW. -/
example :
    (AtomicAction.enqueueLinkCAS 0 10 0 1 7 .null false).access =
      MultiLocationRC11.Access.load .null :=
  rfl

/-- Compare-equal failure is classified as genuinely spurious. -/
example :
    (AtomicAction.enqueueLinkCAS 0 10 0 1 7 .null false).IsSpuriousFailure := by
  simp [AtomicAction.IsSpuriousFailure, AtomicAction.casView?]

/-- Compare-unequal failure is a mismatch refresh, not a matching attempt. -/
example :
    (AtomicAction.enqueueLinkCAS 0 10 0 1 7 (.node 9) false).IsMismatchFailure := by
  simp [AtomicAction.IsMismatchFailure, AtomicAction.casView?]

/-- The source machine excludes a raw mismatched-success label. -/
example :
    ¬ ∃ initial final : LocalState Nat,
      LocalStep 0 initial
        (.atomic ⟨99,
          .enqueueLinkCAS 0 10 0 1 7 (.node 9) true⟩) final := by
  rintro ⟨initial, final, step⟩
  apply step.not_malformedSuccess
  simp [AtomicAction.IsMalformedSuccess, AtomicAction.casView?]

namespace RetroactiveEmpty

/-!
The dequeue observes null first, an enqueue links next, and only then does the
dequeue validate the unchanged Head.  Record-emission order is therefore not
linearization order.
-/
def events : List (TraceEvent Nat) :=
  [.atomic ⟨10, .dequeueNextLoad 1 20 0 .null⟩,
   .atomic ⟨11, .enqueueLinkCAS 0 10 0 1 7 .null true⟩,
   .atomic ⟨12, .dequeueHeadValidateEmpty 1 20 0 10⟩]

theorem emissionOrder :
    (events.filterMap TraceEvent.commitRecord?).map
        AtomicOccurrence.CommitRecord.commit =
      [.enqueue 7, .dequeueEmpty] := by
  rfl

theorem anchoredPoints :
    (events.filterMap TraceEvent.commitRecord?).map
        (fun record => (record.point, record.commit)) =
      [(11, .enqueue 7), (10, .dequeueEmpty)] := by
  rfl

/-- Emission order is not merely a different legal linearization order. -/
theorem emissionOrder_not_commitTrace :
    ¬ ∃ final,
      CommitTrace [] [.enqueue 7, .dequeueEmpty] final := by
  rintro ⟨final, trace⟩
  cases trace with
  | cons _ _ enqueueStep rest =>
      cases enqueueStep
      cases rest with
      | cons _ _ emptyStep tail =>
          cases emptyStep

/-- Ordering by the anchored points yields the legal abstract history. -/
theorem pointOrderedCommitTrace :
    CommitTrace [] [.dequeueEmpty, .enqueue 7] [7] := by
  exact
    CommitTrace.cons .dequeueEmpty _ CommitStep.dequeueEmpty <|
    CommitTrace.cons (.enqueue 7) _ (CommitStep.enqueue [] 7) <|
    CommitTrace.nil [7]

end RetroactiveEmpty

end WeakMemory.MSQueue.Source.Example
