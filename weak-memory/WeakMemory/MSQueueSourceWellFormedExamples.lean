import WeakMemory.MSQueueSourceExamples
import WeakMemory.MSQueueSourceWellFormed

namespace WeakMemory.MSQueue.Source.Example

/-!
The three-operation source history is also a checked global trace.  Its
dynamic atomic IDs are exactly `3, ..., 17`; the three static atoms therefore
make the complete projected carrier use the collision-free range `0, ..., 17`.
-/

theorem sequentialThreadRuns (thread : ThreadId) :
    ∃ final,
      Run thread (.idle : LocalState Nat)
        (threadTrace sequentialEvents thread) final := by
  by_cases threadZero : thread = 0
  · subst thread
    exact ⟨.idle, by
      simpa [threadTrace, sequentialEvents, enqueueEvents,
        valueDequeueEvents, emptyDequeueEvents, TraceEvent.thread,
        AtomicAction.thread] using enqueueRun⟩
  by_cases threadOne : thread = 1
  · subst thread
    exact ⟨.idle, by
      simpa [threadTrace, sequentialEvents, enqueueEvents,
        valueDequeueEvents, emptyDequeueEvents, TraceEvent.thread,
        AtomicAction.thread] using emptyDequeueRun⟩
  by_cases threadTwo : thread = 2
  · subst thread
    exact ⟨.idle, by
      simpa [threadTrace, sequentialEvents, enqueueEvents,
        valueDequeueEvents, emptyDequeueEvents, TraceEvent.thread,
        AtomicAction.thread] using valueDequeueRun⟩
  · refine ⟨.idle, ?_⟩
    have zeroThread : 0 ≠ thread := Ne.symm threadZero
    have oneThread : 1 ≠ thread := Ne.symm threadOne
    have twoThread : 2 ≠ thread := Ne.symm threadTwo
    have emptyProjection :
        threadTrace sequentialEvents thread = [] := by
      simp [threadTrace, sequentialEvents, enqueueEvents,
        valueDequeueEvents, emptyDequeueEvents,
        TraceEvent.thread, AtomicAction.thread,
        zeroThread, oneThread, twoThread]
    rw [emptyProjection]
    exact Run.nil .idle

theorem sequentialPayloadInitializationBeforeRead :
    EventBefore
      (.initializePayload 0 10 1 7)
      (.readPayload 2 30 1 7)
      sequentialEvents := by
  refine ⟨[.invokeEnqueue 0 10 1 7],
    [.atomic ⟨3, .initializeNext 0 10 1⟩,
     .atomic ⟨4, .enqueueTailLoad 0 10 (.node 0)⟩,
     .atomic ⟨5, .enqueueNextLoad 0 10 0 .null⟩,
     .atomic ⟨6, .enqueueTailValidate 0 10 (.node 0)⟩,
     .atomic ⟨7, .enqueueLinkCAS 0 10 0 1 7 .null true⟩,
     .atomic ⟨8, .enqueueFinishTailCAS 0 10 0 1 (.node 0) true⟩,
     .respondEnqueue 0 10,
     .invokeDequeue 2 30,
     .atomic ⟨9, .dequeueHeadLoad 2 30 (.node 0)⟩,
     .atomic ⟨10, .dequeueTailLoad 2 30 (.node 1)⟩,
     .atomic ⟨11, .dequeueNextLoad 2 30 0 (.node 1)⟩,
     .atomic ⟨12, .dequeueHeadValidate 2 30 (.node 0)⟩],
    [.atomic ⟨13, .dequeueHeadCAS 2 30 0 1 7 (.node 0) true⟩,
     .respondDequeue 2 30 (some 7),
     .invokeDequeue 1 20,
     .atomic ⟨14, .dequeueHeadLoad 1 20 (.node 1)⟩,
     .atomic ⟨15, .dequeueTailLoad 1 20 (.node 1)⟩,
     .atomic ⟨16, .dequeueNextLoad 1 20 1 .null⟩,
     .atomic ⟨17, .dequeueHeadValidateEmpty 1 20 1 16⟩,
     .respondDequeue 1 20 none], ?_⟩
  rfl

theorem sequentialSourceWellFormed :
    SourceWellFormed 0 sequentialEvents := by
  refine {
    atomicIdsCanonical := ?_
    invocationIdsNodup := ?_
    reservedNodesNodup := ?_
    dummyNotReserved := ?_
    threadRuns := sequentialThreadRuns
    payloadInitializationMatches := ?_
    nextInitializationMatches := ?_
    payloadReadInitialized := ?_
    emptyAnchor := ?_
  }
  · decide
  · decide
  · decide
  · decide
  · intro thread operation node value member
    simp [sequentialEvents, enqueueEvents, valueDequeueEvents,
      emptyDequeueEvents] at member ⊢
    simp_all
  · intro id thread operation node member
    simp [sequentialEvents, enqueueEvents, valueDequeueEvents,
      emptyDequeueEvents] at member ⊢
    simp_all
  · intro index thread operation node value selected
    have indexShape :
        (thread = 2 ∧ operation = 30 ∧ node = 1 ∧ value = 7) ∧
          index = 14 := by
      simpa [sequentialEvents, enqueueEvents, valueDequeueEvents,
        emptyDequeueEvents] using selected
    rcases indexShape with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    refine ⟨0, 10, 1, by decide, ?_⟩
    decide
  · intro validation thread operation head point member
    simp [sequentialEvents, enqueueEvents, valueDequeueEvents,
      emptyDequeueEvents] at member ⊢
    simp_all [atomicIds, atomicOccurrences,
      TraceEvent.atomicOccurrence?, MultiLocationRC11.IdBefore,
      List.idxOf_cons]

theorem sequentialProjectedAtomIds :
    (projectCandidate 0 sequentialEvents [] (fun _ => [])).atomIds =
      List.range 18 := by
  decide

theorem sequentialEmptyPointBeforeValidation :
    MultiLocationRC11.IdBefore 16 17 (atomicIds sequentialEvents) := by
  apply sequentialSourceWellFormed.emptyPointBeforeValidation
  show TraceEvent.atomic
      ⟨17, AtomicAction.dequeueHeadValidateEmpty 1 20 1 16⟩ ∈
    sequentialEvents
  decide

namespace Rejections

def reusedNodeEvents : List (TraceEvent Nat) :=
  [.invokeEnqueue 0 40 2 7,
   .invokeEnqueue 1 41 2 8]

/-- A node identity cannot be reserved by two enqueue operations. -/
theorem reusedNode_rejected :
    ¬ SourceWellFormed 0 reusedNodeEvents := by
  intro wellFormed
  have nodup := wellFormed.reservedNodesNodup
  simp [reservedNodes, reusedNodeEvents, TraceEvent.reservedNode?] at nodup

def wrongPayloadEvents : List (TraceEvent Nat) :=
  [.initializePayload 0 40 2 7,
   .readPayload 1 41 2 8]

/-- Payload provenance is value-sensitive, not merely node-sensitive. -/
theorem wrongPayload_rejected :
    ¬ SourceWellFormed 0 wrongPayloadEvents := by
  intro wellFormed
  have readSelected :
      (TraceEvent.readPayload 1 41 2 8, 1) ∈
        wrongPayloadEvents.zipIdx := by
    decide
  obtain ⟨owner, invocation, initializationIndex,
      earlier, initializerSelected⟩ :=
    wellFormed.payloadReadInitialized readSelected
  have initializationIndexZero : initializationIndex = 0 := by
    omega
  subst initializationIndex
  simp [wrongPayloadEvents] at initializerSelected

def danglingEmptyAnchorEvents : List (TraceEvent Nat) :=
  [.atomic ⟨3, .dequeueNextLoad 1 50 0 .null⟩,
   .atomic ⟨4, .dequeueHeadValidateEmpty 1 50 0 99⟩]

/-- An empty validation cannot name an arbitrary or absent point. -/
theorem danglingEmptyAnchor_rejected :
    ¬ SourceWellFormed 0 danglingEmptyAnchorEvents := by
  intro wellFormed
  have validationMember :
      TraceEvent.atomic
          ⟨4, AtomicAction.dequeueHeadValidateEmpty 1 50 0 99⟩ ∈
        danglingEmptyAnchorEvents := by
    simp [danglingEmptyAnchorEvents]
  have pointMember := (wellFormed.emptyAnchor validationMember).1
  simp [danglingEmptyAnchorEvents] at pointMember

def noncanonicalIdEvents : List (TraceEvent Nat) :=
  [.atomic ⟨9, .dequeueHeadLoad 0 60 (.node 0)⟩]

/-- Source atom IDs cannot collide with, skip, or precede the canonical range. -/
theorem noncanonicalId_rejected :
    ¬ SourceWellFormed 0 noncanonicalIdEvents := by
  intro wellFormed
  have canonical := wellFormed.atomicIdsCanonical
  simp [atomicIds, atomicOccurrences, canonicalDynamicIds,
    noncanonicalIdEvents, TraceEvent.atomicOccurrence?] at canonical

end Rejections

end WeakMemory.MSQueue.Source.Example
