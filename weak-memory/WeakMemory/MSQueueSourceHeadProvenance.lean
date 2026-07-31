import WeakMemory.MSQueueSourceWellFormed

namespace WeakMemory.MSQueue.Source

/-!
# Dequeue Head and empty-point source provenance

This module recovers the complete same-attempt source prefix behind a
successful dequeue Head CAS and behind an empty validation.  The nonempty
path retains the payload read between validation and CAS.  The empty path
retains the earlier null `head.next` load as the actual linearization point.
-/

namespace Run

/-- Reaching the payload-reading state requires one exact stable nonempty
snapshot: Head load, Tail load, next-node load, then stable Head validation. -/
theorem dequeueReadingPayload_context
    {thread operation head next : Nat}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.dequeueReadingPayload operation head next)) :
    ∃ leading headLoadId tailLoadId nextLoadId validationId tail,
      head ≠ tail ∧
        events = leading ++
          [.atomic ⟨headLoadId,
              .dequeueHeadLoad thread operation (.node head)⟩,
           .atomic ⟨tailLoadId,
              .dequeueTailLoad thread operation (.node tail)⟩,
           .atomic ⟨nextLoadId,
              .dequeueNextLoad thread operation head (.node next)⟩,
           .atomic ⟨validationId,
              .dequeueHeadValidate thread operation (.node head)⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨beforeValidation, validationState, validationEvent,
      eventsShape, beforeValidationRun, validationStep⟩ :=
    run.lastStep_of_ne_nil eventsNonempty
  cases validationStep with
  | dequeueNonempty validationId operation head tail next nextRead different =>
      have beforeValidationNonempty : beforeValidation ≠ [] := by
        intro empty
        subst beforeValidation
        cases beforeValidationRun
      obtain ⟨beforeNext, nextState, nextEvent,
          beforeValidationShape, beforeNextRun, nextStep⟩ :=
        beforeValidationRun.lastStep_of_ne_nil beforeValidationNonempty
      cases nextStep with
      | dequeueNextLoad nextLoadId operation head tail next =>
          have beforeNextNonempty : beforeNext ≠ [] := by
            intro empty
            subst beforeNext
            cases beforeNextRun
          obtain ⟨beforeTail, tailState, tailEvent,
              beforeNextShape, beforeTailRun, tailStep⟩ :=
            beforeNextRun.lastStep_of_ne_nil beforeNextNonempty
          cases tailStep with
          | dequeueTailLoad tailLoadId operation head tail =>
              have beforeTailNonempty : beforeTail ≠ [] := by
                intro empty
                subst beforeTail
                cases beforeTailRun
              obtain ⟨leading, headState, headEvent,
                  beforeTailShape, leadingRun, headStep⟩ :=
                beforeTailRun.lastStep_of_ne_nil beforeTailNonempty
              cases headStep with
              | dequeueHeadLoad headLoadId operation head =>
                  exact ⟨leading, headLoadId, tailLoadId,
                    nextRead, validationId, tail, different, by
                      simp [eventsShape, beforeValidationShape,
                        beforeNextShape, beforeTailShape]⟩

/-- A successful dequeue Head CAS is preceded by the exact nonempty snapshot
and payload read belonging to the same operation attempt. -/
theorem dequeueHeadSuccess_context
    {thread casId operation head next : Nat}
    {value : Value}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation head next value
          (.node head) true⟩ ∈ events) :
    ∃ leading headLoadId tailLoadId nextLoadId validationId tail trailing,
      head ≠ tail ∧
        events = leading ++
          [.atomic ⟨headLoadId,
              .dequeueHeadLoad thread operation (.node head)⟩,
           .atomic ⟨tailLoadId,
              .dequeueTailLoad thread operation (.node tail)⟩,
           .atomic ⟨nextLoadId,
              .dequeueNextLoad thread operation head (.node next)⟩,
           .atomic ⟨validationId,
              .dequeueHeadValidate thread operation (.node head)⟩,
           .readPayload thread operation next value,
           .atomic ⟨casId,
              .dequeueHeadCAS thread operation head next value
                (.node head) true⟩] ++ trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, casStep, afterRun⟩ :=
    run.factor_of_mem member
  cases casStep with
  | dequeueHeadSuccess casId operation head next value =>
      have beforeEventsNonempty : beforeEvents ≠ [] := by
        intro empty
        subst beforeEvents
        cases beforeRun
      obtain ⟨beforePayload, payloadState, payloadEvent,
          beforeEventsShape, beforePayloadRun, payloadStep⟩ :=
        beforeRun.lastStep_of_ne_nil beforeEventsNonempty
      cases payloadStep with
      | readPayload operation head next value =>
          obtain ⟨leading, headLoadId, tailLoadId, nextLoadId,
              validationId, tail, different, prefixShape⟩ :=
            beforePayloadRun.dequeueReadingPayload_context
          exact ⟨leading, headLoadId, tailLoadId, nextLoadId,
            validationId, tail, afterEvents, different, by
              simp [eventsShape, beforeEventsShape, prefixShape]⟩

/-- Reaching an empty-validating state requires Head and Tail to have yielded
the same node, followed by a null load from that node's `next` field. -/
theorem dequeueValidatingEmpty_context
    {thread operation head point : Nat}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.dequeueValidatingHead operation head head point .null)) :
    ∃ leading headLoadId tailLoadId,
      events = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩,
         .atomic ⟨point,
            .dequeueNextLoad thread operation head .null⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨beforeNext, nextState, nextEvent,
      eventsShape, beforeNextRun, nextStep⟩ :=
    run.lastStep_of_ne_nil eventsNonempty
  cases nextStep with
  | dequeueNextLoad point operation head tail next =>
      have beforeNextNonempty : beforeNext ≠ [] := by
        intro empty
        subst beforeNext
        cases beforeNextRun
      obtain ⟨beforeTail, tailState, tailEvent,
          beforeNextShape, beforeTailRun, tailStep⟩ :=
        beforeNextRun.lastStep_of_ne_nil beforeNextNonempty
      cases tailStep with
      | dequeueTailLoad tailLoadId operation head tail =>
          have beforeTailNonempty : beforeTail ≠ [] := by
            intro empty
            subst beforeTail
            cases beforeTailRun
          obtain ⟨leading, headState, headEvent,
              beforeTailShape, leadingRun, headStep⟩ :=
            beforeTailRun.lastStep_of_ne_nil beforeTailNonempty
          cases headStep with
          | dequeueHeadLoad headLoadId operation head =>
              exact ⟨leading, headLoadId, tailLoadId, by
                simp [eventsShape, beforeNextShape, beforeTailShape]⟩

/-- An empty validation retains its complete same-attempt snapshot and the
exact earlier null-next event named by `point`. -/
theorem dequeueEmptyValidation_context
    {thread validationId operation head point : Nat}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨validationId,
          .dequeueHeadValidateEmpty thread operation head point⟩ ∈ events) :
    ∃ leading headLoadId tailLoadId trailing,
      events = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩,
         .atomic ⟨point,
            .dequeueNextLoad thread operation head .null⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidateEmpty thread operation head point⟩] ++
          trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, validationStep, afterRun⟩ :=
    run.factor_of_mem member
  cases validationStep with
  | dequeueEmpty validationId operation head point =>
      obtain ⟨leading, headLoadId, tailLoadId, beforeShape⟩ :=
        beforeRun.dequeueValidatingEmpty_context
      exact ⟨leading, headLoadId, tailLoadId, afterEvents, by
        simp [eventsShape, beforeShape]⟩

end Run

/-- Full same-attempt source provenance for a successful dequeue Head CAS.
The payload read is retained in the thread shape even though it is not an
RC11 atom. -/
def DequeueHeadSuccessProvenance
    (trace : List (TraceEvent Value))
    (thread casId operation head next : Nat)
    (value : Value) : Prop :=
  ∃ leading headLoadId tailLoadId nextLoadId validationId tail trailing,
    head ≠ tail ∧
      threadTrace trace thread = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node tail)⟩,
         .atomic ⟨nextLoadId,
            .dequeueNextLoad thread operation head (.node next)⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidate thread operation (.node head)⟩,
         .readPayload thread operation next value,
         .atomic ⟨casId,
            .dequeueHeadCAS thread operation head next value
              (.node head) true⟩] ++ trailing ∧
      TraceEvent.atomic
          ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node tail)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨nextLoadId,
            .dequeueNextLoad thread operation head (.node next)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨validationId,
            .dequeueHeadValidate thread operation (.node head)⟩ ∈ trace ∧
      TraceEvent.readPayload thread operation next value ∈ trace ∧
      MultiLocationRC11.IdBefore headLoadId tailLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore tailLoadId nextLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore nextLoadId validationId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore validationId casId (atomicIds trace)

/-- Full same-attempt source provenance for an empty dequeue validation.
The recorded `point` is exactly the earlier null `head.next` load. -/
def DequeueEmptyValidationProvenance
    (trace : List (TraceEvent Value))
    (thread validationId operation head point : Nat) : Prop :=
  ∃ leading headLoadId tailLoadId trailing,
    threadTrace trace thread = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩,
         .atomic ⟨point,
            .dequeueNextLoad thread operation head .null⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidateEmpty thread operation head point⟩] ++
          trailing ∧
      TraceEvent.atomic
          ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨point,
            .dequeueNextLoad thread operation head .null⟩ ∈ trace ∧
      MultiLocationRC11.IdBefore headLoadId tailLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore tailLoadId point (atomicIds trace) ∧
      MultiLocationRC11.IdBefore point validationId (atomicIds trace)

namespace SourceWellFormed

/-- A successful Head CAS in a well-formed source trace carries the exact
Head/Tail/next/stable-Head/payload prefix from its own dequeue attempt. -/
theorem dequeueHeadSuccess_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation head next : Nat}
    {value : Value}
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation head next value
          (.node head) true⟩ ∈ trace) :
    DequeueHeadSuccessProvenance trace thread casId operation head next value := by
  let headLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueHeadLoad thread operation (.node head)⟩ :
      AtomicOccurrence Value)
  let tailLoadEvent := fun id tail => TraceEvent.atomic
    (⟨id, .dequeueTailLoad thread operation (.node tail)⟩ :
      AtomicOccurrence Value)
  let nextLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueNextLoad thread operation head (.node next)⟩ :
      AtomicOccurrence Value)
  let validationEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueHeadValidate thread operation (.node head)⟩ :
      AtomicOccurrence Value)
  let payloadEvent : TraceEvent Value :=
    .readPayload thread operation next value
  let casEvent : TraceEvent Value := .atomic
    ⟨casId, .dequeueHeadCAS thread operation head next value
      (.node head) true⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : casEvent ∈ threadTrace trace thread := by
    simp [casEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
      tail, trailing, different, threadShape⟩ :=
    run.dequeueHeadSuccess_context threadMember
  have localHeadTail :
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId tail].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [headLoadEvent, tailLoadEvent]
  have localTailNext :
      [tailLoadEvent tailLoadId tail, nextLoadEvent nextLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [tailLoadEvent, nextLoadEvent]
  have localNextValidation :
      [nextLoadEvent nextLoadId, validationEvent validationId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply List.Sublist.trans (l₂ :=
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId tail,
        nextLoadEvent nextLoadId, validationEvent validationId,
        payloadEvent, casEvent])
    · simp
    · simp [headLoadEvent, tailLoadEvent, nextLoadEvent,
        validationEvent, payloadEvent, casEvent]
  have localValidationCas :
      [validationEvent validationId, casEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply List.Sublist.trans (l₂ :=
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId tail,
        nextLoadEvent nextLoadId, validationEvent validationId,
        payloadEvent, casEvent])
    · exact List.Sublist.cons (headLoadEvent headLoadId)
        (List.Sublist.cons (tailLoadEvent tailLoadId tail)
          (List.Sublist.cons (nextLoadEvent nextLoadId)
            (List.Sublist.cons_cons (validationEvent validationId)
              (List.Sublist.cons payloadEvent
                (List.Sublist.cons_cons casEvent List.Sublist.slnil)))))
    · simp [headLoadEvent, tailLoadEvent, nextLoadEvent,
        validationEvent, payloadEvent, casEvent]
  have localPayload :
      [payloadEvent].Sublist (threadTrace trace thread) := by
    rw [threadShape]
    simp [payloadEvent]
  have threadSublist :
      (threadTrace trace thread).Sublist trace :=
    List.filter_sublist
  have globalHeadTail := localHeadTail.trans threadSublist
  have globalTailNext := localTailNext.trans threadSublist
  have globalNextValidation := localNextValidation.trans threadSublist
  have globalValidationCas := localValidationCas.trans threadSublist
  have globalPayload := localPayload.trans threadSublist
  refine ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
    tail, trailing, different, threadShape, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact globalHeadTail.subset (by simp [headLoadEvent])
  · exact globalHeadTail.subset (by simp [tailLoadEvent])
  · exact globalTailNext.subset (by simp [nextLoadEvent])
  · exact globalNextValidation.subset (by simp [validationEvent])
  · exact globalPayload.subset (by simp [payloadEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalHeadTail
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalTailNext
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalNextValidation
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalValidationCas

/-- An empty validation in a well-formed source trace carries the same-attempt
Head=Tail snapshot and the exact null-next point it validates. -/
theorem dequeueEmptyValidation_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread validationId operation head point : Nat}
    (member :
      TraceEvent.atomic
        ⟨validationId,
          .dequeueHeadValidateEmpty thread operation head point⟩ ∈ trace) :
    DequeueEmptyValidationProvenance trace thread validationId operation
      head point := by
  let headLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueHeadLoad thread operation (.node head)⟩ :
      AtomicOccurrence Value)
  let tailLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueTailLoad thread operation (.node head)⟩ :
      AtomicOccurrence Value)
  let nextLoadEvent : TraceEvent Value := .atomic
    ⟨point, .dequeueNextLoad thread operation head .null⟩
  let validationEvent : TraceEvent Value := .atomic
    ⟨validationId,
      .dequeueHeadValidateEmpty thread operation head point⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : validationEvent ∈ threadTrace trace thread := by
    simp [validationEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨leading, headLoadId, tailLoadId, trailing, threadShape⟩ :=
    run.dequeueEmptyValidation_context threadMember
  have localHeadTail :
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [headLoadEvent, tailLoadEvent]
  have localTailNext :
      [tailLoadEvent tailLoadId, nextLoadEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [tailLoadEvent, nextLoadEvent]
  have localNextValidation :
      [nextLoadEvent, validationEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply List.Sublist.trans (l₂ :=
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId,
        nextLoadEvent, validationEvent])
    · simp
    · simp [headLoadEvent, tailLoadEvent, nextLoadEvent,
        validationEvent]
  have threadSublist :
      (threadTrace trace thread).Sublist trace :=
    List.filter_sublist
  have globalHeadTail := localHeadTail.trans threadSublist
  have globalTailNext := localTailNext.trans threadSublist
  have globalNextValidation := localNextValidation.trans threadSublist
  refine ⟨leading, headLoadId, tailLoadId, trailing, threadShape,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalHeadTail.subset (by simp [headLoadEvent])
  · exact globalHeadTail.subset (by simp [tailLoadEvent])
  · exact globalTailNext.subset (by simp [nextLoadEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalHeadTail
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalTailNext
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalNextValidation

end SourceWellFormed

private theorem headAtomicOccurrence_mem_of_atomicEvent_mem
    {trace : List (TraceEvent Value)}
    {occurrence : AtomicOccurrence Value}
    (member : TraceEvent.atomic occurrence ∈ trace) :
    occurrence ∈ atomicOccurrences trace :=
  List.mem_filterMap.mpr ⟨.atomic occurrence, member, rfl⟩

namespace SupportedExecution

/-- Candidate-level form of the successful Head-CAS source chain.  The four
adjacent atomic pairs are genuine RC11 program-order edges. -/
theorem dequeueHeadSuccess_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread casId operation head next : Nat}
    {value : Value}
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation head next value
          (.node head) true⟩ ∈ trace) :
    ∃ headLoadId tailLoadId nextLoadId validationId tail,
      head ≠ tail ∧
      MultiLocationRC11.PO execution.candidate
          (⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node tail)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node tail)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨nextLoadId,
            .dequeueNextLoad thread operation head (.node next)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨nextLoadId,
            .dequeueNextLoad thread operation head (.node next)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨validationId,
            .dequeueHeadValidate thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨validationId,
            .dequeueHeadValidate thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨casId,
            .dequeueHeadCAS thread operation head next value
              (.node head) true⟩ : AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨_leading, headLoadId, tailLoadId, nextLoadId, validationId,
      tail, _trailing, different, _threadShape, headLoadMember,
      tailLoadMember, nextLoadMember, validationMember, _payloadMember,
      headBeforeTail, tailBeforeNext, nextBeforeValidation,
      validationBeforeCas⟩ :=
    execution.sourceWellFormed.dequeueHeadSuccess_provenance member
  refine ⟨headLoadId, tailLoadId, nextLoadId, validationId, tail,
    different, ?_, ?_, ?_, ?_⟩
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem headLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      rfl headBeforeTail
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      rfl tailBeforeNext
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem validationMember)
      rfl nextBeforeValidation
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem validationMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem member)
      rfl validationBeforeCas

/-- Candidate-level form of the empty-dequeue source chain. -/
theorem dequeueEmptyValidation_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread validationId operation head point : Nat}
    (member :
      TraceEvent.atomic
        ⟨validationId,
          .dequeueHeadValidateEmpty thread operation head point⟩ ∈ trace) :
    ∃ headLoadId tailLoadId,
      MultiLocationRC11.PO execution.candidate
          (⟨headLoadId,
            .dequeueHeadLoad thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node head)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨point,
            .dequeueNextLoad thread operation head .null⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨point,
            .dequeueNextLoad thread operation head .null⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨validationId,
            .dequeueHeadValidateEmpty thread operation head point⟩ :
              AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨_leading, headLoadId, tailLoadId, _trailing, _threadShape,
      headLoadMember, tailLoadMember, nextLoadMember, headBeforeTail,
      tailBeforeNext, nextBeforeValidation⟩ :=
    execution.sourceWellFormed.dequeueEmptyValidation_provenance member
  refine ⟨headLoadId, tailLoadId, ?_, ?_, ?_⟩
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem headLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      rfl headBeforeTail
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      rfl tailBeforeNext
  · exact execution.programOrder_of_atomicIdBefore
      (headAtomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      (headAtomicOccurrence_mem_of_atomicEvent_mem member)
      rfl nextBeforeValidation

end SupportedExecution

end WeakMemory.MSQueue.Source
