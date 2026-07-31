import WeakMemory.MSQueueSourceWellFormed

namespace WeakMemory.MSQueue.Source

/-!
# Source-control provenance of successful queue actions

These facts recover the actual same-attempt observations that led to a
successful structural CAS.  They use the per-thread source machine rather
than assuming a favorable RC11 or linearization order.
-/

private theorem orderedBlock_sublist
    {selected leading block trailing : List α}
    (inside : selected.Sublist block) :
    selected.Sublist (leading ++ block ++ trailing) := by
  exact inside.trans (by simp)

namespace Run

/-- Reaching the enqueue-linking control state requires the exact stable-null
attempt prefix: Tail load, null `tail.next` load, then stable Tail validation. -/
theorem enqueueLinking_context
    {thread operation node tail : Nat}
    {value : Value}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.enqueueLinking operation node value tail)) :
    ∃ leading tailLoadId nextLoadId validationId,
      events = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node tail)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨beforeValidation, validationState, validationEvent,
      eventsShape, beforeValidationRun, validationStep⟩ :=
    run.lastStep_of_ne_nil eventsNonempty
  cases validationStep with
  | enqueueTailStableNull validationId operation node value tail =>
      have beforeValidationNonempty : beforeValidation ≠ [] := by
        intro empty
        subst beforeValidation
        cases beforeValidationRun
      obtain ⟨beforeNextLoad, nextLoadState, nextLoadEvent,
          beforeValidationShape, beforeNextLoadRun, nextLoadStep⟩ :=
        beforeValidationRun.lastStep_of_ne_nil beforeValidationNonempty
      cases nextLoadStep with
      | enqueueNextLoad nextLoadId operation node value tail next =>
          have beforeNextLoadNonempty : beforeNextLoad ≠ [] := by
            intro empty
            subst beforeNextLoad
            cases beforeNextLoadRun
          obtain ⟨leading, tailLoadState, tailLoadEvent,
              beforeNextLoadShape, leadingRun, tailLoadStep⟩ :=
            beforeNextLoadRun.lastStep_of_ne_nil beforeNextLoadNonempty
          cases tailLoadStep with
          | enqueueTailLoad tailLoadId operation node value tail =>
              exact ⟨leading, tailLoadId, nextLoadId, validationId, by
                simp [eventsShape, beforeValidationShape,
                  beforeNextLoadShape]⟩

/-- A successful enqueue link is immediately preceded in its thread trace by
the stable-null attempt observations that justify entering the CAS state. -/
theorem enqueueLinkSuccess_context
    {thread linkId operation node tail : Nat}
    {value : Value}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨linkId, .enqueueLinkCAS thread operation tail node value .null true⟩
          ∈ events) :
    ∃ leading tailLoadId nextLoadId validationId trailing,
      events = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node tail)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩,
         .atomic ⟨linkId,
            .enqueueLinkCAS thread operation tail node value .null true⟩] ++
        trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, linkStep, afterRun⟩ :=
    run.factor_of_mem member
  cases linkStep with
  | enqueueLinkSuccess linkId operation node value tail =>
      obtain ⟨leading, tailLoadId, nextLoadId, validationId,
          beforeShape⟩ := beforeRun.enqueueLinking_context
      exact ⟨leading, tailLoadId, nextLoadId, validationId, afterEvents, by
        simp [eventsShape, beforeShape]⟩

/-- Entering enqueue Tail-help retains the exact non-null `next` observation
and stable Tail validation from the same attempt. -/
theorem enqueueHelpingTail_context
    {thread operation node expected desired : Nat}
    {value : Value}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.enqueueHelpingTail operation node value expected desired)) :
    ∃ leading tailLoadId nextLoadId validationId,
      events = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨beforeValidation, validationState, validationEvent,
      eventsShape, beforeValidationRun, validationStep⟩ :=
    run.lastStep_of_ne_nil eventsNonempty
  cases validationStep with
  | enqueueTailStableNode validationId operation node value expected desired =>
      have beforeValidationNonempty : beforeValidation ≠ [] := by
        intro empty
        subst beforeValidation
        cases beforeValidationRun
      obtain ⟨beforeNextLoad, nextLoadState, nextLoadEvent,
          beforeValidationShape, beforeNextLoadRun, nextLoadStep⟩ :=
        beforeValidationRun.lastStep_of_ne_nil beforeValidationNonempty
      cases nextLoadStep with
      | enqueueNextLoad nextLoadId operation node value expected next =>
          have beforeNextLoadNonempty : beforeNextLoad ≠ [] := by
            intro empty
            subst beforeNextLoad
            cases beforeNextLoadRun
          obtain ⟨leading, tailLoadState, tailLoadEvent,
              beforeNextLoadShape, leadingRun, tailLoadStep⟩ :=
            beforeNextLoadRun.lastStep_of_ne_nil beforeNextLoadNonempty
          cases tailLoadStep with
          | enqueueTailLoad tailLoadId operation node value expected =>
              exact ⟨leading, tailLoadId, nextLoadId, validationId, by
                simp [eventsShape, beforeValidationShape,
                  beforeNextLoadShape]⟩

/-- Exact local context of a successful enqueue-help Tail CAS. -/
theorem enqueueHelpTailSuccess_context
    {thread casId operation expected desired : Nat}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ events) :
    ∃ leading tailLoadId nextLoadId validationId trailing,
      events = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩,
         .atomic ⟨casId,
            .enqueueHelpTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, helpStep, afterRun⟩ :=
    run.factor_of_mem member
  cases helpStep with
  | enqueueHelpTailSuccess casId operation node value expected desired =>
      obtain ⟨leading, tailLoadId, nextLoadId, validationId,
          beforeShape⟩ := beforeRun.enqueueHelpingTail_context
      exact ⟨leading, tailLoadId, nextLoadId, validationId, afterEvents,
        by simp [eventsShape, beforeShape]⟩

/-- Entering dequeue Tail-help retains the exact Head/Tail/next snapshot and
the stable Head validation from that same dequeue attempt. -/
theorem dequeueHelpingTail_context
    {thread operation expected desired : Nat}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.dequeueHelpingTail operation expected desired)) :
    ∃ leading headLoadId tailLoadId nextLoadId validationId,
      events = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node expected)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨beforeValidation, validationState, validationEvent,
      eventsShape, beforeValidationRun, validationStep⟩ :=
    run.lastStep_of_ne_nil eventsNonempty
  cases validationStep with
  | dequeueNeedsHelp validationId operation expected desired nextRead =>
      have beforeValidationNonempty : beforeValidation ≠ [] := by
        intro empty
        subst beforeValidation
        cases beforeValidationRun
      obtain ⟨beforeNextLoad, nextLoadState, nextLoadEvent,
          beforeValidationShape, beforeNextLoadRun, nextLoadStep⟩ :=
        beforeValidationRun.lastStep_of_ne_nil beforeValidationNonempty
      cases nextLoadStep with
      | dequeueNextLoad nextLoadId operation head tail next =>
          have beforeNextLoadNonempty : beforeNextLoad ≠ [] := by
            intro empty
            subst beforeNextLoad
            cases beforeNextLoadRun
          obtain ⟨beforeTailLoad, tailLoadState, tailLoadEvent,
              beforeNextLoadShape, beforeTailLoadRun, tailLoadStep⟩ :=
            beforeNextLoadRun.lastStep_of_ne_nil beforeNextLoadNonempty
          cases tailLoadStep with
          | dequeueTailLoad tailLoadId operation head tail =>
              have beforeTailLoadNonempty : beforeTailLoad ≠ [] := by
                intro empty
                subst beforeTailLoad
                cases beforeTailLoadRun
              obtain ⟨leading, headLoadState, headLoadEvent,
                  beforeTailLoadShape, leadingRun, headLoadStep⟩ :=
                beforeTailLoadRun.lastStep_of_ne_nil beforeTailLoadNonempty
              cases headLoadStep with
              | dequeueHeadLoad headLoadId operation head =>
                  exact ⟨leading, headLoadId, tailLoadId, nextRead,
                    validationId, by
                      simp [eventsShape, beforeValidationShape,
                        beforeNextLoadShape, beforeTailLoadShape]⟩

/-- Exact local context of a successful dequeue-help Tail CAS. -/
theorem dequeueHelpTailSuccess_context
    {thread casId operation expected desired : Nat}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨casId,
          .dequeueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ events) :
    ∃ leading headLoadId tailLoadId nextLoadId validationId trailing,
      events = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node expected)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩,
         .atomic ⟨casId,
            .dequeueHelpTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, helpStep, afterRun⟩ :=
    run.factor_of_mem member
  cases helpStep with
  | dequeueHelpTailSuccess casId operation expected desired =>
      obtain ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
          beforeShape⟩ := beforeRun.dequeueHelpingTail_context
      exact ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
        afterEvents, by simp [eventsShape, beforeShape]⟩

/-- Enqueue finishing can only be entered by the successful link that
installed the exact desired node into `expected.next`. -/
theorem enqueueFinishingTail_context
    {thread operation expected desired : Nat}
    {value : Value}
    {events : List (TraceEvent Value)}
    (run : Run thread (.idle : LocalState Value) events
      (.enqueueFinishingTail operation desired value expected)) :
    ∃ leading linkId,
      events = leading ++
        [.atomic ⟨linkId,
          .enqueueLinkCAS thread operation expected desired value .null true⟩] := by
  have eventsNonempty : events ≠ [] := by
    intro empty
    subst events
    cases run
  obtain ⟨leading, linkState, linkEvent, eventsShape, leadingRun,
      linkStep⟩ := run.lastStep_of_ne_nil eventsNonempty
  cases linkStep with
  | enqueueLinkSuccess linkId operation desired value expected =>
      exact ⟨leading, linkId, eventsShape⟩

/-- Exact local context of a successful enqueue-finish Tail CAS. -/
theorem enqueueFinishTailSuccess_context
    {thread casId operation expected desired : Nat}
    {events : List (TraceEvent Value)}
    {final : LocalState Value}
    (run : Run thread (.idle : LocalState Value) events final)
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueFinishTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ events) :
    ∃ value leading linkId trailing,
      events = leading ++
        [.atomic ⟨linkId,
            .enqueueLinkCAS thread operation expected desired value .null true⟩,
         .atomic ⟨casId,
            .enqueueFinishTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing := by
  obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
      eventsShape, beforeRun, finishStep, afterRun⟩ :=
    run.factor_of_mem member
  cases finishStep with
  | enqueueFinishTailSuccess casId operation desired value expected =>
      obtain ⟨leading, linkId, beforeShape⟩ :=
        beforeRun.enqueueFinishingTail_context
      exact ⟨value, leading, linkId, afterEvents, by
        simp [eventsShape, beforeShape]⟩

end Run

/-- Full same-attempt control-flow provenance for one successful link CAS. -/
def EnqueueLinkSuccessProvenance
    (trace : List (TraceEvent Value))
    (thread linkId operation node tail : Nat)
    (value : Value) : Prop :=
  ∃ tailLoadId nextLoadId validationId leading trailing,
    threadTrace trace thread = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node tail)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩,
         .atomic ⟨linkId,
            .enqueueLinkCAS thread operation tail node value .null true⟩] ++
        trailing ∧
      TraceEvent.atomic
          ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node tail)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩ ∈ trace ∧
      MultiLocationRC11.IdBefore tailLoadId nextLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore nextLoadId validationId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore validationId linkId (atomicIds trace)

/-- Same-attempt source observations behind an enqueue-help Tail CAS. -/
def EnqueueHelpTailSuccessProvenance
    (trace : List (TraceEvent Value))
    (thread casId operation expected desired : Nat) : Prop :=
  ∃ leading tailLoadId nextLoadId validationId trailing,
    threadTrace trace thread = leading ++
        [.atomic ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩,
         .atomic ⟨casId,
            .enqueueHelpTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing ∧
      TraceEvent.atomic
          ⟨tailLoadId,
            .enqueueTailLoad thread operation (.node expected)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩ ∈ trace ∧
      MultiLocationRC11.IdBefore tailLoadId nextLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore nextLoadId validationId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore validationId casId (atomicIds trace)

/-- Same-attempt source observations behind a dequeue-help Tail CAS.  The
stability check on this path is the exact Head validation from the algorithm. -/
def DequeueHelpTailSuccessProvenance
    (trace : List (TraceEvent Value))
    (thread casId operation expected desired : Nat) : Prop :=
  ∃ leading headLoadId tailLoadId nextLoadId validationId trailing,
    threadTrace trace thread = leading ++
        [.atomic ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node expected)⟩,
         .atomic ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩,
         .atomic ⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩,
         .atomic ⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩,
         .atomic ⟨casId,
            .dequeueHelpTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing ∧
      TraceEvent.atomic
          ⟨headLoadId,
            .dequeueHeadLoad thread operation (.node expected)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩ ∈ trace ∧
      TraceEvent.atomic
          ⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩ ∈ trace ∧
      MultiLocationRC11.IdBefore headLoadId tailLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore tailLoadId nextLoadId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore nextLoadId validationId (atomicIds trace) ∧
      MultiLocationRC11.IdBefore validationId casId (atomicIds trace)

/-- A finishing Tail CAS is sourced by the immediately preceding successful
link that installed exactly its `desired` node. -/
def EnqueueFinishTailSuccessProvenance
    (trace : List (TraceEvent Value))
    (thread casId operation expected desired : Nat) : Prop :=
  ∃ (value : Value), ∃ leading linkId trailing,
    threadTrace trace thread = leading ++
        [.atomic ⟨linkId,
            .enqueueLinkCAS thread operation expected desired value .null true⟩,
         .atomic ⟨casId,
            .enqueueFinishTailCAS thread operation expected desired
              (.node expected) true⟩] ++ trailing ∧
      TraceEvent.atomic
          ⟨linkId,
            .enqueueLinkCAS thread operation expected desired value .null true⟩
        ∈ trace ∧
      MultiLocationRC11.IdBefore linkId casId (atomicIds trace)

namespace SourceWellFormed

/-- A successful link event in a well-formed global trace carries the exact
Tail/null-next/stable-Tail control prefix emitted by the same operation. -/
theorem enqueueLinkSuccess_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread linkId operation node tail : Nat}
    {value : Value}
    (member :
      TraceEvent.atomic
        ⟨linkId, .enqueueLinkCAS thread operation tail node value .null true⟩
          ∈ trace) :
    EnqueueLinkSuccessProvenance trace thread linkId operation node tail value := by
  let tailLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueTailLoad thread operation (.node tail)⟩ :
      AtomicOccurrence Value)
  let nextLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueNextLoad thread operation tail .null⟩ :
      AtomicOccurrence Value)
  let validationEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueTailValidate thread operation (.node tail)⟩ :
      AtomicOccurrence Value)
  let linkEvent : TraceEvent Value := .atomic
    ⟨linkId, .enqueueLinkCAS thread operation tail node value .null true⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : linkEvent ∈ threadTrace trace thread := by
    simp [linkEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨leading, tailLoadId, nextLoadId, validationId, trailing,
      threadShape⟩ := run.enqueueLinkSuccess_context threadMember
  have localTailNext :
      [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [tailLoadEvent, nextLoadEvent]
  have localNextValidation :
      [nextLoadEvent nextLoadId, validationEvent validationId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    simp [nextLoadEvent, validationEvent]
  have localValidationLink :
      [validationEvent validationId, linkEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply List.Sublist.trans (l₂ :=
      [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId,
        validationEvent validationId, linkEvent])
    · simp
    · simp [tailLoadEvent, nextLoadEvent, validationEvent, linkEvent]
  have threadSublist :
      (threadTrace trace thread).Sublist trace :=
    List.filter_sublist
  have globalTailNext := localTailNext.trans threadSublist
  have globalNextValidation := localNextValidation.trans threadSublist
  have globalValidationLink := localValidationLink.trans threadSublist
  refine ⟨tailLoadId, nextLoadId, validationId, leading, trailing,
    threadShape, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalTailNext.subset (by simp [tailLoadEvent])
  · exact globalTailNext.subset (by simp [nextLoadEvent])
  · exact globalNextValidation.subset (by simp [validationEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalTailNext
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalNextValidation
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalValidationLink

/-- Global provenance of a successful enqueue-help Tail CAS. -/
theorem enqueueHelpTailSuccess_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    EnqueueHelpTailSuccessProvenance
      trace thread casId operation expected desired := by
  let tailLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueTailLoad thread operation (.node expected)⟩ :
      AtomicOccurrence Value)
  let nextLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueNextLoad thread operation expected (.node desired)⟩ :
      AtomicOccurrence Value)
  let validationEvent := fun id => TraceEvent.atomic
    (⟨id, .enqueueTailValidate thread operation (.node expected)⟩ :
      AtomicOccurrence Value)
  let casEvent : TraceEvent Value := .atomic
    ⟨casId, .enqueueHelpTailCAS thread operation expected desired
      (.node expected) true⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : casEvent ∈ threadTrace trace thread := by
    simp [casEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨leading, tailLoadId, nextLoadId, validationId, trailing,
      threadShape⟩ := run.enqueueHelpTailSuccess_context threadMember
  let block := [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId,
    validationEvent validationId, casEvent]
  have localTailNext :
      [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist (block := block) (by simp [block])
  have localNextValidation :
      [nextLoadEvent nextLoadId, validationEvent validationId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist (block := block) (by simp [block])
  have localValidationCAS :
      [validationEvent validationId, casEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply orderedBlock_sublist (block := block)
    change [validationEvent validationId, casEvent].Sublist
      [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId,
        validationEvent validationId, casEvent]
    exact (List.sublist_cons_self (nextLoadEvent nextLoadId) _).trans
      (List.sublist_cons_self (tailLoadEvent tailLoadId) _)
  have threadSublist : (threadTrace trace thread).Sublist trace :=
    List.filter_sublist
  have globalTailNext := localTailNext.trans threadSublist
  have globalNextValidation := localNextValidation.trans threadSublist
  have globalValidationCAS := localValidationCAS.trans threadSublist
  refine ⟨leading, tailLoadId, nextLoadId, validationId, trailing,
    threadShape, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalTailNext.subset (by simp [tailLoadEvent])
  · exact globalTailNext.subset (by simp [nextLoadEvent])
  · exact globalNextValidation.subset (by simp [validationEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalTailNext
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalNextValidation
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalValidationCAS

/-- Global provenance of a successful dequeue-help Tail CAS. -/
theorem dequeueHelpTailSuccess_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .dequeueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    DequeueHelpTailSuccessProvenance
      trace thread casId operation expected desired := by
  let headLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueHeadLoad thread operation (.node expected)⟩ :
      AtomicOccurrence Value)
  let tailLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueTailLoad thread operation (.node expected)⟩ :
      AtomicOccurrence Value)
  let nextLoadEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueNextLoad thread operation expected (.node desired)⟩ :
      AtomicOccurrence Value)
  let validationEvent := fun id => TraceEvent.atomic
    (⟨id, .dequeueHeadValidate thread operation (.node expected)⟩ :
      AtomicOccurrence Value)
  let casEvent : TraceEvent Value := .atomic
    ⟨casId, .dequeueHelpTailCAS thread operation expected desired
      (.node expected) true⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : casEvent ∈ threadTrace trace thread := by
    simp [casEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
      trailing, threadShape⟩ :=
    run.dequeueHelpTailSuccess_context threadMember
  let block := [headLoadEvent headLoadId, tailLoadEvent tailLoadId,
    nextLoadEvent nextLoadId, validationEvent validationId, casEvent]
  have localHeadTail :
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist (block := block) (by simp [block])
  have localTailNext :
      [tailLoadEvent tailLoadId, nextLoadEvent nextLoadId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist (block := block) (by simp [block])
  have localNextValidation :
      [nextLoadEvent nextLoadId, validationEvent validationId].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist (block := block) (by simp [block])
  have localValidationCAS :
      [validationEvent validationId, casEvent].Sublist
        (threadTrace trace thread) := by
    rw [threadShape]
    apply orderedBlock_sublist (block := block)
    change [validationEvent validationId, casEvent].Sublist
      [headLoadEvent headLoadId, tailLoadEvent tailLoadId,
        nextLoadEvent nextLoadId, validationEvent validationId, casEvent]
    exact (List.sublist_cons_self (nextLoadEvent nextLoadId) _).trans
      ((List.sublist_cons_self (tailLoadEvent tailLoadId) _).trans
        (List.sublist_cons_self (headLoadEvent headLoadId) _))
  have threadSublist : (threadTrace trace thread).Sublist trace :=
    List.filter_sublist
  have globalHeadTail := localHeadTail.trans threadSublist
  have globalTailNext := localTailNext.trans threadSublist
  have globalNextValidation := localNextValidation.trans threadSublist
  have globalValidationCAS := localValidationCAS.trans threadSublist
  refine ⟨leading, headLoadId, tailLoadId, nextLoadId, validationId,
    trailing, threadShape, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalHeadTail.subset (by simp [headLoadEvent])
  · exact globalHeadTail.subset (by simp [tailLoadEvent])
  · exact globalTailNext.subset (by simp [nextLoadEvent])
  · exact globalNextValidation.subset (by simp [validationEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalHeadTail
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalTailNext
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalNextValidation
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalValidationCAS

/-- Global provenance of a successful enqueue-finish Tail CAS. -/
theorem enqueueFinishTailSuccess_provenance
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueFinishTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    EnqueueFinishTailSuccessProvenance (Value := Value)
      trace thread casId operation expected desired := by
  let casEvent : TraceEvent Value := .atomic
    ⟨casId, .enqueueFinishTailCAS thread operation expected desired
      (.node expected) true⟩
  obtain ⟨final, run⟩ := wellFormed.threadRuns thread
  have threadMember : casEvent ∈ threadTrace trace thread := by
    simp [casEvent, threadTrace, member, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨value, leading, linkId, trailing, threadShape⟩ :=
    run.enqueueFinishTailSuccess_context threadMember
  let linkEvent : TraceEvent Value := .atomic
    ⟨linkId,
      .enqueueLinkCAS thread operation expected desired value .null true⟩
  have localLinkCAS : [linkEvent, casEvent].Sublist
      (threadTrace trace thread) := by
    rw [threadShape]
    exact orderedBlock_sublist
      (block := [linkEvent, casEvent]) (by simp)
  have globalLinkCAS := localLinkCAS.trans
    (List.filter_sublist : (threadTrace trace thread).Sublist trace)
  refine ⟨value, leading, linkId, trailing, threadShape, ?_, ?_⟩
  · exact globalLinkCAS.subset (by simp [linkEvent])
  · exact wellFormed.idBefore_of_atomicEvents_sublist globalLinkCAS

end SourceWellFormed

private theorem atomicOccurrence_mem_of_atomicEvent_mem
    {trace : List (TraceEvent Value)}
    {occurrence : AtomicOccurrence Value}
    (member : TraceEvent.atomic occurrence ∈ trace) :
    occurrence ∈ atomicOccurrences trace :=
  List.mem_filterMap.mpr ⟨.atomic occurrence, member, rfl⟩

namespace SupportedExecution

/-- Candidate-level form of the recovered control prefix: all three adjacent
same-attempt source pairs are genuine RC11 program-order edges. -/
theorem enqueueLinkSuccess_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread linkId operation node tail : Nat}
    {value : Value}
    (member :
      TraceEvent.atomic
        ⟨linkId, .enqueueLinkCAS thread operation tail node value .null true⟩
          ∈ trace) :
    ∃ tailLoadId nextLoadId validationId,
      MultiLocationRC11.PO execution.candidate
          (⟨tailLoadId,
            .enqueueTailLoad thread operation (.node tail)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨nextLoadId,
            .enqueueNextLoad thread operation tail .null⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨validationId,
            .enqueueTailValidate thread operation (.node tail)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨linkId,
            .enqueueLinkCAS thread operation tail node value .null true⟩ :
              AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨tailLoadId, nextLoadId, validationId, _leading, _trailing,
      _threadShape, tailLoadMember, nextLoadMember, validationMember,
      tailBeforeNext, nextBeforeValidation, validationBeforeLink⟩ :=
    execution.sourceWellFormed.enqueueLinkSuccess_provenance member
  refine ⟨tailLoadId, nextLoadId, validationId, ?_, ?_, ?_⟩
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      rfl tailBeforeNext
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      rfl nextBeforeValidation
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      (atomicOccurrence_mem_of_atomicEvent_mem member)
      rfl validationBeforeLink

/-- Typed program-order chain behind a successful enqueue-help Tail CAS. -/
theorem enqueueHelpTailSuccess_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    ∃ tailLoadId nextLoadId validationId,
      MultiLocationRC11.PO execution.candidate
          (⟨tailLoadId,
            .enqueueTailLoad thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨nextLoadId,
            .enqueueNextLoad thread operation expected (.node desired)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨validationId,
            .enqueueTailValidate thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨casId,
            .enqueueHelpTailCAS thread operation expected desired
              (.node expected) true⟩ : AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨_leading, tailLoadId, nextLoadId, validationId, _trailing,
      _threadShape, tailLoadMember, nextLoadMember, validationMember,
      tailBeforeNext, nextBeforeValidation, validationBeforeCAS⟩ :=
    execution.sourceWellFormed.enqueueHelpTailSuccess_provenance member
  refine ⟨tailLoadId, nextLoadId, validationId, ?_, ?_, ?_⟩
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      rfl tailBeforeNext
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      rfl nextBeforeValidation
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      (atomicOccurrence_mem_of_atomicEvent_mem member)
      rfl validationBeforeCAS

/-- Typed program-order chain behind a successful dequeue-help Tail CAS. -/
theorem dequeueHelpTailSuccess_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .dequeueHelpTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    ∃ headLoadId tailLoadId nextLoadId validationId,
      MultiLocationRC11.PO execution.candidate
          (⟨headLoadId,
            .dequeueHeadLoad thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨tailLoadId,
            .dequeueTailLoad thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨nextLoadId,
            .dequeueNextLoad thread operation expected (.node desired)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        MultiLocationRC11.PO execution.candidate
          (⟨validationId,
            .dequeueHeadValidate thread operation (.node expected)⟩ :
              AtomicOccurrence Value).toRC11Atom
          (⟨casId,
            .dequeueHelpTailCAS thread operation expected desired
              (.node expected) true⟩ : AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨_leading, headLoadId, tailLoadId, nextLoadId, validationId,
      _trailing, _threadShape, headLoadMember, tailLoadMember, nextLoadMember,
      validationMember, headBeforeTail, tailBeforeNext,
      nextBeforeValidation, validationBeforeCAS⟩ :=
    execution.sourceWellFormed.dequeueHelpTailSuccess_provenance member
  refine ⟨headLoadId, tailLoadId, nextLoadId, validationId,
    ?_, ?_, ?_, ?_⟩
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem headLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      rfl headBeforeTail
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem tailLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      rfl tailBeforeNext
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem nextLoadMember)
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      rfl nextBeforeValidation
  · exact execution.programOrder_of_atomicIdBefore
      (atomicOccurrence_mem_of_atomicEvent_mem validationMember)
      (atomicOccurrence_mem_of_atomicEvent_mem member)
      rfl validationBeforeCAS

/-- Typed program-order edge from the successful link to its finishing Tail
CAS; the source distinction from enqueue-help remains explicit. -/
theorem enqueueFinishTailSuccess_programOrder
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (execution : SupportedExecution (Value := Value) dummy trace)
    {thread casId operation expected desired : Nat}
    (member :
      TraceEvent.atomic
        ⟨casId,
          .enqueueFinishTailCAS thread operation expected desired
            (.node expected) true⟩ ∈ trace) :
    ∃ (value : Value), ∃ linkId,
      MultiLocationRC11.PO execution.candidate
        (⟨linkId,
          .enqueueLinkCAS thread operation expected desired value .null true⟩ :
            AtomicOccurrence Value).toRC11Atom
        (⟨casId,
          .enqueueFinishTailCAS thread operation expected desired
            (.node expected) true⟩ : AtomicOccurrence Value).toRC11Atom := by
  obtain ⟨value, _leading, linkId, _trailing, _threadShape, linkMember,
      linkBeforeCAS⟩ :=
    execution.sourceWellFormed.enqueueFinishTailSuccess_provenance member
  exact ⟨value, linkId, execution.programOrder_of_atomicIdBefore
    (atomicOccurrence_mem_of_atomicEvent_mem linkMember)
    (atomicOccurrence_mem_of_atomicEvent_mem member)
    rfl linkBeforeCAS⟩

end SupportedExecution

end WeakMemory.MSQueue.Source
