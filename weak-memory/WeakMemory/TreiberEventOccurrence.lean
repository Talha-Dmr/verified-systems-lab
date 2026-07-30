import WeakMemory.TreiberNodePublication

namespace WeakMemory.TreiberRC11

/-!
# Recovering source occurrences from canonical events

`EventGraph.atomicEventsFrom` forgets invocation and non-atomic field-access
labels while numbering atomic-head labels.  This module proves the inverse
membership direction: every numbered event identifies an exact source-list
occurrence, including the operation identifier and action stored in its atomic
label.

The witness is an `EventGraph.SourceOccurrence`, not merely membership of an
equal label.  Its prefix and suffix therefore keep repeated equal retry labels
as separate occurrences.
-/

namespace EventGraph

/--
Every member produced by `atomicEventsFrom` comes from one exact atomic source
occurrence.  The prefix determines the event identifier through the number of
earlier atomic labels.
-/
theorem atomicEventsFrom_inverse
    {next : EventId}
    {labels : List (OwnedLabel α)}
    {event : Event α}
    (member : event ∈ atomicEventsFrom next labels) :
    ∃ leading selected trailing operation action,
      labels = leading ++ selected :: trailing ∧
        selected.label = .atomic operation action ∧
        Event.mk
            (next + atomicLabelCount leading)
            (.algorithm action) =
          event := by
  induction labels generalizing next event with
  | nil =>
      simp [atomicEventsFrom] at member
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          obtain ⟨leading, selected, trailing, sourceOperation,
              action, labelsShape, labelShape, eventShape⟩ :=
            inductionHypothesis (next := next) member
          refine ⟨
            { thread := thread
              label := .invokePush operation reserved value
              owned := ownership } :: leading,
            selected, trailing, sourceOperation, action,
            ?_, labelShape, ?_⟩
          · simp [labelsShape]
          · simpa [atomicLabelCount] using eventShape
      | invokePop operation =>
          obtain ⟨leading, selected, trailing, sourceOperation,
              action, labelsShape, labelShape, eventShape⟩ :=
            inductionHypothesis (next := next) member
          refine ⟨
            { thread := thread
              label := .invokePop operation
              owned := ownership } :: leading,
            selected, trailing, sourceOperation, action,
            ?_, labelShape, ?_⟩
          · simp [labelsShape]
          · simpa [atomicLabelCount] using eventShape
      | invokeIsEmpty operation =>
          obtain ⟨leading, selected, trailing, sourceOperation,
              action, labelsShape, labelShape, eventShape⟩ :=
            inductionHypothesis (next := next) member
          refine ⟨
            { thread := thread
              label := .invokeIsEmpty operation
              owned := ownership } :: leading,
            selected, trailing, sourceOperation, action,
            ?_, labelShape, ?_⟩
          · simp [labelsShape]
          · simpa [atomicLabelCount] using eventShape
      | writeNext operation node nextValue =>
          obtain ⟨leading, selected, trailing, sourceOperation,
              action, labelsShape, labelShape, eventShape⟩ :=
            inductionHypothesis (next := next) member
          refine ⟨
            { thread := thread
              label := .writeNext operation node nextValue
              owned := ownership } :: leading,
            selected, trailing, sourceOperation, action,
            ?_, labelShape, ?_⟩
          · simp [labelsShape]
          · simpa [atomicLabelCount] using eventShape
      | readNext operation node nextValue =>
          obtain ⟨leading, selected, trailing, sourceOperation,
              action, labelsShape, labelShape, eventShape⟩ :=
            inductionHypothesis (next := next) member
          refine ⟨
            { thread := thread
              label := .readNext operation node nextValue
              owned := ownership } :: leading,
            selected, trailing, sourceOperation, action,
            ?_, labelShape, ?_⟩
          · simp [labelsShape]
          · simpa [atomicLabelCount] using eventShape
      | atomic operation action =>
          simp only [atomicEventsFrom, List.mem_cons] at member
          rcases member with isHead | inRest
          · subst event
            refine ⟨[],
              { thread := thread
                label := .atomic operation action
                owned := ownership },
              rest, operation, action, rfl, rfl, ?_⟩
            simp [atomicLabelCount]
          · obtain ⟨leading, selected, trailing, sourceOperation,
                laterAction, labelsShape, labelShape, eventShape⟩ :=
              inductionHypothesis (next := next + 1) inRest
            refine ⟨
              { thread := thread
                label := .atomic operation action
                owned := ownership } :: leading,
              selected, trailing, sourceOperation, laterAction,
              ?_, labelShape, ?_⟩
            · simp [labelsShape]
            · simpa [atomicLabelCount, Nat.add_assoc] using eventShape

namespace Skeleton

/--
Every non-initial carrier event is the projection of an exact atomic source
occurrence, retaining both its operation identifier and action.
-/
theorem exists_sourceOccurrence_of_mem_notInitial
    (skeleton : Skeleton α)
    {event : Event α}
    (member : event ∈ skeleton.events)
    (notInitial : ¬ event.IsInitial) :
    ∃ occurrence : SourceOccurrence skeleton,
      ∃ operation action,
        occurrence.selected.label =
            .atomic operation action ∧
          skeleton.atomicEventAtOccurrence occurrence =
            some event := by
  simp only [events, List.mem_cons] at member
  rcases member with isInitial | inAtomic
  · subst event
    exact (notInitial (by trivial)).elim
  · obtain ⟨leading, selected, trailing, operation, action,
        labelsShape, labelShape, eventShape⟩ :=
      atomicEventsFrom_inverse (next := 1) inAtomic
    let occurrence : SourceOccurrence skeleton := {
      leading := leading
      selected := selected
      trailing := trailing
      labelsShape := labelsShape
    }
    refine ⟨occurrence, operation, action, labelShape, ?_⟩
    simpa [atomicEventAtOccurrence, occurrence, labelShape,
      atomicEventAt] using congrArg some eventShape

/--
The event identifier exposes an atomic occurrence's ordinal.  Thus equal
action labels at different atomic ordinals are not collapsed by projection.
-/
theorem event_id_of_atomicOccurrence
    (skeleton : Skeleton α)
    (occurrence : SourceOccurrence skeleton)
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    {event : Event α}
    (labelShape :
      occurrence.selected.label =
        .atomic operation action)
    (projects :
      skeleton.atomicEventAtOccurrence occurrence =
        some event) :
    event.id = 1 + atomicLabelCount occurrence.leading := by
  have eventShape :
      atomicEventAt occurrence.leading action = event := by
    simpa [atomicEventAtOccurrence, labelShape] using projects
  rw [← eventShape]
  rfl

/--
Two projected atomic occurrences with different atomic ordinals yield
different events, even when their operation/action labels are definitionally
equal.
-/
theorem atomicOccurrences_project_ne_of_count_ne
    (skeleton : Skeleton α)
    (first second : SourceOccurrence skeleton)
    {firstOperation secondOperation : ControlFlow.OperationId}
    {firstAction secondAction : TreiberRA.Action α}
    {firstEvent secondEvent : Event α}
    (firstLabel :
      first.selected.label =
        .atomic firstOperation firstAction)
    (secondLabel :
      second.selected.label =
        .atomic secondOperation secondAction)
    (firstProjects :
      skeleton.atomicEventAtOccurrence first =
        some firstEvent)
    (secondProjects :
      skeleton.atomicEventAtOccurrence second =
        some secondEvent)
    (differentOrdinals :
      atomicLabelCount first.leading ≠
        atomicLabelCount second.leading) :
    firstEvent ≠ secondEvent := by
  intro sameEvent
  apply differentOrdinals
  have sameId :
      firstEvent.id = secondEvent.id :=
    congrArg Event.id sameEvent
  rw [
    event_id_of_atomicOccurrence
      skeleton first firstLabel firstProjects,
    event_id_of_atomicOccurrence
      skeleton second secondLabel secondProjects
  ] at sameId
  exact Nat.add_left_cancel sameId

end Skeleton

end EventGraph

namespace SourceAtomicExecution

/--
Every non-initial event of a canonical source execution recovers an exact
atomic occurrence from the source skeleton.  The lift is exact because the
canonical graph carrier is definitionally the skeleton carrier.
-/
theorem exists_sourceOccurrence_of_mem_notInitial
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {event : Event α}
    (member : event ∈ execution.relations.graph.events)
    (notInitial : ¬ event.IsInitial) :
    ∃ occurrence :
        EventGraph.SourceOccurrence execution.source.skeleton,
      ∃ operation action,
        occurrence.selected.label =
            .atomic operation action ∧
          execution.source.skeleton.atomicEventAtOccurrence occurrence =
            some event := by
  apply
    EventGraph.Skeleton.exists_sourceOccurrence_of_mem_notInitial
      execution.source.skeleton
  · simpa using member
  · exact notInitial

end SourceAtomicExecution

end WeakMemory.TreiberRC11
