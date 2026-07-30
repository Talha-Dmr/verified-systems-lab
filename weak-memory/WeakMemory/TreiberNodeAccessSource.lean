import WeakMemory.TreiberSourceExecution

namespace WeakMemory.TreiberRC11

/-!
# Source reads and their canonical atomic observers

This module connects a selected non-atomic `readNext` occurrence to the
canonical atomic graph of a `SourceAtomicExecution`.

The source certificate below states only that the `(node, next)` pair read by
the source agrees with the final functional allocator table. Local
control-flow supplies the exact preceding acquire observer. Numbering supplies
its canonical graph event, and derived graph well-formedness supplies the
observer's unique reads-from source and value.

No release-sequence or publisher-synchronization claim is made here.
-/

/--
Every modeled `readNext` returns the immutable `next` value recorded for its
node in the final allocator table.
-/
structure NextReadValueCertificate
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) : Prop where
  matchesAllocator :
    ∀ (fieldRead :
          EventGraph.SourceOccurrence
            execution.source.skeleton)
      (operation : ControlFlow.OperationId)
      (node : TreiberRA.NodeId)
      (next : Option TreiberRA.NodeId),
      fieldRead.selected.label =
          .readNext operation node next →
        ∃ publisher payload,
          execution.allocator node =
            some
              (publisher,
                { value := payload, next := next })

/--
The complete source-to-atomic information available before proving
publication through a release sequence.

`observer` is the exact local predecessor selected by source control flow.
`observerEvent` is its numbered event in the canonical graph.
`readsFromSource` is the unique graph write chosen for that observer.
-/
structure ReadNextAtomicObservation
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (fieldRead :
      EventGraph.SourceOccurrence
        execution.source.skeleton)
    (operation : ControlFlow.OperationId)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId) where
  readLabel :
    fieldRead.selected.label =
      .readNext operation node next
  publisher :
    Event α
  payload :
    α
  allocatorRecord :
    execution.allocator node =
      some
        (publisher,
          { value := payload, next := next })
  observer :
    EventGraph.SourceOccurrence
      execution.source.skeleton
  observerBeforeFieldRead :
    observer.SequencedBefore fieldRead
  observerAction :
    TreiberRA.Action α
  observerLabel :
    observer.selected.label =
      .atomic operation observerAction
  observerAuthorizes :
    ControlFlow.AuthorizesReadNext
      fieldRead.selected.thread node observerAction
  observerEvent :
    Event α
  observerProjects :
    execution.source.skeleton.atomicEventAtOccurrence observer =
      some observerEvent
  observerMember :
    observerEvent ∈ execution.relations.graph.events
  observerShape :
    observerEvent.IsDereferenceObserver node
  readsFromSource :
    Event α
  readsFrom :
    execution.relations.graph.readsFrom
      readsFromSource observerEvent
  readsFromSourceMember :
    readsFromSource ∈ execution.relations.graph.events
  readsFromSourceValue :
    readsFromSource.writtenValue = some (some node)
  readsFromSourceUnique :
    ∀ {other : Event α},
      execution.relations.graph.readsFrom other observerEvent →
      other = readsFromSource

namespace SourceAtomicExecution

/--
Every selected source `readNext` has an exact preceding acquire observer in
the canonical graph, and that observer has one unique reads-from source
writing the selected non-null node.

This theorem deliberately stops before establishing that the allocator
publisher heads a release sequence reaching `readsFromSource`.
-/
theorem readNextAtomicObservation
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (valueCertificate : NextReadValueCertificate execution)
    (fieldRead :
      EventGraph.SourceOccurrence
        execution.source.skeleton)
    (operation : ControlFlow.OperationId)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId)
    (readLabel :
      fieldRead.selected.label =
        .readNext operation node next) :
    Nonempty
      (ReadNextAtomicObservation
        execution fieldRead operation node next) := by
  obtain ⟨publisher, payload, allocatorRecord⟩ :=
    valueCertificate.matchesAllocator
      fieldRead operation node next readLabel
  obtain ⟨observer, observerBeforeFieldRead,
      observerAction, observerLabel, observerAuthorizes⟩ :=
    execution.source.valid.readNextOccurrence_hasObserver
      fieldRead rfl readLabel
  let observerEvent : Event α :=
    EventGraph.Skeleton.atomicEventAt
      observer.leading observerAction
  have observerProjects :
      execution.source.skeleton.atomicEventAtOccurrence observer =
        some observerEvent := by
    simp [EventGraph.Skeleton.atomicEventAtOccurrence,
      observerEvent, observerLabel]
  have observerMember :
      observerEvent ∈ execution.relations.graph.events := by
    simpa using
      execution.source.skeleton.atomicEventAtOccurrence_mem
        observer observerProjects
  have observerShape :
      observerEvent.IsDereferenceObserver node := by
    simpa [observerEvent,
      EventGraph.Skeleton.atomicEventAt] using
      Event.isDereferenceObserver_of_authorized
        (1 + EventGraph.atomicLabelCount observer.leading)
        observerAuthorizes
  have wellFormed :
      WellFormed execution.relations.graph :=
    execution.toCoreConsistent.toWellFormed
  have observerReads : observerEvent.IsRead :=
    ⟨some node, observerShape.readValue⟩
  obtain ⟨readsFromSource, readsFrom⟩ :=
    wellFormed.everyReadHasSource
      observerMember observerReads
  obtain ⟨readValue, sourceWrites, observerReadsValue⟩ :=
    wellFormed.readsFromValues readsFrom
  have readValueShape : readValue = some node :=
    Option.some.inj
      (observerReadsValue.symm.trans observerShape.readValue)
  subst readValue
  have readsFromSourceMember :
      readsFromSource ∈ execution.relations.graph.events :=
    (wellFormed.readsFromClosed readsFrom).1
  refine ⟨{
    readLabel := readLabel
    publisher := publisher
    payload := payload
    allocatorRecord := allocatorRecord
    observer := observer
    observerBeforeFieldRead := observerBeforeFieldRead
    observerAction := observerAction
    observerLabel := observerLabel
    observerAuthorizes := observerAuthorizes
    observerEvent := observerEvent
    observerProjects := observerProjects
    observerMember := observerMember
    observerShape := observerShape
    readsFromSource := readsFromSource
    readsFrom := readsFrom
    readsFromSourceMember := readsFromSourceMember
    readsFromSourceValue := sourceWrites
    readsFromSourceUnique := ?_
  }⟩
  intro other otherReadsFrom
  exact wellFormed.readsFromFunctional
    otherReadsFrom readsFrom

end SourceAtomicExecution

end WeakMemory.TreiberRC11
