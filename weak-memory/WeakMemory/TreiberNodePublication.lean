import WeakMemory.TreiberNodeOrigin
import WeakMemory.TreiberReleaseSequence

namespace WeakMemory.TreiberRC11

/-!
# Deriving node publication from canonical RF/MO data

This module closes the graph half of the non-atomic dereference argument.
Given only source-level agreement between `readNext` and the immutable
allocator table, the canonical graph now derives:

* the exact preceding acquire observer;
* its unique reads-from source;
* the original release push that allocated the node;
* a complete RMW release sequence from that publisher to the reads-from
  source;
* synchronizes-with and happens-before from publisher to observer.
-/

namespace Event

/-- An allocator event is a non-initial atomic write. -/
theorem write_notInitial_of_allocation
    {event : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (allocation :
      event.allocation? = some (nodeId, node)) :
    event.IsWrite ∧ ¬ event.IsInitial := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp [Event.allocation?] at allocation
      | algorithm action =>
          cases action <;>
            simp [Event.allocation?, Event.IsWrite,
              Event.writtenValue, Event.IsInitial]
              at allocation ⊢

/-- A write of a non-null node cannot be the null initializer. -/
theorem notInitial_of_writesNode
    {event : Event α}
    {node : TreiberRA.NodeId}
    (writesNode :
      event.writtenValue = some (some node)) :
    ¬ event.IsInitial := by
  intro initial
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp [Event.writtenValue] at writesNode
      | algorithm action =>
          simp [Event.IsInitial] at initial

end Event

namespace ReadNextAtomicObservation

/--
The canonical relation data turns one source/observer witness into the full
release-sequence publication witness.
-/
def toPublishedObservation
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    {fieldRead :
      EventGraph.SourceOccurrence
        execution.source.skeleton}
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (observation :
      ReadNextAtomicObservation
        execution fieldRead operation node next) :
    PublishedObservation
      execution.toGraphTyping
      observation.observerEvent node next := by
  let typing := execution.toGraphTyping
  have publisherSound :=
    typing.allocatorSound observation.allocatorRecord
  have publisherMember :
      observation.publisher ∈
        execution.relations.graph.events :=
    publisherSound.1
  have publisherAllocation :
      observation.publisher.allocation? =
        some
          (node,
            { value := observation.payload, next := next }) :=
    publisherSound.2
  have publisherWriteAndNotInitial :=
    Event.write_notInitial_of_allocation
      publisherAllocation
  have sourceWrites :
      observation.readsFromSource.IsWrite :=
    ⟨some node, observation.readsFromSourceValue⟩
  have sourceNotInitial :
      ¬ observation.readsFromSource.IsInitial :=
    Event.notInitial_of_writesNode
      observation.readsFromSourceValue
  have publisherOrdered :=
    execution.allocatorPublisher_eq_or_precedes_writer
      observation.allocatorRecord
      observation.readsFromSourceMember
      observation.readsFromSourceValue
  have releaseSequence :
      execution.relations.graph.ReleaseSequence
        observation.publisher
        observation.readsFromSource :=
    execution.relations
      |>.releaseSequence_of_eq_or_modificationOrder
        publisherMember
        publisherWriteAndNotInitial.1
        publisherWriteAndNotInitial.2
        observation.readsFromSourceMember
        sourceWrites
        sourceNotInitial
        publisherOrdered
  exact {
    publisher :=
      observation.publisher
    readsFromSource :=
      observation.readsFromSource
    value :=
      observation.payload
    recorded :=
      observation.allocatorRecord
    observerShape :=
      observation.observerShape
    releaseSequence :=
      releaseSequence
    readsFrom :=
      observation.readsFrom
  }

end ReadNextAtomicObservation

namespace SourceAtomicExecution

/--
Every modeled `readNext` derives a complete publication witness from canonical
RF/MO data and source-level immutable-field agreement.
-/
theorem readNextPublishedObservation
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
    ∃ observerEvent,
      Nonempty
        (PublishedObservation
          execution.toGraphTyping
          observerEvent node next) := by
  obtain ⟨observation⟩ :=
    execution.readNextAtomicObservation
      valueCertificate fieldRead operation node next readLabel
  exact ⟨observation.observerEvent,
    ⟨observation.toPublishedObservation⟩⟩

end SourceAtomicExecution

end WeakMemory.TreiberRC11
