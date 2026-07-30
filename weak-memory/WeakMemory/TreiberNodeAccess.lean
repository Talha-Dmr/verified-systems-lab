import WeakMemory.TreiberControlledCandidate

namespace WeakMemory.TreiberRC11

/-!
# Publication safety for Treiber node-field reads

The atomic-head graph deliberately excludes non-atomic `node->next` accesses.
Those accesses remain source positions in `TreiberControlFlow`. This module
states and proves the graph half of the C11 publication argument:

```text
successful push CAS (release publisher)
              ↓ release sequence
atomic write read by the acquire observer
              ↓ reads-from
pop load or failed pop CAS (acquire observer)
```

The source layer separately proves `writeNext` is sequenced before the release
publisher and that the acquire observer is sequenced before the corresponding
`readNext`. A later successful pop CAS is not accepted as the observer for an
earlier field read.
-/

namespace Event

/--
An acquire atomic event whose non-null result is used by the next pop
iteration to dereference `node->next`.
-/
inductive IsDereferenceObserver
    (node : TreiberRA.NodeId) :
    Event α → Prop where
  | popLoad (id thread : Nat) :
      IsDereferenceObserver node
        (Event.mk id
          (.algorithm (.popLoad thread (some node))))
  | popFailure
      (id thread expected : Nat) :
      IsDereferenceObserver node
        (Event.mk id
          (.algorithm
            (.popFailure thread (some expected) (some node))))

/-- Every dereference observer reads the selected non-null node. -/
theorem IsDereferenceObserver.readValue
    {event : Event α}
    {node : TreiberRA.NodeId}
    (observer : event.IsDereferenceObserver node) :
    event.readValue = some (some node) := by
  cases observer <;> rfl

/-- Every dereference observer has acquire semantics in `c/treiber.c`. -/
theorem IsDereferenceObserver.hasAcquire
    {event : Event α}
    {node : TreiberRA.NodeId}
    (observer : event.IsDereferenceObserver node) :
    event.order.hasAcquire = true := by
  cases observer <;> rfl

/-- A local control-flow authorization produces the matching graph shape. -/
theorem isDereferenceObserver_of_authorized
    {thread : Nat}
    {node : TreiberRA.NodeId}
    {action : TreiberRA.Action α}
    (id : EventId)
    (authorized :
      ControlFlow.AuthorizesReadNext thread node action) :
    (Event.mk id (.algorithm action) : Event α)
      |>.IsDereferenceObserver node := by
  cases authorized with
  | popLoad =>
      exact .popLoad id thread
  | popFailure expected =>
      exact .popFailure id thread expected

/-- Every allocator event is the release successful push that publishes it. -/
theorem hasRelease_of_allocation
    {event : Event α}
    {nodeId : TreiberRA.NodeId}
    {node : TreiberRA.Node α}
    (allocation :
      event.allocation? = some (nodeId, node)) :
    event.order.hasRelease = true := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          simp [Event.allocation?] at allocation
      | algorithm action =>
          cases action <;>
            simp [Event.allocation?, Event.order,
              TreiberRA.Action.order] at allocation ⊢

end Event

/--
A proof that one acquire observer obtained a published node through the
publisher's release sequence.

The reads-from source need not be the original publisher. A later successful
CAS may re-expose the same node while remaining in the release sequence.
-/
structure PublishedObservation
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (typing : GraphTyping graph initial)
    (observer : Event α)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId) where
  publisher :
    Event α
  readsFromSource :
    Event α
  value :
    α
  recorded :
    typing.allocator node =
      some (publisher, { value := value, next := next })
  observerShape :
    observer.IsDereferenceObserver node
  releaseSequence :
    graph.ReleaseSequence publisher readsFromSource
  readsFrom :
    graph.readsFrom readsFromSource observer

namespace PublishedObservation

/-- The allocator table proves that the publisher is in the graph carrier. -/
theorem publisherMember
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    publication.publisher ∈ graph.events :=
  (typing.allocatorSound publication.recorded).1

/-- The publisher allocates the exact immutable node read by the source. -/
theorem publisherAllocation
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    publication.publisher.allocation? =
      some
        (node,
          { value := publication.value, next := next }) :=
  (typing.allocatorSound publication.recorded).2

/-- The unique allocator publisher has release semantics. -/
theorem publisherReleases
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    publication.publisher.order.hasRelease = true :=
  Event.hasRelease_of_allocation
    publication.publisherAllocation

/-- The observer has acquire semantics. -/
theorem observerAcquires
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    observer.order.hasAcquire = true :=
  publication.observerShape.hasAcquire

/-- The release-sequence witness is exactly a graph synchronizes-with edge. -/
theorem synchronizesWith
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    graph.synchronizesWith publication.publisher observer :=
  ⟨publication.readsFromSource,
    publication.releaseSequence,
    publication.readsFrom,
    publication.publisherReleases,
    publication.observerAcquires⟩

/-- Publication happens before the acquire observer in the atomic graph. -/
theorem happensBefore
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (publication :
      PublishedObservation typing observer node next) :
    graph.HappensBefore publication.publisher observer :=
  Graph.HappensBefore.synchronizesWith
    publication.synchronizesWith

/--
Publication also precedes the observer in extended coherence, which makes the
edge visible to every existing respecting replay schedule. This conclusion is
weaker than synchronizes-with and is not used as a substitute for field-access
safety.
-/
theorem extendedCoherence
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {observer : Event α}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (wellFormed : WellFormed graph)
    (publication :
      PublishedObservation typing observer node next) :
    graph.ExtendedCoherence publication.publisher observer := by
  rcases publication.releaseSequence.equalOrPrecedes wellFormed with
    sameSource | publisherBeforeSource
  · have publisherReadsFrom :
        graph.readsFrom publication.publisher observer := by
      rw [sameSource]
      exact publication.readsFrom
    exact Graph.ExtendedCoherence.readsFrom
      publisherReadsFrom
  · exact Graph.ExtendedCoherence.transitive
      (Graph.ExtendedCoherence.modificationOrder
        publisherBeforeSource)
      (Graph.ExtendedCoherence.readsFrom
        publication.readsFrom)

end PublishedObservation

/--
Happens-before over source occurrences, retaining non-atomic labels while
embedding synchronization from their numbered atomic projections.
-/
inductive SourceHappensBefore
    (graph : Graph α)
    (skeleton : EventGraph.Skeleton α) :
    Relation (EventGraph.SourceOccurrence skeleton) where
  | sequencedBefore {first second} :
      first.SequencedBefore second →
      SourceHappensBefore graph skeleton first second
  | atomicSynchronization
      {first second}
      {firstEvent secondEvent : Event α} :
      skeleton.atomicEventAtOccurrence first = some firstEvent →
      skeleton.atomicEventAtOccurrence second = some secondEvent →
      graph.synchronizesWith firstEvent secondEvent →
      SourceHappensBefore graph skeleton first second
  | transitive {first middle last} :
      SourceHappensBefore graph skeleton first middle →
      SourceHappensBefore graph skeleton middle last →
      SourceHappensBefore graph skeleton first last

/--
Complete publication chain for one selected source `readNext`.

The immutable allocator record makes the field value exact. The three order
segments are the C11 chain `writeNext sb release ; sw acquire ; sb readNext`.
-/
structure VisibleNextWrite
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (typing : GraphTyping graph initial)
    (skeleton : EventGraph.Skeleton α)
    (fieldRead : EventGraph.SourceOccurrence skeleton)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId) where
  fieldWrite :
    EventGraph.SourceOccurrence skeleton
  publisher :
    EventGraph.SourceOccurrence skeleton
  observer :
    EventGraph.SourceOccurrence skeleton
  observerEvent :
    Event α
  publication :
    PublishedObservation typing observerEvent node next
  fieldWriteBeforePublisher :
    fieldWrite.SequencedBefore publisher
  observerBeforeFieldRead :
    observer.SequencedBefore fieldRead
  publisherProjects :
    skeleton.atomicEventAtOccurrence publisher =
      some publication.publisher
  observerProjects :
    skeleton.atomicEventAtOccurrence observer =
      some observerEvent
  fieldWriteLabel :
    ∃ operation,
      fieldWrite.selected.label =
        .writeNext operation node next
  fieldReadLabel :
    ∃ operation,
      fieldRead.selected.label =
        .readNext operation node next

namespace VisibleNextWrite

/-- The full source-level publication chain happens before the field read. -/
theorem happensBefore
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {typing : GraphTyping graph initial}
    {skeleton : EventGraph.Skeleton α}
    {fieldRead : EventGraph.SourceOccurrence skeleton}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (visible :
      VisibleNextWrite typing skeleton fieldRead node next) :
    SourceHappensBefore graph skeleton
      visible.fieldWrite fieldRead := by
  apply SourceHappensBefore.transitive
    (SourceHappensBefore.sequencedBefore
      visible.fieldWriteBeforePublisher)
  apply SourceHappensBefore.transitive
    (SourceHappensBefore.atomicSynchronization
      visible.publisherProjects
      visible.observerProjects
      visible.publication.synchronizesWith)
  exact SourceHappensBefore.sequencedBefore
    visible.observerBeforeFieldRead

end VisibleNextWrite

/-- Every modeled non-atomic `next` read has a complete visible-write chain. -/
def AllNextReadsHaveVisibleWrite
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (typing : GraphTyping graph initial)
    (skeleton : EventGraph.Skeleton α) : Prop :=
  ∀ (fieldRead : EventGraph.SourceOccurrence skeleton)
    (operation : ControlFlow.OperationId)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId),
    fieldRead.selected.label =
        .readNext operation node next →
      Nonempty
        (VisibleNextWrite
          typing skeleton fieldRead node next)

/--
The node-access certificate attached to a controlled source candidate.

This field is deliberately separate from `RemainingConsistency`: it is the
source/non-atomic obligation that a later RF/MO constructor must derive.
-/
structure NodeAccessCertificate
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (candidate : ControlledCandidate graph initial) : Prop where
  allNextReads :
    AllNextReadsHaveVisibleWrite
      candidate.toGraphTyping
      candidate.source.skeleton

namespace NodeAccessCertificate

/--
Every selected field read has an exact source write that happens before it in
the mixed source/atomic relation.
-/
theorem visibleWrite
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {candidate : ControlledCandidate graph initial}
    (certificate : NodeAccessCertificate candidate)
    (fieldRead :
      EventGraph.SourceOccurrence
        candidate.source.skeleton)
    (operation : ControlFlow.OperationId)
    (node : TreiberRA.NodeId)
    (next : Option TreiberRA.NodeId)
    (readLabel :
      fieldRead.selected.label =
        .readNext operation node next) :
    ∃ fieldWrite :
        EventGraph.SourceOccurrence
          candidate.source.skeleton,
      (∃ pushOperation,
        fieldWrite.selected.label =
          .writeNext pushOperation node next) ∧
      SourceHappensBefore graph
        candidate.source.skeleton
        fieldWrite fieldRead := by
  obtain ⟨visible⟩ :=
    certificate.allNextReads
      fieldRead operation node next readLabel
  exact ⟨visible.fieldWrite,
    visible.fieldWriteLabel,
    visible.happensBefore⟩

end NodeAccessCertificate

end WeakMemory.TreiberRC11
