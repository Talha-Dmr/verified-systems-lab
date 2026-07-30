import WeakMemory.TreiberEventOccurrence

namespace WeakMemory.TreiberRC11

/-!
# Deriving source-level node-access safety

The canonical atomic relation data already derives a published acquire
observation for every modeled `readNext`.  This module connects that graph
witness back to the exact source occurrence of the allocating release push and
then to its preceding non-atomic `writeNext`.
-/

namespace SourceAtomicExecution

/--
Canonical relation data and immutable-field agreement derive the complete
source/atomic visibility certificate for every modeled `node->next` read.
-/
theorem toNodeAccessCertificate
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (valueCertificate : NextReadValueCertificate execution) :
    NodeAccessCertificate execution.toControlledCandidate := by
  refine { allNextReads := ?_ }
  intro fieldRead operation node next readLabel
  obtain ⟨observation⟩ :=
    execution.readNextAtomicObservation
      valueCertificate fieldRead operation node next readLabel
  let publication :
      PublishedObservation
        execution.toGraphTyping
        observation.observerEvent node next :=
    observation.toPublishedObservation
  have publisherAllocation :
      publication.publisher.allocation? =
        some
          (node,
            { value := publication.value, next := next }) :=
    publication.publisherAllocation
  have publisherNotInitial :
      ¬ publication.publisher.IsInitial :=
    (Event.write_notInitial_of_allocation
      publisherAllocation).2
  obtain ⟨publisherOccurrence, publisherOperation,
      publisherAction, publisherLabel, publisherProjects⟩ :=
    execution.exists_sourceOccurrence_of_mem_notInitial
      publication.publisherMember publisherNotInitial
  have publisherEventShape :
      EventGraph.Skeleton.atomicEventAt
          publisherOccurrence.leading publisherAction =
        publication.publisher := by
    simpa [
      EventGraph.Skeleton.atomicEventAtOccurrence,
      publisherLabel
    ] using publisherProjects
  have sourceAllocation :
      (EventGraph.Skeleton.atomicEventAt
          publisherOccurrence.leading publisherAction).allocation? =
        some
          (node,
            { value := publication.value, next := next }) := by
    rw [publisherEventShape]
    exact publisherAllocation
  cases publisherAction with
  | pushLoad thread observed =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | popLoad thread observed =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | isEmptyLoad thread observed =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | pushSuccess thread reserved value expected =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
      rcases sourceAllocation with
        ⟨reservedShape, valueShape, expectedShape⟩
      subst reserved
      subst value
      subst expected
      have publisherThread :
          publisherOccurrence.selected.thread = thread :=
        (publisherOccurrence.selected.atomic_actionThread
          publisherLabel).symm
      obtain ⟨fieldWrite, fieldWriteBeforePublisher,
          fieldWriteLabel⟩ :=
        execution.source.valid.pushSuccessOccurrence_hasNextWrite
          publisherOccurrence publisherThread publisherLabel
      exact ⟨{
        fieldWrite := fieldWrite
        publisher := publisherOccurrence
        observer := observation.observer
        observerEvent := observation.observerEvent
        publication := publication
        fieldWriteBeforePublisher := fieldWriteBeforePublisher
        observerBeforeFieldRead :=
          observation.observerBeforeFieldRead
        publisherProjects := publisherProjects
        observerProjects := observation.observerProjects
        fieldWriteLabel := ⟨publisherOperation, fieldWriteLabel⟩
        fieldReadLabel := ⟨operation, readLabel⟩
      }⟩
  | pushFailure thread reserved value expected actual =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | popSuccess thread removed value nextPointer =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | popFailure thread expected actual =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation
  | popEmpty thread =>
      simp [EventGraph.Skeleton.atomicEventAt,
        Event.allocation?] at sourceAllocation

/--
Package a canonical atomic execution as a C-shaped execution without asking a
caller to construct a separate publication certificate.
-/
def toCSourceExecution
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    (valueCertificate : NextReadValueCertificate execution) :
    CSourceExecution initial where
  atomic := execution
  nodeAccess := execution.toNodeAccessCertificate valueCertificate

/--
End-to-end sequential legality and node-access safety from canonical relation
data plus the immutable-field value certificate.
-/
theorem linearizable_and_nodeSafe_of_nextReadValues
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (valueCertificate : NextReadValueCertificate execution)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate execution.toControlledCandidate ∧
      ∃ schedule final finalValues,
        RespectsGraph execution.relations.graph schedule ∧
          replay? initial schedule = some final ∧
          TreiberRA.Represents
            final.heap final.head finalValues ∧
          StackSpec.Legal initialValues
            (Treiber.completedHistory
              (TreiberRA.commits
                (projectedActions schedule)))
            finalValues :=
  (execution.toCSourceExecution valueCertificate)
    |>.linearizable_and_nodeSafe initialRepresentation

end SourceAtomicExecution

end WeakMemory.TreiberRC11
