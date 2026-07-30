import WeakMemory.TreiberEventGraph

namespace WeakMemory.TreiberRC11.Interleaving

/-!
# Locally valid global Treiber interleavings

`EventGraph.Skeleton` collects source-control-flow labels from every thread in
one finite global list. This module checks the local source shape of that list:
projecting it to any one thread must produce a `ControlFlow.Execution` that
starts idle. The final local state may remain non-idle, representing a finite
prefix with a pending invocation.

The source certificate also records the two global allocation disciplines
that are not properties of a single local execution:

* invocation operation identifiers are never reused;
* push invocations reserve distinct nodes that are absent from the initial
  heap.

This is deliberately only a source-skeleton certificate. It does not yet
construct `GeneratedEvents`, reads-from, modification order, or publication
witnesses.
-/

/-- Keep exactly the labels owned by one thread, preserving global order. -/
def labelsForThread
    (thread : Nat) :
    List (EventGraph.OwnedLabel α) →
      List (ControlFlow.Label α)
  | [] => []
  | owned :: rest =>
      if owned.thread = thread then
        owned.label :: labelsForThread thread rest
      else
        labelsForThread thread rest

/-- Thread projection distributes over concatenation. -/
theorem labelsForThread_append
    (thread : Nat)
    (first second : List (EventGraph.OwnedLabel α)) :
    labelsForThread thread (first ++ second) =
      labelsForThread thread first ++
        labelsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      simp only [List.cons_append, labelsForThread]
      split <;> simp [inductionHypothesis]

/-- Extract the operation identifier of an invocation label. -/
def invocationOperation? :
    EventGraph.OwnedLabel α →
      Option ControlFlow.OperationId
  | ⟨_, .invokePush operation .., _⟩ => some operation
  | ⟨_, .invokePop operation, _⟩ => some operation
  | ⟨_, .invokeIsEmpty operation, _⟩ => some operation
  | ⟨_, .writeNext .., _⟩ => none
  | ⟨_, .readNext .., _⟩ => none
  | ⟨_, .atomic .., _⟩ => none

/-- Invocation operation identifiers in global skeleton order. -/
def invocationOperations
    (labels : List (EventGraph.OwnedLabel α)) :
    List ControlFlow.OperationId :=
  labels.filterMap invocationOperation?

/-- Extract the node reserved by a push invocation. -/
def pushReservation? :
    EventGraph.OwnedLabel α →
      Option TreiberRA.NodeId
  | ⟨_, .invokePush _ reserved .., _⟩ => some reserved
  | ⟨_, .invokePop _, _⟩ => none
  | ⟨_, .invokeIsEmpty _, _⟩ => none
  | ⟨_, .writeNext .., _⟩ => none
  | ⟨_, .readNext .., _⟩ => none
  | ⟨_, .atomic .., _⟩ => none

/-- Push-reserved node identifiers in global skeleton order. -/
def pushReservations
    (labels : List (EventGraph.OwnedLabel α)) :
    List TreiberRA.NodeId :=
  labels.filterMap pushReservation?

/--
Every label in a thread projection comes from an owned global label for that
thread.
-/
theorem exists_owned_of_mem_labelsForThread
    {thread : Nat}
    {labels : List (EventGraph.OwnedLabel α)}
    {label : ControlFlow.Label α}
    (member : label ∈ labelsForThread thread labels) :
    ∃ owned,
      owned ∈ labels ∧
        owned.thread = thread ∧
        owned.label = label := by
  induction labels with
  | nil =>
      simp [labelsForThread] at member
  | cons owned rest inductionHypothesis =>
      by_cases sameThread : owned.thread = thread
      · simp only [labelsForThread, sameThread, ↓reduceIte,
          List.mem_cons] at member
        rcases member with isHead | inRest
        · exact ⟨owned, by simp, sameThread, isHead.symm⟩
        · obtain ⟨source, sourceMember, sourceThread, sourceLabel⟩ :=
            inductionHypothesis inRest
          exact ⟨source, by simp [sourceMember],
            sourceThread, sourceLabel⟩
      · simp only [labelsForThread, sameThread, ↓reduceIte] at member
        obtain ⟨source, sourceMember, sourceThread, sourceLabel⟩ :=
          inductionHypothesis member
        exact ⟨source, by simp [sourceMember],
          sourceThread, sourceLabel⟩

/--
An atomic action found in a thread projection carries exactly that thread in
its operational action.
-/
theorem atomic_actionThread_of_mem_labelsForThread
    {thread : Nat}
    {labels : List (EventGraph.OwnedLabel α)}
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (member :
      ControlFlow.Label.atomic operation action ∈
        labelsForThread thread labels) :
    ControlFlow.actionThread action = thread := by
  obtain ⟨owned, _, ownerThread, labelShape⟩ :=
    exists_owned_of_mem_labelsForThread member
  have actionThread :=
    owned.atomic_actionThread labelShape
  exact actionThread.trans ownerThread

/--
A globally collected skeleton is locally valid when every per-thread
projection is a source-shaped execution starting from idle.

The existential final state intentionally permits finite prefixes whose last
invocation is still pending.
-/
structure LocallyValid
    (skeleton : EventGraph.Skeleton α) : Prop where
  execution :
    ∀ thread,
      ∃ final,
        ControlFlow.Execution thread
          .idle
          (labelsForThread thread skeleton.labels)
          final

/--
Local validity plus globally unique invocation identities and node
reservations.
-/
structure SourceSkeleton
    (initial : TreiberRA.State α)
    (skeleton : EventGraph.Skeleton α) : Prop
    extends LocallyValid skeleton where
  operationIdsNodup :
    (invocationOperations skeleton.labels).Nodup
  reservationsNodup :
    (pushReservations skeleton.labels).Nodup
  reservationsFresh :
    ∀ {reserved : TreiberRA.NodeId},
      reserved ∈ pushReservations skeleton.labels →
      initial.heap reserved = none

namespace LocallyValid

/-- Retrieve the locally valid execution for a chosen thread. -/
theorem exists_execution
    {skeleton : EventGraph.Skeleton α}
    (valid : LocallyValid skeleton)
    (thread : Nat) :
    ∃ final,
      ControlFlow.Execution thread
        .idle
        (labelsForThread thread skeleton.labels)
        final :=
  valid.execution thread

/-- Every atomic label in a locally valid thread projection has that thread. -/
theorem atomicActionThread
    {skeleton : EventGraph.Skeleton α}
    (valid : LocallyValid skeleton)
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (member :
      ControlFlow.Label.atomic operation action ∈
        labelsForThread thread skeleton.labels) :
    ControlFlow.actionThread action = thread := by
  obtain ⟨final, execution⟩ := valid.execution thread
  exact execution.atomicLabelsHaveThread
    operation action member

end LocallyValid

/--
If a filtered extraction is duplicate-free, the value extracted at a chosen
list occurrence does not occur in either surrounding fragment.
-/
private theorem extracted_unique_at
    {extract : γ → Option δ}
    {items earlier later : List γ}
    {item : γ}
    {value : δ}
    (itemsShape : items = earlier ++ item :: later)
    (extracts : extract item = some value)
    (noDuplicates : (items.filterMap extract).Nodup) :
    value ∉ earlier.filterMap extract ∧
      value ∉ later.filterMap extract := by
  have shapedExtraction :
      items.filterMap extract =
        earlier.filterMap extract ++
          value :: later.filterMap extract := by
    subst items
    simp [extracts]
  rw [shapedExtraction] at noDuplicates
  have appendNodup :=
    List.nodup_append.mp noDuplicates
  constructor
  · intro inEarlier
    exact appendNodup.2.2
      value inEarlier value (by simp) rfl
  · exact (List.nodup_cons.mp appendNodup.2.1).1

namespace SourceSkeleton

/-- The certified local execution for any selected thread. -/
theorem exists_execution
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    (thread : Nat) :
    ∃ final,
      ControlFlow.Execution thread
        .idle
        (labelsForThread thread skeleton.labels)
        final :=
  certificate.toLocallyValid.execution thread

/-- Every atomic action in a certified projection has its projected thread. -/
theorem atomicActionThread
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (member :
      ControlFlow.Label.atomic operation action ∈
        labelsForThread thread skeleton.labels) :
    ControlFlow.actionThread action = thread :=
  certificate.toLocallyValid.atomicActionThread member

/--
The operation identifier at one invocation occurrence is absent from every
earlier and later invocation occurrence in the global skeleton.
-/
theorem operation_unique_at
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {earlier later : List (EventGraph.OwnedLabel α)}
    {owned : EventGraph.OwnedLabel α}
    {operation : ControlFlow.OperationId}
    (labelsShape :
      skeleton.labels = earlier ++ owned :: later)
    (invocation :
      invocationOperation? owned = some operation) :
    operation ∉ invocationOperations earlier ∧
      operation ∉ invocationOperations later := by
  exact extracted_unique_at
    labelsShape invocation certificate.operationIdsNodup

/--
The node at one push-reservation occurrence is absent from every earlier and
later push reservation in the global skeleton.
-/
theorem reservation_unique_at
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {earlier later : List (EventGraph.OwnedLabel α)}
    {owned : EventGraph.OwnedLabel α}
    {reserved : TreiberRA.NodeId}
    (labelsShape :
      skeleton.labels = earlier ++ owned :: later)
    (reservation :
      pushReservation? owned = some reserved) :
    reserved ∉ pushReservations earlier ∧
      reserved ∉ pushReservations later := by
  exact extracted_unique_at
    labelsShape reservation certificate.reservationsNodup

/-- Every reserved push node is absent from the initial heap. -/
theorem reservationFresh
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {owned : EventGraph.OwnedLabel α}
    {reserved : TreiberRA.NodeId}
    (member : owned ∈ skeleton.labels)
    (reservation :
      pushReservation? owned = some reserved) :
    initial.heap reserved = none := by
  apply certificate.reservationsFresh
  exact List.mem_filterMap.mpr
    ⟨owned, member, reservation⟩

/--
Every selected source-level `readNext` occurrence has an earlier owned atomic
event in the same thread and operation that supplied its non-null node.

The local observer is immediately previous after thread projection. Other
threads may have labels between the observer and field read in the global
skeleton, so this theorem exposes global prefix membership rather than global
adjacency.
-/
theorem readNext_hasObserver
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {leading trailing : List (EventGraph.OwnedLabel α)}
    {fieldRead : EventGraph.OwnedLabel α}
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (labelsShape :
      skeleton.labels =
        leading ++ fieldRead :: trailing)
    (readThread : fieldRead.thread = thread)
    (readLabel :
      fieldRead.label =
        .readNext operation node next) :
    ∃ observer action,
      observer ∈ leading ∧
        observer.thread = thread ∧
        observer.label = .atomic operation action ∧
        ControlFlow.AuthorizesReadNext thread node action := by
  obtain ⟨final, execution⟩ :=
    certificate.exists_execution thread
  have projectedShape :
      labelsForThread thread skeleton.labels =
        labelsForThread thread leading ++
          .readNext operation node next ::
            labelsForThread thread trailing := by
    rw [labelsShape, labelsForThread_append]
    simp [labelsForThread, readThread, readLabel]
  obtain ⟨earlier, action, leadingShape, authorized⟩ :=
    execution.readNext_hasObserver projectedShape
  have atomicMember :
      ControlFlow.Label.atomic operation action ∈
        labelsForThread thread leading := by
    rw [leadingShape]
    simp
  obtain ⟨observer, observerMember, observerThread,
      observerLabel⟩ :=
    exists_owned_of_mem_labelsForThread atomicMember
  exact ⟨observer, action, observerMember,
    observerThread, observerLabel, authorized⟩

/--
Every selected successful push has an earlier source `writeNext` occurrence
in the same thread and operation, carrying exactly the pointer installed in
the allocator record at publication.
-/
theorem pushSuccess_hasNextWrite
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    {leading trailing : List (EventGraph.OwnedLabel α)}
    {publisher : EventGraph.OwnedLabel α}
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    (labelsShape :
      skeleton.labels =
        leading ++ publisher :: trailing)
    (publisherThread : publisher.thread = thread)
    (publisherLabel :
      publisher.label =
        .atomic operation
          (.pushSuccess thread reserved value expected)) :
    ∃ fieldWrite,
      fieldWrite ∈ leading ∧
        fieldWrite.thread = thread ∧
        fieldWrite.label =
          .writeNext operation reserved expected := by
  obtain ⟨final, execution⟩ :=
    certificate.exists_execution thread
  have projectedShape :
      labelsForThread thread skeleton.labels =
        labelsForThread thread leading ++
          .atomic operation
            (.pushSuccess thread reserved value expected) ::
            labelsForThread thread trailing := by
    rw [labelsShape, labelsForThread_append]
    simp [labelsForThread, publisherThread, publisherLabel]
  obtain ⟨earlier, leadingShape⟩ :=
    execution.pushSuccess_hasNextWrite projectedShape
  have writeMember :
      ControlFlow.Label.writeNext operation reserved expected ∈
        labelsForThread thread leading := by
    rw [leadingShape]
    simp
  obtain ⟨fieldWrite, fieldWriteMember, fieldWriteThread,
      fieldWriteLabel⟩ :=
    exists_owned_of_mem_labelsForThread writeMember
  exact ⟨fieldWrite, fieldWriteMember,
    fieldWriteThread, fieldWriteLabel⟩

/--
Occurrence-level form of `readNext_hasObserver`, preserving the identity of
equal repeated retry labels.
-/
theorem readNextOccurrence_hasObserver
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    (fieldRead : EventGraph.SourceOccurrence skeleton)
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {node : TreiberRA.NodeId}
    {next : Option TreiberRA.NodeId}
    (readThread :
      fieldRead.selected.thread = thread)
    (readLabel :
      fieldRead.selected.label =
        .readNext operation node next) :
    ∃ observer : EventGraph.SourceOccurrence skeleton,
      observer.SequencedBefore fieldRead ∧
        ∃ action,
          observer.selected.label =
              .atomic operation action ∧
            ControlFlow.AuthorizesReadNext
              thread node action := by
  obtain ⟨observerOwned, action, observerMember,
      observerThread, observerLabel, authorized⟩ :=
    certificate.readNext_hasObserver
      fieldRead.labelsShape readThread readLabel
  obtain ⟨before, after, leadingShape⟩ :=
    List.append_of_mem observerMember
  let observer : EventGraph.SourceOccurrence skeleton := {
    leading := before
    selected := observerOwned
    trailing :=
      after ++ fieldRead.selected :: fieldRead.trailing
    labelsShape := by
      rw [fieldRead.labelsShape, leadingShape]
      simp [List.append_assoc]
  }
  refine ⟨observer, ?_, action, observerLabel, authorized⟩
  constructor
  · exact observerThread.trans readThread.symm
  · simp [observer, EventGraph.SourceOccurrence.index,
      leadingShape]

/--
Occurrence-level form of `pushSuccess_hasNextWrite`, preserving the exact
pre-publication write paired with a release CAS.
-/
theorem pushSuccessOccurrence_hasNextWrite
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate : SourceSkeleton initial skeleton)
    (publisher : EventGraph.SourceOccurrence skeleton)
    {thread : Nat}
    {operation : ControlFlow.OperationId}
    {reserved : TreiberRA.NodeId}
    {value : α}
    {expected : Option TreiberRA.NodeId}
    (publisherThread :
      publisher.selected.thread = thread)
    (publisherLabel :
      publisher.selected.label =
        .atomic operation
          (.pushSuccess thread reserved value expected)) :
    ∃ fieldWrite : EventGraph.SourceOccurrence skeleton,
      fieldWrite.SequencedBefore publisher ∧
        fieldWrite.selected.label =
          .writeNext operation reserved expected := by
  obtain ⟨fieldWriteOwned, fieldWriteMember,
      fieldWriteThread, fieldWriteLabel⟩ :=
    certificate.pushSuccess_hasNextWrite
      publisher.labelsShape publisherThread publisherLabel
  obtain ⟨before, after, leadingShape⟩ :=
    List.append_of_mem fieldWriteMember
  let fieldWrite : EventGraph.SourceOccurrence skeleton := {
    leading := before
    selected := fieldWriteOwned
    trailing :=
      after ++ publisher.selected :: publisher.trailing
    labelsShape := by
      rw [publisher.labelsShape, leadingShape]
      simp [List.append_assoc]
  }
  refine ⟨fieldWrite, ?_, fieldWriteLabel⟩
  constructor
  · exact fieldWriteThread.trans publisherThread.symm
  · simp [fieldWrite, EventGraph.SourceOccurrence.index,
      leadingShape]

end SourceSkeleton

end WeakMemory.TreiberRC11.Interleaving
