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

/-- Extract the operation identifier of an invocation label. -/
def invocationOperation? :
    EventGraph.OwnedLabel α →
      Option ControlFlow.OperationId
  | ⟨_, .invokePush operation .., _⟩ => some operation
  | ⟨_, .invokePop operation, _⟩ => some operation
  | ⟨_, .invokeIsEmpty operation, _⟩ => some operation
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

end SourceSkeleton

end WeakMemory.TreiberRC11.Interleaving
