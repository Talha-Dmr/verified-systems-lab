import WeakMemory.TreiberControlFlow

namespace WeakMemory.TreiberRC11.EventGraph

/-!
# Numbering control-flow labels into graph events

This module gives a finite global carrier to per-thread control-flow labels.
Invocation labels remain available as source-history metadata but do not
become `TreiberRC11.Event` values. Atomic labels are numbered with fresh,
strictly increasing identifiers and projected to `Event.algorithm`.

Identifier zero is reserved for one logical initializer. Atomic identifiers
start at one. Program order relates graph members from the same thread when
their identifiers increase. Because numbering follows global label chronology
and the resulting event identifiers are strictly increasing, this is exactly
same-thread emitted chronology.

Reads-from and modification order are deliberately supplied separately when a
`Graph` is formed. This module proves only carrier, identifier, initializer,
and program-order properties; it does not claim full `WellFormed`.
-/

/-- A label belongs to a thread when any atomic action carries that thread. -/
def LabelOwnedBy
    (thread : Nat) :
    ControlFlow.Label α → Prop
  | .invokePush .. => True
  | .invokePop .. => True
  | .invokeIsEmpty .. => True
  | .atomic _ action =>
      ControlFlow.actionThread action = thread

/-- One globally collected control-flow label together with its owner. -/
structure OwnedLabel (α : Type) where
  thread : Nat
  label : ControlFlow.Label α
  owned : LabelOwnedBy thread label

namespace OwnedLabel

/-- Package a label emitted by a local step with its proven thread owner. -/
def ofLocalStep
    {thread : Nat}
    {before after : ControlFlow.LocalState α}
    {label : ControlFlow.Label α}
    (step : ControlFlow.LocalStep thread before label after) :
    OwnedLabel α := {
  thread := thread
  label := label
  owned := by
    cases label with
    | invokePush =>
        exact True.intro
    | invokePop =>
        exact True.intro
    | invokeIsEmpty =>
        exact True.intro
    | atomic operation action =>
        exact step.atomicActionThread_eq
}

/-- Ownership exposes the embedded thread of an atomic label. -/
theorem atomic_actionThread
    {owned : OwnedLabel α}
    {operation : ControlFlow.OperationId}
    {action : TreiberRA.Action α}
    (shape :
      owned.label = .atomic operation action) :
    ControlFlow.actionThread action = owned.thread := by
  have ownership := owned.owned
  rw [shape] at ownership
  exact ownership

end OwnedLabel

/--
Number only atomic labels, starting at `next`.

Invocation labels consume no graph identifier because they are not atomic-head
events in the current RC11 graph layer.
-/
def atomicEventsFrom :
    EventId →
    List (OwnedLabel α) →
    List (Event α)
  | _, [] => []
  | next, owned :: rest =>
      match owned.label with
      | .invokePush .. =>
          atomicEventsFrom next rest
      | .invokePop .. =>
          atomicEventsFrom next rest
      | .invokeIsEmpty .. =>
          atomicEventsFrom next rest
      | .atomic _ action =>
          Event.mk next (.algorithm action) ::
            atomicEventsFrom (next + 1) rest

/-- Every numbered atomic event has an identifier at least `next`. -/
theorem atomicEventsFrom_id_lowerBound
    {next : EventId}
    {labels : List (OwnedLabel α)}
    {event : Event α}
    (member : event ∈ atomicEventsFrom next labels) :
    next ≤ event.id := by
  induction labels generalizing next with
  | nil =>
      simp [atomicEventsFrom] at member
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis (next := next) member
      | invokePop operation =>
          exact inductionHypothesis (next := next) member
      | invokeIsEmpty operation =>
          exact inductionHypothesis (next := next) member
      | atomic operation action =>
          simp only [atomicEventsFrom, List.mem_cons] at member
          rcases member with isHead | inRest
          · subst event
            exact Nat.le_refl next
          · exact Nat.le_trans
              (Nat.le_succ next)
              (inductionHypothesis
                (next := next + 1) inRest)

/-- Numbered atomic-event identifiers increase with emitted chronology. -/
theorem atomicEventsFrom_pairwise_id_lt
    (next : EventId)
    (labels : List (OwnedLabel α)) :
    (atomicEventsFrom next labels).Pairwise
      (fun first second => first.id < second.id) := by
  induction labels generalizing next with
  | nil =>
      exact List.Pairwise.nil
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis next
      | invokePop operation =>
          exact inductionHypothesis next
      | invokeIsEmpty operation =>
          exact inductionHypothesis next
      | atomic operation action =>
          apply List.Pairwise.cons
          · intro later laterMember
            exact Nat.lt_of_lt_of_le
              (Nat.lt_succ_self next)
              (atomicEventsFrom_id_lowerBound laterMember)
          · exact inductionHypothesis (next + 1)

/-- Fresh numbering prevents duplicate atomic events. -/
theorem atomicEventsFrom_nodup
    (next : EventId)
    (labels : List (OwnedLabel α)) :
    (atomicEventsFrom next labels).Nodup := by
  induction labels generalizing next with
  | nil =>
      exact List.nodup_nil
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis next
      | invokePop operation =>
          exact inductionHypothesis next
      | invokeIsEmpty operation =>
          exact inductionHypothesis next
      | atomic operation action =>
          apply List.nodup_cons.mpr
          constructor
          · intro headInRest
            have lowerBound :
                next + 1 ≤
                  (Event.mk next
                    (.algorithm action) : Event α).id :=
              atomicEventsFrom_id_lowerBound headInRest
            have impossible : next < next :=
              Nat.lt_of_lt_of_le
                (Nat.lt_succ_self next)
                lowerBound
            exact (Nat.lt_irrefl next) impossible
          · exact inductionHypothesis (next + 1)

/-- Equal numbered identifiers identify the same atomic event. -/
theorem atomicEventsFrom_uniqueIds
    (next : EventId)
    (labels : List (OwnedLabel α))
    {left right : Event α}
    (leftMember :
      left ∈ atomicEventsFrom next labels)
    (rightMember :
      right ∈ atomicEventsFrom next labels)
    (sameId : left.id = right.id) :
    left = right := by
  induction labels generalizing next left right with
  | nil =>
      simp [atomicEventsFrom] at leftMember
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis
            (next := next)
            leftMember rightMember sameId
      | invokePop operation =>
          exact inductionHypothesis
            (next := next)
            leftMember rightMember sameId
      | invokeIsEmpty operation =>
          exact inductionHypothesis
            (next := next)
            leftMember rightMember sameId
      | atomic operation action =>
          simp only [atomicEventsFrom, List.mem_cons] at leftMember
          simp only [atomicEventsFrom, List.mem_cons] at rightMember
          rcases leftMember with leftIsHead | leftInRest
          · subst left
            rcases rightMember with rightIsHead | rightInRest
            · exact rightIsHead.symm
            · have lowerBound :
                  next + 1 ≤ right.id :=
                atomicEventsFrom_id_lowerBound rightInRest
              rw [← sameId] at lowerBound
              have impossible : next < next :=
                Nat.lt_of_lt_of_le
                  (Nat.lt_succ_self next)
                  lowerBound
              exact (Nat.lt_irrefl next impossible).elim
          · rcases rightMember with rightIsHead | rightInRest
            · subst right
              have lowerBound :
                  next + 1 ≤ left.id :=
                atomicEventsFrom_id_lowerBound leftInRest
              rw [sameId] at lowerBound
              have impossible : next < next :=
                Nat.lt_of_lt_of_le
                  (Nat.lt_succ_self next)
                  lowerBound
              exact (Nat.lt_irrefl next impossible).elim
            · exact inductionHypothesis
                (next := next + 1)
                leftInRest rightInRest sameId

/-- Numbered events are algorithm events, never logical initializers. -/
theorem atomicEventsFrom_not_initial
    {next : EventId}
    {labels : List (OwnedLabel α)}
    {event : Event α}
    (member : event ∈ atomicEventsFrom next labels) :
    ¬ event.IsInitial := by
  induction labels generalizing next with
  | nil =>
      simp [atomicEventsFrom] at member
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label with
      | invokePush operation reserved value =>
          exact inductionHypothesis (next := next) member
      | invokePop operation =>
          exact inductionHypothesis (next := next) member
      | invokeIsEmpty operation =>
          exact inductionHypothesis (next := next) member
      | atomic operation action =>
          simp only [atomicEventsFrom, List.mem_cons] at member
          rcases member with isHead | inRest
          · subst event
            simp [Event.IsInitial]
          · exact inductionHypothesis
              (next := next + 1) inRest

/-- A global finite collection of owned control-flow labels. -/
structure Skeleton (α : Type) where
  labels : List (OwnedLabel α)

namespace Skeleton

/-- The unique logical initializer, using the reserved identifier zero. -/
def initialEvent : Event α :=
  Event.mk 0 .initial

/-- Initializer followed by freshly numbered atomic events. -/
def events (skeleton : Skeleton α) : List (Event α) :=
  initialEvent ::
    atomicEventsFrom 1 skeleton.labels

/--
Program order is same-thread order induced by increasing fresh identifiers.

Membership guards make closure a construction property rather than a
requirement on arbitrary relation endpoints.
-/
def programOrder
    (skeleton : Skeleton α) :
    Relation (Event α) :=
  fun source target =>
    source ∈ skeleton.events ∧
      target ∈ skeleton.events ∧
      ∃ thread,
        source.thread? = some thread ∧
          target.thread? = some thread ∧
          source.id < target.id

/--
Form an RC11 graph after a caller supplies reads-from and modification order.

No property of either supplied relation is asserted here.
-/
def toGraph
    (skeleton : Skeleton α)
    (readsFrom modificationOrder : Relation (Event α)) :
    Graph α where
  events := skeleton.events
  programOrder := skeleton.programOrder
  readsFrom := readsFrom
  modificationOrder := modificationOrder

/-- The complete event carrier is ordered by strictly increasing identifiers. -/
theorem events_pairwise_id_lt
    (skeleton : Skeleton α) :
    skeleton.events.Pairwise
      (fun first second => first.id < second.id) := by
  apply List.Pairwise.cons
  · intro event member
    have lowerBound :
        1 ≤ event.id :=
      atomicEventsFrom_id_lowerBound member
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one lowerBound
  · exact atomicEventsFrom_pairwise_id_lt
      1 skeleton.labels

/-- The generated carrier contains no duplicate event. -/
theorem noDuplicateEvents
    (skeleton : Skeleton α) :
    skeleton.events.Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro initialInAtomic
    have lowerBound :
        1 ≤ (initialEvent : Event α).id :=
      atomicEventsFrom_id_lowerBound initialInAtomic
    have impossible : 0 < 0 := by
      simpa [initialEvent] using
        (Nat.lt_of_lt_of_le Nat.zero_lt_one lowerBound)
    exact (Nat.lt_irrefl 0) impossible
  · exact atomicEventsFrom_nodup 1 skeleton.labels

/-- Generated event identifiers are globally injective on the carrier. -/
theorem uniqueIds
    (skeleton : Skeleton α)
    {left right : Event α}
    (leftMember : left ∈ skeleton.events)
    (rightMember : right ∈ skeleton.events)
    (sameId : left.id = right.id) :
    left = right := by
  simp only [events, List.mem_cons] at leftMember rightMember
  rcases leftMember with leftIsInitial | leftInAtomic
  · subst left
    rcases rightMember with rightIsInitial | rightInAtomic
    · exact rightIsInitial.symm
    · have lowerBound :
          1 ≤ right.id :=
        atomicEventsFrom_id_lowerBound rightInAtomic
      rw [← sameId] at lowerBound
      have impossible : 0 < 0 := by
        simpa [initialEvent] using
          (Nat.lt_of_lt_of_le Nat.zero_lt_one lowerBound)
      exact (Nat.lt_irrefl 0 impossible).elim
  · rcases rightMember with rightIsInitial | rightInAtomic
    · subst right
      have lowerBound :
          1 ≤ left.id :=
        atomicEventsFrom_id_lowerBound leftInAtomic
      rw [sameId] at lowerBound
      have impossible : 0 < 0 := by
        simpa [initialEvent] using
          (Nat.lt_of_lt_of_le Nat.zero_lt_one lowerBound)
      exact (Nat.lt_irrefl 0 impossible).elim
    · exact atomicEventsFrom_uniqueIds
        1 skeleton.labels
        leftInAtomic rightInAtomic sameId

/-- The reserved initializer is present and is the only initial event. -/
theorem initialExistsUnique
    (skeleton : Skeleton α) :
    ∃ initial,
      initial ∈ skeleton.events ∧
        initial.IsInitial ∧
        ∀ other,
          other ∈ skeleton.events →
          other.IsInitial →
          other = initial := by
  refine ⟨initialEvent, by simp [events], ?_, ?_⟩
  · trivial
  · intro other otherMember otherInitial
    simp only [events, List.mem_cons] at otherMember
    rcases otherMember with isInitializer | inAtomic
    · exact isInitializer
    · exact
        (atomicEventsFrom_not_initial inAtomic
          otherInitial).elim

/-- Constructed program-order edges are closed over the graph carrier. -/
theorem programOrderClosed
    (skeleton : Skeleton α)
    (readsFrom modificationOrder : Relation (Event α))
    {source target : Event α}
    (edge :
      (skeleton.toGraph readsFrom modificationOrder).programOrder
        source target) :
    source ∈
        (skeleton.toGraph readsFrom modificationOrder).events ∧
      target ∈
        (skeleton.toGraph readsFrom modificationOrder).events :=
  ⟨edge.1, edge.2.1⟩

/-- Constructed program-order edges relate events of one algorithm thread. -/
theorem programOrderSameThread
    (skeleton : Skeleton α)
    (readsFrom modificationOrder : Relation (Event α))
    {source target : Event α}
    (edge :
      (skeleton.toGraph readsFrom modificationOrder).programOrder
        source target) :
    ∃ thread,
      source.thread? = some thread ∧
        target.thread? = some thread := by
  exact ⟨edge.2.2.choose,
    edge.2.2.choose_spec.1,
    edge.2.2.choose_spec.2.1⟩

/-- Increasing identifiers make constructed program order irreflexive. -/
theorem programOrderIrreflexive
    (skeleton : Skeleton α)
    (readsFrom modificationOrder : Relation (Event α))
    (event : Event α) :
    ¬ (skeleton.toGraph readsFrom modificationOrder).programOrder
      event event := by
  intro edge
  exact (Nat.lt_irrefl event.id) edge.2.2.choose_spec.2.2

/-- Same-thread identifier order makes constructed program order transitive. -/
theorem programOrderTransitive
    (skeleton : Skeleton α)
    (readsFrom modificationOrder : Relation (Event α))
    {first middle last : Event α}
    (firstEdge :
      (skeleton.toGraph readsFrom modificationOrder).programOrder
        first middle)
    (secondEdge :
      (skeleton.toGraph readsFrom modificationOrder).programOrder
        middle last) :
    (skeleton.toGraph readsFrom modificationOrder).programOrder
      first last := by
  obtain ⟨firstMember, middleMember, firstThread,
      firstThreadShape, middleFirstThread, firstBeforeMiddle⟩ :=
    firstEdge
  obtain ⟨_, lastMember, secondThread,
      middleSecondThread, lastThreadShape, middleBeforeLast⟩ :=
    secondEdge
  have sameThread : firstThread = secondThread :=
    Option.some.inj
      (middleFirstThread.symm.trans middleSecondThread)
  subst secondThread
  exact ⟨firstMember, lastMember, firstThread,
    firstThreadShape, lastThreadShape,
    Nat.lt_trans firstBeforeMiddle middleBeforeLast⟩

end Skeleton

end WeakMemory.TreiberRC11.EventGraph
