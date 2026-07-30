import WeakMemory.TreiberC11V1

namespace WeakMemory.TreiberC11V1.RC11

/-!
# Independent finite RC11 core for the source semantics

This module equips `TreiberC11V1` source traces with finite, single-location
atomic relations.  It imports neither the checked Treiber execution graph nor
the raw validator.  A later refinement module may translate these atoms and
relations into those target types.

The only atomic location represented here is `stack->head`.  Identifier zero
is reserved for its implicit null initializer; all source atomic occurrences
come from the trace.
-/

/-- The implicit initializer or one numbered source atomic occurrence. -/
inductive Atom (α : Type) where
  | initial
  | occurrence (value : AtomicOccurrence α)
  deriving Repr, DecidableEq

namespace Atom

/-- Identifier zero is reserved for the implicit initializer. -/
def id : Atom α → EventId
  | .initial => 0
  | .occurrence sourceOccurrence => sourceOccurrence.id

def thread? : Atom α → Option ThreadId
  | .initial => none
  | .occurrence sourceOccurrence =>
      some sourceOccurrence.action.thread

/--
The value read from `head`, if this atom reads.

Every source atomic occurrence reads `head`; the implicit initializer does
not.
-/
def readValue : Atom α → Option Ptr
  | .initial => none
  | .occurrence sourceOccurrence =>
      some sourceOccurrence.action.readValue

/-- The value written to `head`, if this atom writes. -/
def writtenValue : Atom α → Option Ptr
  | .initial => some .null
  | .occurrence sourceOccurrence =>
      sourceOccurrence.action.writtenValue

/-- The exact source memory order, with a relaxed logical initializer. -/
def order : Atom α → MemoryOrder
  | .initial => .relaxed
  | .occurrence sourceOccurrence =>
      sourceOccurrence.action.order

/-- Successful source compare-exchanges are the non-initial RMW atoms. -/
def isRMW : Atom α → Bool
  | .initial => false
  | .occurrence sourceOccurrence =>
      sourceOccurrence.action.isRMW

def IsRead (atom : Atom α) : Prop :=
  ∃ value, atom.readValue = some value

def IsWrite (atom : Atom α) : Prop :=
  ∃ value, atom.writtenValue = some value

def IsRMW (atom : Atom α) : Prop :=
  atom.isRMW = true

def IsInitial : Atom α → Prop
  | .initial => True
  | .occurrence _ => False

end Atom

/-- Node-carrying source atomics agree with the candidate's payload table. -/
def AtomicPayloadConsistent
    (payload : NodeId → α) :
    AtomicAction α → Prop
  | .pushCas _ _ node value _ _ _ =>
      value = payload node
  | .popCas _ _ expected value _ _ _ =>
      value = payload expected
  | _ =>
      True

/-- Push invocations and node-carrying atomics use the fixed node payload. -/
def TracePayloadConsistent
    (payload : NodeId → α) :
    TraceEvent α → Prop
  | .invokePush _ _ node value =>
      value = payload node
  | .atomic occurrence =>
      AtomicPayloadConsistent payload occurrence.action
  | _ =>
      True

/--
A finite single-head candidate.

`modificationOrder` is the non-initial write tail; the initializer is
prepended by `writeOrder`.  `readSources` stores `(read, source)` identifier
pairs.
-/
structure Candidate (α : Type) where
  trace : List (TraceEvent α)
  /-- Abstract payload associated with each reclamation-free node identity. -/
  payload : NodeId → α
  readSources : List (EventId × EventId)
  modificationOrder : List EventId

/-- Project an atomic trace event into the independent atom carrier. -/
def atomOfTraceEvent? : TraceEvent α → Option (Atom α)
  | .atomic occurrence => some (.occurrence occurrence)
  | _ => none

namespace Candidate

/-- Source atomic occurrences in trace order. -/
def nonInitialAtoms (candidate : Candidate α) : List (Atom α) :=
  candidate.trace.filterMap atomOfTraceEvent?

/-- The implicit initializer followed by source atoms in trace order. -/
def atoms (candidate : Candidate α) : List (Atom α) :=
  .initial :: candidate.nonInitialAtoms

/-- Atom identifiers in source occurrence order. -/
def atomIds (candidate : Candidate α) : List EventId :=
  candidate.atoms.map Atom.id

/-- Full modification order, including the implicit initializer. -/
def writeOrder (candidate : Candidate α) : List EventId :=
  0 :: candidate.modificationOrder

end Candidate

/-- First source associated with a target identifier, if one is present. -/
def sourceFor :
    List (EventId × EventId) → EventId → Option EventId
  | [], _ => none
  | (candidateTarget, candidateSource) :: rest, target =>
      if candidateTarget = target then
        some candidateSource
      else
        sourceFor rest target

namespace Candidate

/-- The finite reads-from source function induced by `readSources`. -/
def sourceId
    (candidate : Candidate α)
    (target : EventId) : Option EventId :=
  sourceFor candidate.readSources target

/--
Canonical finite serialization of the carrier-relevant source function.

The fixed-point requirement in `Valid` excludes duplicate, off-carrier, and
non-read associations without referring to the downstream validator.
-/
def canonicalReadSources
    (candidate : Candidate α) :
    List (EventId × EventId) :=
  candidate.atoms.filterMap fun target =>
    (candidate.sourceId target.id).map fun source =>
      (target.id, source)

end Candidate

/-- A relation used only by this independent finite semantics. -/
abbrev Rel (β : Type) := β → β → Prop

/--
Strict position order on two identifiers in a finite list.

Membership is part of the relation, so all derived relation endpoints stay on
the explicit finite carrier.
-/
def IdBefore
    (first second : EventId)
    (order : List EventId) : Prop :=
  first ∈ order ∧
    second ∈ order ∧
    order.idxOf first < order.idxOf second

/-- No listed identifier occurs strictly between two ordered identifiers. -/
def IdAdjacent
    (first second : EventId)
    (order : List EventId) : Prop :=
  IdBefore first second order ∧
    ∀ middle,
      ¬ (IdBefore first middle order ∧
        IdBefore middle second order)

/-- Exact same-thread atomic occurrence order inherited from the source trace. -/
def PO (candidate : Candidate α) : Rel (Atom α) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      ∃ thread,
        source.thread? = some thread ∧
          target.thread? = some thread ∧
          IdBefore source.id target.id candidate.atomIds

/-- Functional reads-from graph induced by the finite source lookup. -/
def RF (candidate : Candidate α) : Rel (Atom α) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      candidate.sourceId target.id = some source.id

/-- Strict order induced by the full finite write order. -/
def MO (candidate : Candidate α) : Rel (Atom α) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      IdBefore source.id target.id candidate.writeOrder

/-- From-read (`rb`): a read precedes every later write after its RF source. -/
def RB (candidate : Candidate α) : Rel (Atom α) :=
  fun read laterWrite =>
    ∃ source,
      RF candidate source read ∧
        MO candidate source laterWrite ∧
        read ≠ laterWrite

/-- Nonempty transitive closure of RF, MO, and RB. -/
inductive ECO (candidate : Candidate α) : Rel (Atom α) where
  | readsFrom {source target} :
      RF candidate source target →
      ECO candidate source target
  | modificationOrder {source target} :
      MO candidate source target →
      ECO candidate source target
  | readsBefore {source target} :
      RB candidate source target →
      ECO candidate source target
  | transitive {first middle last} :
      ECO candidate first middle →
      ECO candidate middle last →
      ECO candidate first last

/--
Two writes are consecutive in the finite single-location modification order.
-/
def ImmediateMO
    (candidate : Candidate α)
    (source target : Atom α) : Prop :=
  source ∈ candidate.atoms ∧
    target ∈ candidate.atoms ∧
    source.IsWrite ∧
    target.IsWrite ∧
    IdAdjacent source.id target.id candidate.writeOrder

/--
The source-specific release-sequence fragment: a release head followed by
consecutive successful RMW modifications.
-/
inductive ReleaseSequence
    (candidate : Candidate α)
    (head : Atom α) : Atom α → Prop where
  | head (member : head ∈ candidate.atoms) :
      ReleaseSequence candidate head head
  | rmw {previous next} :
      ReleaseSequence candidate head previous →
      ImmediateMO candidate previous next →
      next.IsRMW →
      ReleaseSequence candidate head next

/-- Release-sequence synchronization with an acquiring RF target. -/
def SW (candidate : Candidate α) : Rel (Atom α) :=
  fun release acquire =>
    ∃ source,
      ReleaseSequence candidate release source ∧
        RF candidate source acquire ∧
        release.order.hasRelease = true ∧
        acquire.order.hasAcquire = true

/-- Happens-before is the nonempty transitive closure of PO and SW. -/
inductive HB (candidate : Candidate α) : Rel (Atom α) where
  | programOrder {source target} :
      PO candidate source target →
      HB candidate source target
  | synchronizesWith {source target} :
      SW candidate source target →
      HB candidate source target
  | transitive {first middle last} :
      HB candidate first middle →
      HB candidate middle last →
      HB candidate first last

/-- The nonempty transitive closure of PO and RF used by no-thin-air. -/
inductive CausalOrder (candidate : Candidate α) : Rel (Atom α) where
  | programOrder {source target} :
      PO candidate source target →
      CausalOrder candidate source target
  | readsFrom {source target} :
      RF candidate source target →
      CausalOrder candidate source target
  | transitive {first middle last} :
      CausalOrder candidate first middle →
      CausalOrder candidate middle last →
      CausalOrder candidate first last

/-- Irreflexivity of an already transitively closed relation. -/
def Acyclic (relation : Rel β) : Prop :=
  ∀ element, ¬ relation element element

/-- Single-location non-SC coherence: `hb ; eco?` is irreflexive. -/
def Coherent (candidate : Candidate α) : Prop :=
  ∀ {source middle},
    HB candidate source middle →
      source ≠ middle ∧
        ¬ ECO candidate middle source

/--
Validity of the independent finite single-head RC11 candidate.

The finite data fields are deliberately shaped so a later refinement proof can
construct the validator's relation-data certificate without assuming it.
`noThinAir` and `coherence` state the independent consistency conditions.
-/
structure Valid (candidate : Candidate α) : Prop where
  /--
  Semantic atom identifiers are the canonical `0, 1, ..., n` numbering.
  This is a lossless normalization choice, not a validator-derived fact.
  -/
  atomIdsCanonical :
    candidate.atomIds =
      List.range candidate.atoms.length
  atomIdsNodup :
    candidate.atomIds.Nodup
  payloadConsistent :
    ∀ event,
      event ∈ candidate.trace →
        TracePayloadConsistent candidate.payload event
  writeTailNodup :
    candidate.modificationOrder.Nodup
  writeTailExact :
    ∀ eventId,
      eventId ∈ candidate.modificationOrder ↔
        ∃ atom,
          atom ∈ candidate.atoms ∧
            atom.id = eventId ∧
            atom.IsWrite ∧
            ¬ atom.IsInitial
  sourceSpec :
    ∀ target,
      target ∈ candidate.atoms →
        match target.readValue with
        | none =>
            candidate.sourceId target.id = none
        | some value =>
            ∃ source,
              source ∈ candidate.atoms ∧
                source.writtenValue = some value ∧
                candidate.sourceId target.id =
                  some source.id
  readSourcesCanonical :
    candidate.readSources =
      candidate.canonicalReadSources
  rmwAdjacent :
    ∀ {source rmw},
      source ∈ candidate.atoms →
      rmw ∈ candidate.atoms →
      candidate.sourceId rmw.id = some source.id →
      rmw.IsRMW →
      IdAdjacent source.id rmw.id candidate.writeOrder
  noThinAir :
    Acyclic (CausalOrder candidate)
  coherence :
    Coherent candidate

namespace Valid

/-- Coherence already excludes happens-before cycles. -/
theorem happensBeforeAcyclic
    {candidate : Candidate α}
    (valid : Valid candidate) :
    Acyclic (HB candidate) := by
  intro atom cycle
  exact (valid.coherence cycle).1 rfl

end Valid

namespace Candidate

/-- The empty initialized execution candidate. -/
def empty (payload : NodeId → α) : Candidate α where
  trace := []
  payload := payload
  readSources := []
  modificationOrder := []

private theorem empty_po_false
    (nodePayload : NodeId → α)
    {source target : Atom α} :
    ¬ PO (empty nodePayload) source target := by
  rintro ⟨sourceMember, _, thread, sourceThread, _⟩
  have sourceIsInitial :
      source = (.initial : Atom α) := by
    simpa [empty, atoms, nonInitialAtoms] using sourceMember
  subst source
  simp [Atom.thread?] at sourceThread

private theorem empty_rf_false
    (nodePayload : NodeId → α)
    {source target : Atom α} :
    ¬ RF (empty nodePayload) source target := by
  rintro ⟨_, _, chosen⟩
  simp [empty, sourceId, sourceFor] at chosen

private theorem empty_sw_false
    (nodePayload : NodeId → α)
    {source target : Atom α} :
    ¬ SW (empty nodePayload) source target := by
  rintro ⟨write, _, readsFrom, _⟩
  exact empty_rf_false nodePayload readsFrom

private theorem empty_hb_false
    (nodePayload : NodeId → α)
    {source target : Atom α} :
    ¬ HB (empty nodePayload) source target := by
  intro path
  induction path with
  | programOrder programOrder =>
      exact empty_po_false nodePayload programOrder
  | synchronizesWith synchronizesWith =>
      exact empty_sw_false nodePayload synchronizesWith
  | transitive _ _ firstImpossible _ =>
      exact firstImpossible

private theorem empty_causal_false
    (nodePayload : NodeId → α)
    {source target : Atom α} :
    ¬ CausalOrder (empty nodePayload) source target := by
  intro path
  induction path with
  | programOrder programOrder =>
      exact empty_po_false nodePayload programOrder
  | readsFrom readsFrom =>
      exact empty_rf_false nodePayload readsFrom
  | transitive _ _ firstImpossible _ =>
      exact firstImpossible

/-- The empty initialized candidate satisfies the independent finite core. -/
theorem empty_valid
    (nodePayload : NodeId → α) :
    Valid (empty nodePayload) := by
  refine {
    atomIdsCanonical := ?_
    atomIdsNodup := ?_
    payloadConsistent := ?_
    writeTailNodup := ?_
    writeTailExact := ?_
    sourceSpec := ?_
    readSourcesCanonical := ?_
    rmwAdjacent := ?_
    noThinAir := ?_
    coherence := ?_
  }
  · rfl
  · simp [empty, atomIds, atoms, nonInitialAtoms, Atom.id]
  · intro event member
    simp [empty] at member
  · simp [empty]
  · intro eventId
    simp [empty, atoms, nonInitialAtoms,
      Atom.IsWrite, Atom.writtenValue, Atom.IsInitial]
  · intro target targetMember
    simp [empty, atoms, nonInitialAtoms] at targetMember
    subst target
    rfl
  · rfl
  · intro source rmw sourceMember rmwMember chosen rmwShape
    simp [empty, atoms, nonInitialAtoms] at rmwMember
    subst rmw
    simp [Atom.IsRMW, Atom.isRMW] at rmwShape
  · intro atom
    exact empty_causal_false nodePayload
  · intro source middle happensBefore
    exact (empty_hb_false nodePayload happensBefore).elim

end Candidate

end WeakMemory.TreiberC11V1.RC11
