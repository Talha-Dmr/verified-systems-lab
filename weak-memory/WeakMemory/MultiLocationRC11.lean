import WeakMemory

namespace WeakMemory.MultiLocationRC11

/-!
# Reusable finite multi-location RC11/RA core

This module is independent of any one concurrent algorithm.  It provides the
finite atomic, non-SC release/acquire fragment needed by the reclamation-free
Michael--Scott development.  In particular, modification order is total only
per location; unrelated writes are never forced into a global order.

This is not a full ISO C semantics.  Source control flow, object lifetime,
non-atomic payload publication, weak-CAS spurious failure, and client history
are separate layers.
-/

abbrev EventId := Nat
abbrev ThreadId := Nat
abbrev Rel (α : Type) := α → α → Prop

/--
The atomic access shape represented by the core.

A failed weak compare-exchange projects to `load`; a successful one projects
to the single read/write event `rmw`.  Whether a compare-equal load arose from
a spurious weak-CAS failure belongs to the source/control layer, not RC11.
-/
inductive Access (Value : Type) where
  | initial (value : Value)
  | load (value : Value)
  | store (value : Value)
  | rmw (read written : Value)
  deriving Repr, DecidableEq

namespace Access

def readValue : Access Value → Option Value
  | .initial _ | .store _ => none
  | .load value | .rmw value _ => some value

def writtenValue : Access Value → Option Value
  | .load _ => none
  | .initial value | .store value | .rmw _ value => some value

def IsRead : Access Value → Prop
  | .load _ | .rmw _ _ => True
  | .initial _ | .store _ => False

def IsWrite : Access Value → Prop
  | .initial _ | .store _ | .rmw _ _ => True
  | .load _ => False

def IsRMW : Access Value → Prop
  | .rmw _ _ => True
  | .initial _ | .load _ | .store _ => False

def IsInitial : Access Value → Prop
  | .initial _ => True
  | .load _ | .store _ | .rmw _ _ => False

/-!
Supported non-SC RA orders.  `seqCst` is intentionally rejected because this
core carries no global SC order.
-/
def Allows : Access Value → MemoryOrder → Prop
  | .initial _, .relaxed => True
  | .load _, .relaxed | .load _, .acquire => True
  | .store _, .relaxed | .store _, .release => True
  | .rmw _ _, .relaxed
  | .rmw _ _, .acquire
  | .rmw _ _, .release
  | .rmw _ _, .acqRel => True
  | _, _ => False

end Access

/-- One location initializer or later atomic event. -/
structure Atom (Location Value : Type) where
  id : EventId
  thread? : Option ThreadId
  location : Location
  access : Access Value
  order : MemoryOrder
  deriving Repr, DecidableEq

namespace Atom

def readValue (atom : Atom Location Value) : Option Value :=
  atom.access.readValue

def writtenValue (atom : Atom Location Value) : Option Value :=
  atom.access.writtenValue

def IsRead (atom : Atom Location Value) : Prop :=
  atom.access.IsRead

def IsWrite (atom : Atom Location Value) : Prop :=
  atom.access.IsWrite

def IsRMW (atom : Atom Location Value) : Prop :=
  atom.access.IsRMW

def IsInitial (atom : Atom Location Value) : Prop :=
  atom.access.IsInitial

/-- A proper atomic write event rather than an object initializer. -/
def IsNoninitialWrite (atom : Atom Location Value) : Prop :=
  atom.IsWrite ∧ ¬ atom.IsInitial

/-!
A global initializer has no source thread.  A freshly allocated queue node's
`next` initializer instead has an owner thread and retains its ordinary
program-order position before publication.
-/
def IsGlobalInitial (atom : Atom Location Value) : Prop :=
  atom.IsInitial ∧ atom.thread? = none

theorem isWrite_of_writtenValue
    {atom : Atom Location Value}
    {value : Value}
    (written : atom.writtenValue = some value) :
    atom.IsWrite := by
  change atom.access.writtenValue = some value at written
  change atom.access.IsWrite
  generalize atom.access = access at written ⊢
  cases access <;>
    simp [Access.writtenValue, Access.IsWrite] at written ⊢

theorem isNoninitialWrite_of_isRMW
    {atom : Atom Location Value}
    (isRMW : atom.IsRMW) :
    atom.IsNoninitialWrite := by
  change atom.access.IsRMW at isRMW
  change atom.access.IsWrite ∧ ¬ atom.access.IsInitial
  generalize atom.access = access at isRMW ⊢
  cases access <;>
    simp [Access.IsRMW, Access.IsWrite, Access.IsInitial] at isRMW ⊢

end Atom

/-!
`modificationOrder location` contains exactly the write identifiers at that
location, including its unique initializer.
-/
structure Candidate (Location Value : Type) where
  atoms : List (Atom Location Value)
  readSources : List (EventId × EventId)
  modificationOrder : Location → List EventId

/-- First source associated with a target identifier, if present. -/
def sourceFor :
    List (EventId × EventId) → EventId → Option EventId
  | [], _ => none
  | (candidateTarget, candidateSource) :: rest, target =>
      if candidateTarget = target then
        some candidateSource
      else
        sourceFor rest target

namespace Candidate

def atomIds (candidate : Candidate Location Value) : List EventId :=
  candidate.atoms.map Atom.id

def sourceId
    (candidate : Candidate Location Value)
    (target : EventId) : Option EventId :=
  sourceFor candidate.readSources target

def Represents
    (candidate : Candidate Location Value)
    (location : Location) : Prop :=
  ∃ atom,
    atom ∈ candidate.atoms ∧ atom.location = location

def InitializerAt
    (candidate : Candidate Location Value)
    (location : Location)
    (initializer : Atom Location Value) : Prop :=
  initializer ∈ candidate.atoms ∧
    initializer.location = location ∧
    initializer.IsInitial

/--
Canonical carrier restriction of the finite reads-from source function.
Requiring this as a fixed point excludes duplicate and off-carrier entries.
-/
def canonicalReadSources
    (candidate : Candidate Location Value) :
    List (EventId × EventId) :=
  candidate.atoms.filterMap fun target =>
    (candidate.sourceId target.id).map fun source =>
      (target.id, source)

end Candidate

/-- Strict position order on identifiers in an explicit finite list. -/
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

namespace IdBefore

theorem first_mem
    {first second : EventId}
    {order : List EventId}
    (before : IdBefore first second order) :
    first ∈ order :=
  before.1

theorem second_mem
    {first second : EventId}
    {order : List EventId}
    (before : IdBefore first second order) :
    second ∈ order :=
  before.2.1

theorem irreflexive
    {eventId : EventId}
    {order : List EventId} :
    ¬ IdBefore eventId eventId order := by
  rintro ⟨_, _, impossible⟩
  exact Nat.lt_irrefl _ impossible

theorem transitive
    {first middle last : EventId}
    {order : List EventId}
    (firstMiddle : IdBefore first middle order)
    (middleLast : IdBefore middle last order) :
    IdBefore first last order :=
  ⟨firstMiddle.1, middleLast.2.1,
    Nat.lt_trans firstMiddle.2.2 middleLast.2.2⟩

/-- The head of a list precedes every different member of its tail. -/
theorem head
    {head later : EventId}
    {tail : List EventId}
    (different : head ≠ later)
    (member : later ∈ tail) :
    IdBefore head later (head :: tail) := by
  refine ⟨by simp, by simp [member], ?_⟩
  simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
    if_neg different]
  exact Nat.zero_lt_succ _

/-- A strict order in a tail is preserved when a fresh head is added. -/
theorem cons
    {first second head : EventId}
    {tail : List EventId}
    (headFresh : head ∉ tail)
    (before : IdBefore first second tail) :
    IdBefore first second (head :: tail) := by
  have headNeFirst : head ≠ first := by
    intro same
    subst first
    exact headFresh before.first_mem
  have headNeSecond : head ≠ second := by
    intro same
    subst second
    exact headFresh before.second_mem
  refine ⟨by simp [before.first_mem], by simp [before.second_mem], ?_⟩
  simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
    if_neg headNeFirst, if_neg headNeSecond]
  exact Nat.add_lt_add_right before.2.2 1

/-- A duplicate-free list containing `[first, second]` as a sublist places
`first` strictly before `second`. -/
theorem of_pair_sublist
    {first second : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (orderedPair : [first, second].Sublist order) :
    IdBefore first second order := by
  induction order with
  | nil => simp at orderedPair
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp noDuplicates).1
      have tailNodup := (List.nodup_cons.mp noDuplicates).2
      cases orderedPair with
      | cons _ pairInTail =>
          exact IdBefore.cons headFresh
            (inductionHypothesis tailNodup pairInTail)
      | cons_cons _ secondInTail =>
          have secondMember : second ∈ tail :=
            secondInTail.subset (by simp)
          exact IdBefore.head
            (by
              intro same
              subst second
              exact headFresh secondMember)
            secondMember

/-- Distinct members of a duplicate-free identifier list are comparable. -/
theorem total
    {first second : EventId}
    {order : List EventId}
    (noDuplicates : order.Nodup)
    (firstMember : first ∈ order)
    (secondMember : second ∈ order)
    (different : first ≠ second) :
    IdBefore first second order ∨ IdBefore second first order := by
  induction order with
  | nil => simp at firstMember
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp noDuplicates).1
      have tailNodup := (List.nodup_cons.mp noDuplicates).2
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with firstIsHead | firstInTail
      · subst first
        rcases secondMember with secondIsHead | secondInTail
        · exact (different secondIsHead.symm).elim
        · exact Or.inl (IdBefore.head different secondInTail)
      · rcases secondMember with secondIsHead | secondInTail
        · subst second
          exact Or.inr (IdBefore.head different.symm firstInTail)
        · rcases inductionHypothesis tailNodup firstInTail secondInTail with
            firstBefore | secondBefore
          · exact Or.inl (IdBefore.cons headFresh firstBefore)
          · exact Or.inr (IdBefore.cons headFresh secondBefore)

end IdBefore

/-!
Program order contains global-initializer edges and exact same-thread source
order.  A thread-owned dynamic initializer uses only the second branch.
-/
def PO (candidate : Candidate Location Value) :
    Rel (Atom Location Value) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      ((source.IsGlobalInitial ∧ ¬ target.IsGlobalInitial) ∨
        ∃ thread,
          source.thread? = some thread ∧
            target.thread? = some thread ∧
            IdBefore source.id target.id candidate.atomIds)

/-!
Reads-from is intrinsically typed by carrier, access shape, location, and
value.  Well-formedness later makes it total and functional on reads.
-/
def RF (candidate : Candidate Location Value) :
    Rel (Atom Location Value) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      source.IsWrite ∧
      target.IsRead ∧
      source.location = target.location ∧
      source.writtenValue = target.readValue ∧
      candidate.sourceId target.id = some source.id

/-- Strict per-location modification order on writes. -/
def MO (candidate : Candidate Location Value) :
    Rel (Atom Location Value) :=
  fun source target =>
    source ∈ candidate.atoms ∧
      target ∈ candidate.atoms ∧
      source.IsWrite ∧
      target.IsWrite ∧
      source.location = target.location ∧
      IdBefore source.id target.id
        (candidate.modificationOrder source.location)

/-- From-read: a read precedes every later write after its RF source. -/
def RB (candidate : Candidate Location Value) :
    Rel (Atom Location Value) :=
  fun read laterWrite =>
    ∃ source,
      RF candidate source read ∧
        MO candidate source laterWrite ∧
        read ≠ laterWrite

/-- Nonempty transitive closure of `rf ∪ mo ∪ rb`. -/
inductive ECO (candidate : Candidate Location Value) :
    Rel (Atom Location Value) where
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

/-- Consecutive writes in their common location's modification order. -/
def ImmediateMO
    (candidate : Candidate Location Value)
    (source target : Atom Location Value) : Prop :=
  source ∈ candidate.atoms ∧
    target ∈ candidate.atoms ∧
    source.IsWrite ∧
    target.IsWrite ∧
    source.location = target.location ∧
    IdAdjacent source.id target.id
      (candidate.modificationOrder source.location)

/--
The non-fence RC11 release sequence of a write.

Besides the head itself, its base may be a later same-thread write at the
same location.  Further members are RMW events that read from the preceding
member.  RMW atomicity is a separate well-formedness obligation: it turns
that reads-from edge into adjacency in modification order.
-/
inductive ReleaseSequence
    (candidate : Candidate Location Value)
    (head : Atom Location Value) :
    Atom Location Value → Prop where
  | head
      (member : head ∈ candidate.atoms)
      (isWrite : head.IsNoninitialWrite) :
      ReleaseSequence candidate head head
  | sameThreadWrite {member} :
      head.IsNoninitialWrite →
      PO candidate head member →
      head.location = member.location →
      member.IsNoninitialWrite →
      ReleaseSequence candidate head member
  | rmw {previous next} :
      ReleaseSequence candidate head previous →
      RF candidate previous next →
      next.IsRMW →
      ReleaseSequence candidate head next

/-- Release-sequence synchronization with an acquiring RF target. -/
def SW (candidate : Candidate Location Value) :
    Rel (Atom Location Value) :=
  fun release acquire =>
    ∃ source,
      ReleaseSequence candidate release source ∧
        RF candidate source acquire ∧
        release.order.hasRelease = true ∧
        acquire.order.hasAcquire = true

/-- Nonempty transitive closure of program order and synchronizes-with. -/
inductive HB (candidate : Candidate Location Value) :
    Rel (Atom Location Value) where
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

/-- Nonempty transitive closure of program order and reads-from. -/
inductive CausalOrder (candidate : Candidate Location Value) :
    Rel (Atom Location Value) where
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

def Acyclic (relation : Rel α) : Prop :=
  ∀ element, ¬ relation element element

/-- Non-SC RC11 coherence: `hb ; eco?` is irreflexive. -/
def Coherent (candidate : Candidate Location Value) : Prop :=
  ∀ {source middle},
    HB candidate source middle →
      source ≠ middle ∧
        ¬ ECO candidate middle source

/-!
Finite structural well-formedness.  Only locations represented by the finite
carrier require an initializer, so an infinite logical site type such as
`next NodeId` causes no infinitary obligation.
-/
structure WellFormed
    (candidate : Candidate Location Value) : Prop where
  atomIdsNodup :
    candidate.atomIds.Nodup
  orderSupported :
    ∀ atom,
      atom ∈ candidate.atoms →
      atom.access.Allows atom.order
  threadlessIsInitial :
    ∀ atom,
      atom ∈ candidate.atoms →
      atom.thread? = none →
      atom.IsInitial
  initializerExistsUnique :
    ∀ location,
      candidate.Represents location →
      ∃ initializer,
        candidate.InitializerAt location initializer ∧
          ∀ other,
            candidate.InitializerAt location other →
            other = initializer
  modificationOrderNodup :
    ∀ location,
      (candidate.modificationOrder location).Nodup
  modificationOrderExact :
    ∀ location eventId,
      eventId ∈ candidate.modificationOrder location ↔
        ∃ atom,
          atom ∈ candidate.atoms ∧
            atom.location = location ∧
            atom.id = eventId ∧
            atom.IsWrite
  initializerFirst :
    ∀ {initializer later},
      candidate.InitializerAt initializer.location initializer →
      later ∈ candidate.atoms →
      later.location = initializer.location →
      later.IsWrite →
      later ≠ initializer →
      IdBefore initializer.id later.id
        (candidate.modificationOrder initializer.location)
  sourceSpec :
    ∀ target,
      target ∈ candidate.atoms →
      match target.readValue with
      | none =>
          candidate.sourceId target.id = none
      | some value =>
          ∃ source,
            source ∈ candidate.atoms ∧
              source.location = target.location ∧
              source.writtenValue = some value ∧
              candidate.sourceId target.id = some source.id
  readSourcesCanonical :
    candidate.readSources = candidate.canonicalReadSources
  rmwReadsImmediatePredecessor :
    ∀ {source rmw},
      RF candidate source rmw →
      rmw.IsRMW →
      ImmediateMO candidate source rmw

/-- Structural validity plus the two independent RC11 consistency clauses. -/
structure Valid
    (candidate : Candidate Location Value) : Prop
    extends WellFormed candidate where
  noThinAir :
    Acyclic (CausalOrder candidate)
  coherence :
    Coherent candidate

namespace WellFormed

private theorem eq_of_mem_of_map_nodup
    {items : List β}
    {mapKey : β → γ}
    (keysNodup : (items.map mapKey).Nodup)
    {left right : β}
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameKey : mapKey left = mapKey right) :
    left = right := by
  induction items with
  | nil =>
      simp at leftMember
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp keysNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftIsHead | leftInTail
      · subst left
        rcases rightMember with rightIsHead | rightInTail
        · exact rightIsHead.symm
        · exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨right, rightInTail, sameKey.symm⟩)
      · rcases rightMember with rightIsHead | rightInTail
        · subst right
          exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨left, leftInTail, sameKey⟩)
        · exact inductionHypothesis nodupParts.2
            leftInTail rightInTail

/-- Represented identifiers select at most one carrier atom. -/
theorem atom_eq_of_id_eq
    {candidate : Candidate Location Value}
    (wellFormed : WellFormed candidate)
    {left right : Atom Location Value}
    (leftMember : left ∈ candidate.atoms)
    (rightMember : right ∈ candidate.atoms)
    (sameId : left.id = right.id) :
    left = right :=
  eq_of_mem_of_map_nodup wellFormed.atomIdsNodup
    leftMember rightMember sameId

/-- Modification order is total on represented writes at one location. -/
theorem modificationOrder_total
    {candidate : Candidate Location Value}
    (wellFormed : WellFormed candidate)
    {first second : Atom Location Value}
    (firstMember : first ∈ candidate.atoms)
    (secondMember : second ∈ candidate.atoms)
    (firstWrite : first.IsWrite)
    (secondWrite : second.IsWrite)
    (sameLocation : first.location = second.location) :
    first = second ∨
      MO candidate first second ∨
      MO candidate second first := by
  by_cases sameId : first.id = second.id
  · exact Or.inl
      (wellFormed.atom_eq_of_id_eq firstMember secondMember sameId)
  · have firstIdMember :
        first.id ∈ candidate.modificationOrder first.location :=
      (wellFormed.modificationOrderExact first.location first.id).2
        ⟨first, firstMember, rfl, rfl, firstWrite⟩
    have secondIdMember :
        second.id ∈ candidate.modificationOrder first.location :=
      (wellFormed.modificationOrderExact first.location second.id).2
        ⟨second, secondMember, sameLocation.symm, rfl, secondWrite⟩
    rcases IdBefore.total
        (wellFormed.modificationOrderNodup first.location)
        firstIdMember secondIdMember sameId with
      firstBefore | secondBefore
    · exact Or.inr (Or.inl
        ⟨firstMember, secondMember, firstWrite, secondWrite,
          sameLocation, firstBefore⟩)
    · have converted :
          IdBefore second.id first.id
            (candidate.modificationOrder second.location) := by
        simpa [sameLocation] using secondBefore
      exact Or.inr (Or.inr
        ⟨secondMember, firstMember, secondWrite, firstWrite,
          sameLocation.symm, converted⟩)

/-- Reads-from is functional on represented targets. -/
theorem rf_functional
    {candidate : Candidate Location Value}
    (wellFormed : WellFormed candidate)
    {first second target : Atom Location Value}
    (firstReadsFrom : RF candidate first target)
    (secondReadsFrom : RF candidate second target) :
    first = second := by
  have sameId : first.id = second.id := by
    have firstChosen := firstReadsFrom.2.2.2.2.2.2
    have secondChosen := secondReadsFrom.2.2.2.2.2.2
    rw [firstChosen] at secondChosen
    exact Option.some.inj secondChosen
  exact wellFormed.atom_eq_of_id_eq
    firstReadsFrom.1 secondReadsFrom.1 sameId

/-- Every represented read has its typed reads-from edge. -/
theorem everyRead_hasSource
    {candidate : Candidate Location Value}
    (wellFormed : WellFormed candidate)
    {target : Atom Location Value}
    (targetMember : target ∈ candidate.atoms)
    (targetRead : target.IsRead) :
    ∃ source, RF candidate source target := by
  cases accessShape : target.access with
  | initial value =>
      simp [Atom.IsRead, Access.IsRead, accessShape] at targetRead
  | store value =>
      simp [Atom.IsRead, Access.IsRead, accessShape] at targetRead
  | load value =>
      have sourceSpec := wellFormed.sourceSpec target targetMember
      simp [Atom.readValue, Access.readValue, accessShape] at sourceSpec
      obtain ⟨source, sourceMember, sameLocation,
        sameValue, chosen⟩ := sourceSpec
      refine ⟨source, sourceMember, targetMember, ?_, ?_,
        sameLocation, ?_, chosen⟩
      · exact Atom.isWrite_of_writtenValue sameValue
      · simp [Atom.IsRead, Access.IsRead, accessShape]
      · simpa [Atom.writtenValue, Atom.readValue,
          Access.writtenValue, Access.readValue, accessShape]
          using sameValue
  | rmw read written =>
      have sourceSpec := wellFormed.sourceSpec target targetMember
      simp [Atom.readValue, Access.readValue, accessShape] at sourceSpec
      obtain ⟨source, sourceMember, sameLocation,
        sameValue, chosen⟩ := sourceSpec
      refine ⟨source, sourceMember, targetMember, ?_, ?_,
        sameLocation, ?_, chosen⟩
      · exact Atom.isWrite_of_writtenValue sameValue
      · simp [Atom.IsRead, Access.IsRead, accessShape]
      · simpa [Atom.writtenValue, Atom.readValue,
          Access.writtenValue, Access.readValue, accessShape]
          using sameValue

end WellFormed

namespace PO

theorem closed
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : PO candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms :=
  ⟨edge.1, edge.2.1⟩

theorem irreflexive
    {candidate : Candidate Location Value}
    (atom : Atom Location Value) :
    ¬ PO candidate atom atom := by
  rintro ⟨_, _, global | sameThread⟩
  · exact global.2 global.1
  · obtain ⟨_, _, _, before⟩ := sameThread
    exact IdBefore.irreflexive before

end PO

namespace RF

theorem closed
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : RF candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms :=
  ⟨edge.1, edge.2.1⟩

theorem sameLocation
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : RF candidate source target) :
    source.location = target.location :=
  edge.2.2.2.2.1

theorem valueAgreement
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : RF candidate source target) :
    source.writtenValue = target.readValue :=
  edge.2.2.2.2.2.1

end RF

namespace MO

theorem closed
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : MO candidate source target) :
    source ∈ candidate.atoms ∧ target ∈ candidate.atoms :=
  ⟨edge.1, edge.2.1⟩

theorem writes
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : MO candidate source target) :
    source.IsWrite ∧ target.IsWrite :=
  ⟨edge.2.2.1, edge.2.2.2.1⟩

theorem sameLocation
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : MO candidate source target) :
    source.location = target.location :=
  edge.2.2.2.2.1

theorem irreflexive
    {candidate : Candidate Location Value}
    (atom : Atom Location Value) :
    ¬ MO candidate atom atom := by
  rintro ⟨_, _, _, _, _, before⟩
  exact IdBefore.irreflexive before

theorem transitive
    {candidate : Candidate Location Value}
    {first middle last : Atom Location Value}
    (firstMiddle : MO candidate first middle)
    (middleLast : MO candidate middle last) :
    MO candidate first last := by
  obtain ⟨firstMember, _, firstWrite, _, firstMiddleLocation,
    firstMiddleBefore⟩ := firstMiddle
  obtain ⟨_, lastMember, _, lastWrite, middleLastLocation,
    middleLastBefore⟩ := middleLast
  refine ⟨firstMember, lastMember, firstWrite, lastWrite,
    firstMiddleLocation.trans middleLastLocation, ?_⟩
  have converted :
      IdBefore middle.id last.id
        (candidate.modificationOrder first.location) := by
    simpa [firstMiddleLocation] using middleLastBefore
  exact IdBefore.transitive firstMiddleBefore converted

end MO

namespace RB

theorem sameLocation
    {candidate : Candidate Location Value}
    {read laterWrite : Atom Location Value}
    (edge : RB candidate read laterWrite) :
    read.location = laterWrite.location := by
  obtain ⟨source, readsFrom, modificationOrder, _⟩ := edge
  exact readsFrom.sameLocation.symm.trans modificationOrder.sameLocation

end RB

namespace ECO

theorem sameLocation
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (path : ECO candidate source target) :
    source.location = target.location := by
  induction path with
  | readsFrom edge => exact edge.sameLocation
  | modificationOrder edge => exact edge.sameLocation
  | readsBefore edge => exact edge.sameLocation
  | transitive _ _ firstSame secondSame =>
      exact firstSame.trans secondSame

end ECO

namespace ImmediateMO

theorem sameLocation
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : ImmediateMO candidate source target) :
    source.location = target.location :=
  edge.2.2.2.2.1

theorem toModificationOrder
    {candidate : Candidate Location Value}
    {source target : Atom Location Value}
    (edge : ImmediateMO candidate source target) :
    MO candidate source target :=
  ⟨edge.1, edge.2.1, edge.2.2.1, edge.2.2.2.1,
    edge.2.2.2.2.1, edge.2.2.2.2.2.1⟩

/-- A write has at most one immediate modification-order successor. -/
theorem target_eq
    {candidate : Candidate Location Value}
    (wellFormed : WellFormed candidate)
    {source first second : Atom Location Value}
    (firstImmediate : ImmediateMO candidate source first)
    (secondImmediate : ImmediateMO candidate source second) :
    first = second := by
  by_cases sameId : first.id = second.id
  · exact wellFormed.atom_eq_of_id_eq
      firstImmediate.2.1 secondImmediate.2.1 sameId
  · have firstAdjacent := firstImmediate.2.2.2.2.2
    have secondAdjacent := secondImmediate.2.2.2.2.2
    rcases IdBefore.total
        (wellFormed.modificationOrderNodup source.location)
        firstAdjacent.1.second_mem secondAdjacent.1.second_mem sameId with
      firstBeforeSecond | secondBeforeFirst
    · exact (secondAdjacent.2 first.id
        ⟨firstAdjacent.1, firstBeforeSecond⟩).elim
    · exact (firstAdjacent.2 second.id
        ⟨secondAdjacent.1, secondBeforeFirst⟩).elim

end ImmediateMO

namespace ReleaseSequence

theorem headNoninitialWrite
    {candidate : Candidate Location Value}
    {head member : Atom Location Value}
    (sequence : ReleaseSequence candidate head member) :
    head.IsNoninitialWrite := by
  induction sequence with
  | head _ headWrite => exact headWrite
  | sameThreadWrite headWrite => exact headWrite
  | rmw _ _ _ inductionHypothesis => exact inductionHypothesis

theorem memberNoninitialWrite
    {candidate : Candidate Location Value}
    {head member : Atom Location Value}
    (sequence : ReleaseSequence candidate head member) :
    member.IsNoninitialWrite := by
  cases sequence with
  | head _ headWrite => exact headWrite
  | sameThreadWrite _ _ _ memberWrite => exact memberWrite
  | rmw _ _ isRMW => exact Atom.isNoninitialWrite_of_isRMW isRMW

theorem sameLocation
    {candidate : Candidate Location Value}
    {head member : Atom Location Value}
    (sequence : ReleaseSequence candidate head member) :
    head.location = member.location := by
  induction sequence with
  | head => rfl
  | sameThreadWrite _ _ sameLocation _ =>
      exact sameLocation
  | rmw _ readsFrom _ previousSame =>
      exact previousSame.trans readsFrom.sameLocation

end ReleaseSequence

namespace SW

theorem sameLocation
    {candidate : Candidate Location Value}
    {release acquire : Atom Location Value}
    (edge : SW candidate release acquire) :
    release.location = acquire.location := by
  obtain ⟨source, sequence, readsFrom, _, _⟩ := edge
  exact sequence.sameLocation.trans readsFrom.sameLocation

end SW

namespace Valid

/-- Coherence already excludes happens-before cycles. -/
theorem happensBeforeAcyclic
    {candidate : Candidate Location Value}
    (valid : Valid candidate) :
    Acyclic (HB candidate) := by
  intro atom cycle
  exact (valid.coherence cycle).1 rfl

/-- No nonempty `(po ∪ rf)` path may return to its source. -/
theorem noProgramOrderReadsFromCycle
    {candidate : Candidate Location Value}
    (valid : Valid candidate)
    (atom : Atom Location Value) :
    ¬ CausalOrder candidate atom atom :=
  valid.noThinAir atom

/-- No happens-before edge may be followed back by extended coherence. -/
theorem noHappensBeforeECOReturn
    {candidate : Candidate Location Value}
    (valid : Valid candidate)
    {source middle : Atom Location Value}
    (happensBefore : HB candidate source middle) :
    ¬ ECO candidate middle source :=
  (valid.coherence happensBefore).2

end Valid

/-!
A common finite rank is a convenient checked certificate for consistency.
It is not an extra RC11 relation; clients may prove consistency directly.
-/
structure OrderWitness
    (candidate : Candidate Location Value) where
  rank : Atom Location Value → Nat
  programOrderIncreases :
    ∀ {source target},
      PO candidate source target → rank source < rank target
  readsFromIncreases :
    ∀ {source target},
      RF candidate source target → rank source < rank target
  modificationOrderIncreases :
    ∀ {source target},
      MO candidate source target → rank source < rank target
  readsBeforeIncreases :
    ∀ {source target},
      RB candidate source target → rank source < rank target

namespace OrderWitness

theorem releaseSequenceDoesNotDecrease
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate)
    {head member : Atom Location Value}
    (sequence : ReleaseSequence candidate head member) :
    witness.rank head ≤ witness.rank member := by
  induction sequence with
  | head => exact Nat.le_refl _
  | sameThreadWrite _ programOrder _ _ =>
      exact Nat.le_of_lt
        (witness.programOrderIncreases programOrder)
  | rmw _ readsFrom _ previousDoesNotDecrease =>
      exact Nat.le_of_lt
        (Nat.lt_of_le_of_lt previousDoesNotDecrease
          (witness.readsFromIncreases readsFrom))

theorem synchronizesWithIncreases
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate)
    {release acquire : Atom Location Value}
    (edge : SW candidate release acquire) :
    witness.rank release < witness.rank acquire := by
  obtain ⟨source, sequence, readsFrom, _, _⟩ := edge
  exact Nat.lt_of_le_of_lt
    (witness.releaseSequenceDoesNotDecrease sequence)
    (witness.readsFromIncreases readsFrom)

theorem causalOrderIncreases
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate)
    {source target : Atom Location Value}
    (path : CausalOrder candidate source target) :
    witness.rank source < witness.rank target := by
  induction path with
  | programOrder edge =>
      exact witness.programOrderIncreases edge
  | readsFrom edge =>
      exact witness.readsFromIncreases edge
  | transitive _ _ firstIncreases secondIncreases =>
      exact Nat.lt_trans firstIncreases secondIncreases

theorem extendedCoherenceIncreases
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate)
    {source target : Atom Location Value}
    (path : ECO candidate source target) :
    witness.rank source < witness.rank target := by
  induction path with
  | readsFrom edge =>
      exact witness.readsFromIncreases edge
  | modificationOrder edge =>
      exact witness.modificationOrderIncreases edge
  | readsBefore edge =>
      exact witness.readsBeforeIncreases edge
  | transitive _ _ firstIncreases secondIncreases =>
      exact Nat.lt_trans firstIncreases secondIncreases

theorem happensBeforeIncreases
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate)
    {source target : Atom Location Value}
    (path : HB candidate source target) :
    witness.rank source < witness.rank target := by
  induction path with
  | programOrder edge =>
      exact witness.programOrderIncreases edge
  | synchronizesWith edge =>
      exact witness.synchronizesWithIncreases edge
  | transitive _ _ firstIncreases secondIncreases =>
      exact Nat.lt_trans firstIncreases secondIncreases

theorem noThinAir
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate) :
    Acyclic (CausalOrder candidate) := by
  intro atom cycle
  exact Nat.lt_irrefl _ (witness.causalOrderIncreases cycle)

theorem coherent
    {candidate : Candidate Location Value}
    (witness : OrderWitness candidate) :
    Coherent candidate := by
  intro source middle happensBefore
  have forward := witness.happensBeforeIncreases happensBefore
  constructor
  · intro equal
    subst middle
    exact Nat.lt_irrefl _ forward
  · intro backwards
    have reverse := witness.extendedCoherenceIncreases backwards
    exact (Nat.not_lt_of_ge (Nat.le_of_lt forward)) reverse

end OrderWitness

end WeakMemory.MultiLocationRC11
