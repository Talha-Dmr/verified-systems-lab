import WeakMemory.TreiberRelations

namespace WeakMemory.TreiberRC11

/-!
# Ranking constructed Treiber relations

`AtomicRelationData` supplies the concrete reads-from and modification-order
relations and proves their eleven structural well-formedness fields. This
module isolates the one remaining semantic ingredient: a common strict rank
for program order, reads-from, modification order, and reads-before.

The rank makes every extended-coherence edge increase. A release sequence is
nonstrictly increasing from its release head to the write read by an acquire,
so synchronization and consequently happens-before are strictly increasing as
well. These facts construct RC11 coherence without accepting it as a separate
certificate.
-/

/--
A common well-founded order for the four primitive relations used by the
single-location RC11 fragment.
-/
structure RC11OrderWitness
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton) where
  rank : Event α → Nat
  programOrder_lt :
    ∀ {source target},
      data.graph.programOrder source target →
      rank source < rank target
  readsFrom_lt :
    ∀ {source target},
      data.graph.readsFrom source target →
      rank source < rank target
  modificationOrder_lt :
    ∀ {source target},
      data.graph.modificationOrder source target →
      rank source < rank target
  readsBefore_lt :
    ∀ {source target},
      data.graph.ReadsBefore source target →
      rank source < rank target

namespace RC11OrderWitness

/-- Every extended-coherence path strictly increases the common rank. -/
theorem extendedCoherence_lt
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    order.rank source < order.rank target := by
  induction edge with
  | readsFrom readsFrom =>
      exact order.readsFrom_lt readsFrom
  | modificationOrder modificationOrder =>
      exact order.modificationOrder_lt modificationOrder
  | readsBefore readsBefore =>
      exact order.readsBefore_lt readsBefore
  | transitive first second firstLt secondLt =>
      exact Nat.lt_trans firstLt secondLt

/--
A release-sequence endpoint is either its head or has strictly greater rank.
-/
theorem releaseSequence_eq_or_lt
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {head source : Event α}
    (sequence : data.graph.ReleaseSequence head source) :
    head = source ∨ order.rank head < order.rank source := by
  induction sequence with
  | head member =>
      exact Or.inl rfl
  | @rmw previous next previousSequence immediate isRMW
      inductionHypothesis =>
      have previousBeforeNext :
          order.rank previous < order.rank next :=
        order.modificationOrder_lt immediate.2.2.1
      exact Or.inr <| by
        rcases inductionHypothesis with same | headBeforePrevious
        · subst previous
          exact previousBeforeNext
        · exact Nat.lt_trans headBeforePrevious previousBeforeNext

/-- Release sequences never decrease the common rank. -/
theorem releaseSequence_le
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {head source : Event α}
    (sequence : data.graph.ReleaseSequence head source) :
    order.rank head ≤ order.rank source := by
  rcases order.releaseSequence_eq_or_lt sequence with same | before
  · subst source
    exact Nat.le_refl _
  · exact Nat.le_of_lt before

/-- A nontrivial release sequence strictly increases the common rank. -/
theorem releaseSequence_lt
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {head source : Event α}
    (sequence : data.graph.ReleaseSequence head source)
    (different : head ≠ source) :
    order.rank head < order.rank source := by
  rcases order.releaseSequence_eq_or_lt sequence with same | before
  · exact (different same).elim
  · exact before

/-- Synchronization through a release sequence strictly increases rank. -/
theorem synchronizesWith_lt
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {release acquire : Event α}
    (synchronizes :
      data.graph.synchronizesWith release acquire) :
    order.rank release < order.rank acquire := by
  obtain ⟨source, sequence, readsFrom, _, _⟩ := synchronizes
  exact Nat.lt_of_le_of_lt
    (order.releaseSequence_le sequence)
    (order.readsFrom_lt readsFrom)

/-- Every happens-before path strictly increases the common rank. -/
theorem happensBefore_lt
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data)
    {source target : Event α}
    (happensBefore : data.graph.HappensBefore source target) :
    order.rank source < order.rank target := by
  induction happensBefore with
  | programOrder programOrder =>
      exact order.programOrder_lt programOrder
  | synchronizesWith synchronizesWith =>
      exact order.synchronizesWith_lt synchronizesWith
  | transitive first second firstLt secondLt =>
      exact Nat.lt_trans firstLt secondLt

/--
The common rank rules out both happens-before self-edges and a return path
through extended coherence.
-/
theorem coherent
    {skeleton : EventGraph.Skeleton α}
    {data : AtomicRelationData skeleton}
    (order : RC11OrderWitness data) :
    data.graph.Coherent := by
  intro source middle happensBefore
  have sourceBeforeMiddle :
      order.rank source < order.rank middle :=
    order.happensBefore_lt happensBefore
  constructor
  · intro same
    subst middle
    exact (Nat.lt_irrefl _) sourceBeforeMiddle
  · intro returns
    have middleBeforeSource :
        order.rank middle < order.rank source :=
      order.extendedCoherence_lt returns
    exact (Nat.lt_irrefl _)
      (Nat.lt_trans sourceBeforeMiddle middleBeforeSource)

end RC11OrderWitness

namespace AtomicRelationData

/--
The constructed relation fields and a common rank produce the complete
remaining-consistency certificate.
-/
theorem toRemainingConsistency
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (order : RC11OrderWitness data) :
    RemainingConsistency data.graph where
  toRemainingWellFormedRelations :=
    data.toRemainingWellFormedRelations
  coherence :=
    order.coherent

end AtomicRelationData

end WeakMemory.TreiberRC11
