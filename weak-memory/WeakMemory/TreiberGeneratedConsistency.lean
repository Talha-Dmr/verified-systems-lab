import WeakMemory.TreiberControlledCandidate

namespace WeakMemory.TreiberRC11

/-!
# Completing consistency for source-controlled candidates

`ControlledCandidate` already constructs the finite event carrier, its unique
initializer, and exact same-thread program order. This module packages only
the relational obligations that remain for reads-from, modification order,
and successful RMW events.

Happens-before acyclicity and no-thin-air are not certificate fields:

* coherence directly makes happens-before irreflexive;
* causal order embeds into the combined scheduling order, whose acyclicity is
  derived from well-formedness and coherence.

The resulting reduced certificate therefore contains eleven graph-relation
fields and coherence, rather than repeating the source-constructed carrier
and program-order fields or separately assuming the two derived acyclicity
conditions.
-/

namespace Graph.CausalOrder

/-- Every causal-order path is a path in the combined scheduling relation. -/
theorem toOrderPath
    {graph : Graph α}
    {source target : Event α}
    (causal : graph.CausalOrder source target) :
    Relation.TransGen graph.OrderEdge source target := by
  induction causal with
  | programOrder programOrder =>
      exact Relation.TransGen.single (Or.inl programOrder)
  | readsFrom readsFrom =>
      exact Relation.TransGen.single
        (Or.inr
          (Graph.ExtendedCoherence.readsFrom readsFrom))
  | transitive first second firstPath secondPath =>
      exact Relation.TransGen.trans firstPath secondPath

end Graph.CausalOrder

/-- Scheduling-order acyclicity implies RC11 no-thin-air. -/
theorem noThinAir_of_orderAcyclic
    {graph : Graph α}
    (orderAcyclic : graph.OrderAcyclic) :
    Acyclic graph.CausalOrder := by
  intro event causalCycle
  exact orderAcyclic event causalCycle.toOrderPath

/-- The first conjunct of coherence already makes happens-before acyclic. -/
theorem happensBeforeAcyclic_of_coherent
    {graph : Graph α}
    (coherent : graph.Coherent) :
    Acyclic graph.HappensBefore := by
  intro event happensBeforeCycle
  exact (coherent happensBeforeCycle).1 rfl

/--
The eleven `WellFormed` fields not constructed by a controlled source
skeleton and not derivable from coherence.
-/
structure RemainingWellFormedRelations
    (graph : Graph α) : Prop where
  readsFromClosed :
    ∀ {source target},
      graph.readsFrom source target →
      source ∈ graph.events ∧ target ∈ graph.events
  modificationOrderClosed :
    ∀ {source target},
      graph.modificationOrder source target →
      source ∈ graph.events ∧ target ∈ graph.events
  readsFromValues :
    ∀ {source target},
      graph.readsFrom source target →
      ∃ value,
        source.writtenValue = some value ∧
        target.readValue = some value
  readsFromFunctional :
    ∀ {firstSource secondSource target},
      graph.readsFrom firstSource target →
      graph.readsFrom secondSource target →
      firstSource = secondSource
  everyReadHasSource :
    ∀ {target},
      target ∈ graph.events →
      target.IsRead →
      ∃ source, graph.readsFrom source target
  modificationOrderWrites :
    ∀ {source target},
      graph.modificationOrder source target →
      source.IsWrite ∧ target.IsWrite
  modificationOrderIrreflexive :
    ∀ event, ¬ graph.modificationOrder event event
  modificationOrderTransitive :
    ∀ {first middle last},
      graph.modificationOrder first middle →
      graph.modificationOrder middle last →
      graph.modificationOrder first last
  modificationOrderTotal :
    ∀ {left right},
      left ∈ graph.events →
      right ∈ graph.events →
      left.IsWrite →
      right.IsWrite →
      left ≠ right →
      graph.modificationOrder left right ∨
        graph.modificationOrder right left
  initialPrecedesWrites :
    ∀ {initial write},
      initial ∈ graph.events →
      initial.IsInitial →
      write ∈ graph.events →
      write.IsWrite →
      ¬ write.IsInitial →
      graph.modificationOrder initial write
  rmwReadsImmediatePredecessor :
    ∀ {source rmw},
      graph.readsFrom source rmw →
      rmw.IsRMW →
      graph.modificationOrder source rmw ∧
        ∀ middle,
          middle ∈ graph.events →
          middle.IsWrite →
          ¬ (graph.modificationOrder source middle ∧
            graph.modificationOrder middle rmw)

/--
The reduced consistency certificate: the eleven remaining relation fields
plus coherence.
-/
structure RemainingConsistency
    (graph : Graph α) : Prop
    extends RemainingWellFormedRelations graph where
  coherence :
    graph.Coherent

namespace ControlledCandidate

/--
A controlled carrier and the reduced consistency certificate reconstruct all
fields of `WellFormed`.
-/
theorem toWellFormed
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (candidate : ControlledCandidate graph initial)
    (certificate : RemainingConsistency graph) :
    WellFormed graph := by
  let carrier := candidate.toCarrierProgramOrderWellFormed
  exact {
    noDuplicateEvents :=
      carrier.noDuplicateEvents
    uniqueIds :=
      carrier.uniqueIds
    programOrderClosed :=
      carrier.programOrderClosed
    programOrderSameThread :=
      carrier.programOrderSameThread
    programOrderIrreflexive :=
      carrier.programOrderIrreflexive
    programOrderTransitive :=
      carrier.programOrderTransitive
    readsFromClosed :=
      certificate.readsFromClosed
    modificationOrderClosed :=
      certificate.modificationOrderClosed
    readsFromValues :=
      certificate.readsFromValues
    readsFromFunctional :=
      certificate.readsFromFunctional
    everyReadHasSource :=
      certificate.everyReadHasSource
    modificationOrderWrites :=
      certificate.modificationOrderWrites
    modificationOrderIrreflexive :=
      certificate.modificationOrderIrreflexive
    modificationOrderTransitive :=
      certificate.modificationOrderTransitive
    modificationOrderTotal :=
      certificate.modificationOrderTotal
    initialExistsUnique :=
      carrier.initialExistsUnique
    initialPrecedesWrites :=
      certificate.initialPrecedesWrites
    rmwReadsImmediatePredecessor :=
      certificate.rmwReadsImmediatePredecessor
    happensBeforeAcyclic :=
      happensBeforeAcyclic_of_coherent
        certificate.coherence
  }

/--
A controlled carrier and the reduced certificate reconstruct full core
consistency. No-thin-air is derived rather than supplied.
-/
theorem toCoreConsistent
    {graph : Graph α}
    {initial : TreiberRA.State α}
    (candidate : ControlledCandidate graph initial)
    (certificate : RemainingConsistency graph) :
    CoreConsistent graph := by
  let wellFormed := candidate.toWellFormed certificate
  have orderAcyclic : graph.OrderAcyclic :=
    orderAcyclic_of_wellFormed_coherent
      wellFormed certificate.coherence
  exact {
    toWellFormed := wellFormed
    noThinAir :=
      noThinAir_of_orderAcyclic orderAcyclic
    coherence :=
      certificate.coherence
  }

end ControlledCandidate

/--
End-to-end linearizability from the reduced remaining-consistency
certificate, without accepting a separately assembled `CoreConsistent`.
-/
theorem linearizable_of_remainingConsistency
    [DecidableEq α]
    {graph : Graph α}
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (candidate : ControlledCandidate graph initial)
    (certificate : RemainingConsistency graph)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    ∃ schedule final finalValues,
      RespectsGraph graph schedule ∧
        replay? initial schedule = some final ∧
        TreiberRA.Represents
          final.heap final.head finalValues ∧
        StackSpec.Legal initialValues
          (Treiber.completedHistory
            (TreiberRA.commits
              (projectedActions schedule)))
          finalValues :=
  CoreConsistent.linearizable_of_controlledCandidate
    (candidate.toCoreConsistent certificate)
    candidate
    initialRepresentation

end WeakMemory.TreiberRC11
