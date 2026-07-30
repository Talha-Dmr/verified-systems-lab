import WeakMemory.TreiberRelationOrder
import WeakMemory.TreiberNodeAccess

namespace WeakMemory.TreiberRC11

/-!
# Canonical RC11 graphs from source executions

This module removes the arbitrary graph and manual
`RemainingConsistency` boundary from the main construction path.

A `SourceAtomicExecution` contains:

* one locally valid source skeleton;
* the actual finite semantic choices for atomic reads-from and modification
  order;
* a common rank certifying RC11 order consistency;
* the existing generated allocator/event typing certificate.

Its graph, carrier, program order, reads-from, and modification order are all
definitions. The eleven remaining well-formedness fields and coherence are
theorems. A later C-semantics translation or executable validator must produce
the relation data and rank witness; they are not inferred from source syntax,
because RC11 executions genuinely choose `rf` and `mo`.
-/

/--
A source-controlled atomic execution with constructively defined graph
relations and consistency.
-/
structure SourceAtomicExecution
    (initial : TreiberRA.State α) where
  source :
    ControlledSource initial
  relations :
    AtomicRelationData source.skeleton
  order :
    RC11OrderWitness relations
  allocator :
    AllocatorTable α
  initialHeadEmpty :
    initial.head = none
  generated :
    GeneratedEvents relations.graph initial allocator
      source.skeleton.events

namespace SourceAtomicExecution

/--
The canonical relation graph is a controlled candidate without an arbitrary
carrier permutation or separately supplied program-order equality.
-/
def toControlledCandidate
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    ControlledCandidate execution.relations.graph initial where
  source :=
    execution.source
  allocator :=
    execution.allocator
  initialHeadEmpty :=
    execution.initialHeadEmpty
  generated :=
    execution.generated
  eventsPermutation :=
    List.Perm.refl _
  programOrder_eq :=
    rfl

/-- The finite relation representation derives all graph consistency fields. -/
theorem toRemainingConsistency
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    RemainingConsistency execution.relations.graph :=
  execution.relations.toRemainingConsistency execution.order

/-- The canonical source execution derives full core consistency. -/
theorem toCoreConsistent
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    CoreConsistent execution.relations.graph :=
  execution.toControlledCandidate.toCoreConsistent
    execution.toRemainingConsistency

/-- The generated source execution derives the existing allocator typing. -/
def toGraphTyping
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    GraphTyping execution.relations.graph initial :=
  execution.toControlledCandidate.toGraphTyping

/--
End-to-end legal sequential history without accepting an arbitrary graph,
eleven relation fields, coherence, no-thin-air, or scheduling acyclicity as
manual premises.
-/
theorem linearizable
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : SourceAtomicExecution initial)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
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
  linearizable_of_remainingConsistency
    execution.toControlledCandidate
    execution.toRemainingConsistency
    initialRepresentation

end SourceAtomicExecution

/--
The canonical atomic execution paired with its source-level non-atomic
publication certificate.

This remains a reusable interface for independently certified candidates.
`TreiberNodeAccessDerivation` constructs it canonically from immutable-field
value agreement and the relation data.
-/
structure CSourceExecution
    (initial : TreiberRA.State α) where
  atomic :
    SourceAtomicExecution initial
  nodeAccess :
    NodeAccessCertificate atomic.toControlledCandidate

namespace CSourceExecution

/--
A C-shaped source execution supplies both the legal sequential result and the
auditable publication-safety certificate for every modeled `node->next` read.
-/
theorem linearizable_and_nodeSafe
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {initialValues : List α}
    (execution : CSourceExecution initial)
    (initialRepresentation :
      TreiberRA.Represents
        initial.heap initial.head initialValues) :
    NodeAccessCertificate
        execution.atomic.toControlledCandidate ∧
      ∃ schedule final finalValues,
        RespectsGraph
            execution.atomic.relations.graph schedule ∧
          replay? initial schedule = some final ∧
          TreiberRA.Represents
            final.heap final.head finalValues ∧
          StackSpec.Legal initialValues
            (Treiber.completedHistory
              (TreiberRA.commits
                (projectedActions schedule)))
            finalValues :=
  ⟨execution.nodeAccess,
    execution.atomic.linearizable initialRepresentation⟩

end CSourceExecution

end WeakMemory.TreiberRC11
