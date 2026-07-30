import WeakMemory.TreiberC11V1DerivedOrder
import WeakMemory.TreiberC11V1Infinite

namespace WeakMemory.TreiberC11V1

/-!
# Infinite RC11 executions

This module connects one infinite Treiber source execution to the existing
finite declarative RC11 semantics.  It makes no liveness claim.  Instead, it
requires every finite source prefix to have a declarative execution whose
payload, reads-from source function, and modification order are restrictions
of single global objects.

The restriction fields are essential: a family of unrelated valid finite
executions would not describe one coherent infinite execution.
-/

/--
One coherent infinite source/RC11 execution.

The global modification order is a strict relation on event identifiers.
Every pair of atoms that has appeared in a finite prefix is related by the
finite candidate's `RC11.MO` exactly when its identifiers are related
globally.  Requiring this for all in-prefix atoms is slightly stronger than
requiring it only for pairs already known to be writes.
-/
structure InfiniteRC11Execution (α : Type) (threadCount : Nat) where
  /-- The single infinite source execution represented by every prefix. -/
  source :
    InfiniteExecution α threadCount
  /-- The immutable payload table shared by all finite prefixes. -/
  payload :
    NodeId → α
  /-- The global reads-from source lookup, indexed by target event ID. -/
  readSource :
    EventId → Option EventId
  /-- The global strict modification-order relation on event IDs. -/
  modificationOrder :
    EventId → EventId → Prop
  modificationOrderIrreflexive :
    ∀ event, ¬ modificationOrder event event
  modificationOrderTransitive :
    ∀ {first middle last},
      modificationOrder first middle →
      modificationOrder middle last →
      modificationOrder first last
  /-- The existing finite declarative execution for each source prefix. -/
  finitePrefix :
    Nat → DeclarativeExecution α
  prefixTrace :
    ∀ length,
      (finitePrefix length).candidate.trace =
        source.tracePrefix length
  prefixPayload :
    ∀ length,
      (finitePrefix length).candidate.payload = payload
  prefixReadSource :
    ∀ length (atom : RC11.Atom α),
      atom ∈ (finitePrefix length).candidate.atoms →
        (finitePrefix length).candidate.sourceId atom.id =
          readSource atom.id
  /-- Every global reads-from endpoint occurs in one common finite prefix. -/
  readSourceSupported :
    ∀ {targetId sourceId},
      readSource targetId = some sourceId →
        ∃ length,
          ∃ sourceAtom targetAtom : RC11.Atom α,
          sourceAtom ∈
              (finitePrefix length).candidate.atoms ∧
            targetAtom ∈
              (finitePrefix length).candidate.atoms ∧
            sourceAtom.id = sourceId ∧
            targetAtom.id = targetId
  prefixModificationOrder :
    ∀ length (first second : RC11.Atom α),
      first ∈ (finitePrefix length).candidate.atoms →
      second ∈ (finitePrefix length).candidate.atoms →
        (RC11.MO (finitePrefix length).candidate first second ↔
          modificationOrder first.id second.id)
  /-- Every global modification-order endpoint occurs in one common prefix. -/
  modificationOrderSupported :
    ∀ {firstId secondId},
      modificationOrder firstId secondId →
        ∃ length,
          ∃ first second : RC11.Atom α,
          first ∈
              (finitePrefix length).candidate.atoms ∧
            second ∈
              (finitePrefix length).candidate.atoms ∧
            first.id = firstId ∧
            second.id = secondId

namespace InfiniteRC11Execution

/-- Expose one finite declarative prefix through a named projection. -/
def declarativePrefix
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    DeclarativeExecution α :=
  execution.finitePrefix length

/-- The projected declarative trace is exactly the source trace prefix. -/
@[simp] theorem declarativePrefix_trace
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    (execution.declarativePrefix length).candidate.trace =
      execution.source.tracePrefix length :=
  execution.prefixTrace length

/-- Every projected prefix uses the one global immutable payload table. -/
@[simp] theorem declarativePrefix_payload
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    (execution.declarativePrefix length).candidate.payload =
      execution.payload :=
  execution.prefixPayload length

/-- Reads-from lookup in a projected prefix is the global lookup restriction. -/
theorem declarativePrefix_readSource
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    (atom : RC11.Atom α)
    (member :
      atom ∈ (execution.declarativePrefix length).candidate.atoms) :
    (execution.declarativePrefix length).candidate.sourceId atom.id =
      execution.readSource atom.id :=
  execution.prefixReadSource length atom member

/--
Finite reads-from is exactly the restriction of the global source lookup to
atoms in the projected prefix.
-/
theorem declarativePrefix_readsFrom
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    (source target : RC11.Atom α)
    (sourceMember :
      source ∈ (execution.declarativePrefix length).candidate.atoms)
    (targetMember :
      target ∈ (execution.declarativePrefix length).candidate.atoms) :
    RC11.RF
        (execution.declarativePrefix length).candidate
        source target ↔
      execution.readSource target.id = some source.id := by
  simp only [RC11.RF, sourceMember, targetMember, true_and]
  rw [
    execution.declarativePrefix_readSource
      length target targetMember
  ]

/--
Finite modification order is exactly the restriction of global modification
order to atoms in the projected prefix.
-/
theorem declarativePrefix_modificationOrder
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat)
    (first second : RC11.Atom α)
    (firstMember :
      first ∈ (execution.declarativePrefix length).candidate.atoms)
    (secondMember :
      second ∈ (execution.declarativePrefix length).candidate.atoms) :
    RC11.MO
        (execution.declarativePrefix length).candidate
        first second ↔
      execution.modificationOrder first.id second.id :=
  execution.prefixModificationOrder
    length first second firstMember secondMember

/--
Every global reads-from association is represented by an actual RF edge in
one finite declarative prefix.
-/
theorem readSource_hasFiniteWitness
    (execution : InfiniteRC11Execution α threadCount)
    {targetId sourceId : EventId}
    (readsFrom : execution.readSource targetId = some sourceId) :
    ∃ length,
      ∃ source target : RC11.Atom α,
      source ∈
          (execution.declarativePrefix length).candidate.atoms ∧
        target ∈
          (execution.declarativePrefix length).candidate.atoms ∧
        source.id = sourceId ∧
        target.id = targetId ∧
        RC11.RF
          (execution.declarativePrefix length).candidate
          source target := by
  obtain ⟨length, source, target, sourceMember,
      targetMember, sourceIdExact, targetIdExact⟩ :=
    execution.readSourceSupported readsFrom
  refine
    ⟨length, source, target, sourceMember, targetMember,
      sourceIdExact, targetIdExact, ?_⟩
  rw [
    execution.declarativePrefix_readsFrom
      length source target sourceMember targetMember,
    targetIdExact,
    sourceIdExact
  ]
  exact readsFrom

/--
Every global modification-order edge is represented by an actual finite
`RC11.MO` edge with the same endpoint identifiers.
-/
theorem modificationOrder_hasFiniteWitness
    (execution : InfiniteRC11Execution α threadCount)
    {firstId secondId : EventId}
    (ordered :
      execution.modificationOrder firstId secondId) :
    ∃ length,
      ∃ first second : RC11.Atom α,
      first ∈
          (execution.declarativePrefix length).candidate.atoms ∧
        second ∈
          (execution.declarativePrefix length).candidate.atoms ∧
        first.id = firstId ∧
        second.id = secondId ∧
        RC11.MO
          (execution.declarativePrefix length).candidate
          first second := by
  obtain ⟨length, first, second, firstMember,
      secondMember, firstIdExact, secondIdExact⟩ :=
    execution.modificationOrderSupported ordered
  refine
    ⟨length, first, second, firstMember, secondMember,
      firstIdExact, secondIdExact, ?_⟩
  rw [
    execution.declarativePrefix_modificationOrder
      length first second firstMember secondMember,
    firstIdExact,
    secondIdExact
  ]
  exact ordered

/--
The projected declarative trace has the existing finite source `GlobalRun`.

This proof uses the infinite source execution, rather than accepting an
unrelated finite run witness.
-/
theorem declarativePrefix_globalRun
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    GlobalRun
      (execution.declarativePrefix length).candidate.trace := by
  rw [execution.declarativePrefix_trace length]
  exact execution.source.prefix_globalRun length

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
