import WeakMemory.MemoryFairVisibility
import WeakMemory.MSQueueInfinite

namespace WeakMemory.MSQueue.Source

/-!
# Position-indexed memory fairness for the infinite Michael--Scott queue

The finite queue model uses three static atoms with identifiers `0`, `1`, and
`2`; dynamic source events then use canonical identifiers starting at `3`.
For temporal arguments we keep identifiers and source positions separate:
positions `0`, `1`, and `2` denote the static Head, Tail, and dummy-next
initializers, while transition `time` is represented by position `time + 3`.

Memory fairness is stated independently at every logical queue site.  This is
important for the infinitely many possible `.next node` sites: a visibility
argument selects one site first and consumes prefix-finiteness only there.
-/

namespace InfiniteRC11Execution

private theorem readValue_exists_of_isRead
    (atom : MultiLocationRC11.Atom Site Ptr)
    (read : atom.IsRead) :
    ∃ value, atom.readValue = some value := by
  change atom.access.IsRead at read
  change ∃ value, atom.access.readValue = some value
  generalize atom.access = access at read ⊢
  cases access <;>
    simp_all [MultiLocationRC11.Access.IsRead,
      MultiLocationRC11.Access.readValue]

/-- RC11 event identifier represented by one position in the source run. -/
def graphEventId?
    (execution : InfiniteRC11Execution Value threadCount dummy) :
    Nat → Option EventId
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | time + 3 =>
      match execution.source.event time with
      | .atomic occurrence => some occurrence.id
      | _ => none

/-- Global modification order at one site, lifted to source positions. -/
def ModificationOrderAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site)
    (first second : Nat) : Prop :=
  ∃ firstId secondId,
    execution.graphEventId? first = some firstId ∧
      execution.graphEventId? second = some secondId ∧
      execution.modificationOrder site firstId secondId

/-- Position-indexed from-read (`rf⁻¹ ; mo`) at one selected site. -/
def FromReadAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site)
    (read laterWrite : Nat) : Prop :=
  ∃ readId sourceId writeId,
    execution.graphEventId? read = some readId ∧
      execution.graphEventId? laterWrite = some writeId ∧
      execution.readSource readId = some sourceId ∧
      execution.modificationOrder site sourceId writeId ∧
      read ≠ laterWrite

/-- The coherent source run equipped with relations for one selected site. -/
def executionGraphAt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (site : Site) :
    Liveness.InfiniteExecutionGraph
      (GlobalStep (Value := Value)) where
  toInfiniteRun := execution.source.toInfiniteRun
  modificationOrder := execution.ModificationOrderAt site
  fromRead := execution.FromReadAt site

/-- Prefix-finite `mo` and `fr`, independently at every represented site. -/
def MemoryFair
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  ∀ site, Liveness.MemoryFair (execution.executionGraphAt site)

/-- The exact selected-site visibility premise used by progress. -/
def FromReadFair
    (execution : InfiniteRC11Execution Value threadCount dummy) : Prop :=
  ∀ site, Liveness.PrefixFinite (execution.FromReadAt site)

/-- Full per-site memory fairness supplies the `fr` visibility component. -/
theorem fromReadFair_of_memoryFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (memoryFair : execution.MemoryFair) :
    execution.FromReadFair := by
  intro site
  exact (memoryFair site).2

@[simp] theorem graphEventId?_headInitializer
    (execution : InfiniteRC11Execution Value threadCount dummy) :
    execution.graphEventId? 0 = some 0 :=
  rfl

@[simp] theorem graphEventId?_tailInitializer
    (execution : InfiniteRC11Execution Value threadCount dummy) :
    execution.graphEventId? 1 = some 1 :=
  rfl

@[simp] theorem graphEventId?_dummyNextInitializer
    (execution : InfiniteRC11Execution Value threadCount dummy) :
    execution.graphEventId? 2 = some 2 :=
  rfl

@[simp] theorem graphEventId?_atomic
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time : Nat)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence) :
    execution.graphEventId? (time + 3) = some occurrence.id := by
  simp [graphEventId?, event]

/-- One dynamic atomic event belongs to the supported prefix ending after it. -/
theorem occurrence_mem_supportedPrefix_atoms
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time : Nat)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence) :
    occurrence.toRC11Atom ∈
      (execution.supportedPrefix (time + 1)).candidate.atoms := by
  apply (execution.supportedPrefix (time + 1)).atomicAtom_mem
  apply List.mem_filterMap.mpr
  refine ⟨TraceEvent.atomic occurrence, ?_, rfl⟩
  unfold InfiniteExecution.tracePrefix
  apply List.mem_map.mpr
  exact ⟨time, by simp, event⟩

/-- Every earlier atomic event belongs to each sufficiently long prefix. -/
theorem occurrence_mem_supportedPrefix_atoms_of_lt
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time length : Nat)
    (beforeEnd : time < length)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence) :
    occurrence.toRC11Atom ∈
      (execution.supportedPrefix length).candidate.atoms := by
  apply (execution.supportedPrefix length).atomicAtom_mem
  apply List.mem_filterMap.mpr
  refine ⟨TraceEvent.atomic occurrence, ?_, rfl⟩
  unfold InfiniteExecution.tracePrefix
  apply List.mem_map.mpr
  exact ⟨time, by simp [beforeEnd], event⟩

/-- Every dynamic source atomic occurrence has one global reads-from source. -/
theorem readSource_exists_of_atomic
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time : Nat)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence)
    (read : occurrence.toRC11Atom.IsRead) :
    ∃ sourceId, execution.readSource occurrence.id = some sourceId := by
  let finiteExecution := execution.supportedPrefix (time + 1)
  have member : occurrence.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms time occurrence event
  obtain ⟨readValue, readValueEq⟩ :
      ∃ readValue, occurrence.toRC11Atom.readValue = some readValue := by
    exact readValue_exists_of_isRead occurrence.toRC11Atom read
  have sourceSpec :=
    finiteExecution.valid.sourceSpec occurrence.toRC11Atom member
  rw [readValueEq] at sourceSpec
  obtain ⟨source, sourceMember, sourceLocation, sourceValue, chosenSource⟩ :=
    sourceSpec
  refine ⟨source.id, ?_⟩
  have restrictionRaw :=
    execution.prefixReadSource (time + 1) occurrence.toRC11Atom member
  have restriction :
      finiteExecution.candidate.sourceId occurrence.toRC11Atom.id =
        execution.readSource occurrence.toRC11Atom.id := by
    exact restrictionRaw
  exact restriction.symm.trans chosenSource

/-- The RF source observed at one source transition. -/
def observedWrite
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time : Nat) : EventId :=
  match execution.source.event time with
  | .atomic occurrence => (execution.readSource occurrence.id).getD 0
  | _ => 0

/-- At an atomic transition, `observedWrite` is its actual global RF source. -/
theorem readSource_eq_observedWrite_of_atomic
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (time : Nat)
    (occurrence : AtomicOccurrence Value)
    (event : execution.source.event time = .atomic occurrence)
    (read : occurrence.toRC11Atom.IsRead) :
    execution.readSource occurrence.id =
      some (execution.observedWrite time) := by
  obtain ⟨sourceId, source⟩ :=
    execution.readSource_exists_of_atomic time occurrence event read
  simp [observedWrite, event, source]

/-- Atomic reads with the same global RF source observe the same pointer. -/
theorem readValue_eq_of_same_readSource
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (firstTime secondTime : Nat)
    (first second : AtomicOccurrence Value)
    (firstEvent : execution.source.event firstTime = .atomic first)
    (secondEvent : execution.source.event secondTime = .atomic second)
    (firstRead : first.toRC11Atom.IsRead)
    (secondRead : second.toRC11Atom.IsRead)
    (sourceId : EventId)
    (firstSource : execution.readSource first.id = some sourceId)
    (secondSource : execution.readSource second.id = some sourceId) :
    first.toRC11Atom.readValue = second.toRC11Atom.readValue := by
  let length := max firstTime secondTime + 1
  let finiteExecution := execution.supportedPrefix length
  have firstMember : first.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms_of_lt
      firstTime length (by omega) first firstEvent
  have secondMember : second.toRC11Atom ∈ finiteExecution.candidate.atoms :=
    execution.occurrence_mem_supportedPrefix_atoms_of_lt
      secondTime length (by omega) second secondEvent
  obtain ⟨firstReadValue, firstReadValueEq⟩ :
      ∃ value, first.toRC11Atom.readValue = some value := by
    exact readValue_exists_of_isRead first.toRC11Atom firstRead
  obtain ⟨secondReadValue, secondReadValueEq⟩ :
      ∃ value, second.toRC11Atom.readValue = some value := by
    exact readValue_exists_of_isRead second.toRC11Atom secondRead
  have firstSpec :=
    finiteExecution.valid.sourceSpec first.toRC11Atom firstMember
  rw [firstReadValueEq] at firstSpec
  obtain ⟨firstWriter, firstWriterMember, firstLocation,
      firstValue, firstChosen⟩ := firstSpec
  have secondSpec :=
    finiteExecution.valid.sourceSpec second.toRC11Atom secondMember
  rw [secondReadValueEq] at secondSpec
  obtain ⟨secondWriter, secondWriterMember, secondLocation,
      secondValue, secondChosen⟩ := secondSpec
  have firstWriterId : firstWriter.id = sourceId := by
    have restrictionRaw :=
      execution.prefixReadSource length first.toRC11Atom firstMember
    have restriction :
        finiteExecution.candidate.sourceId first.toRC11Atom.id =
          execution.readSource first.toRC11Atom.id := by
      exact restrictionRaw
    have selected : some firstWriter.id = some sourceId := by
      rw [← firstChosen]
      exact restriction.trans firstSource
    exact Option.some.inj selected
  have secondWriterId : secondWriter.id = sourceId := by
    have restrictionRaw :=
      execution.prefixReadSource length second.toRC11Atom secondMember
    have restriction :
        finiteExecution.candidate.sourceId second.toRC11Atom.id =
          execution.readSource second.toRC11Atom.id := by
      exact restrictionRaw
    have selected : some secondWriter.id = some sourceId := by
      rw [← secondChosen]
      exact restriction.trans secondSource
    exact Option.some.inj selected
  have sameWriter : firstWriter = secondWriter :=
    finiteExecution.valid.atom_eq_of_id_eq
      firstWriterMember secondWriterMember
      (firstWriterId.trans secondWriterId.symm)
  subst secondWriter
  rw [firstReadValueEq, secondReadValueEq]
  exact congrArg some (Option.some.inj (firstValue.symm.trans secondValue))

/-!
Prefix-finite selected-site `fr` eventually exposes a fixed stable write to
the chosen atomic attempts.  Queue-specific code only has to show that every
alternative RF source is modification-order earlier than `stableWrite`.
-/
theorem eventually_observes_stable_write_of_fromReadFair
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (fromReadFair : execution.FromReadFair)
    (site : Site)
    (attempt : Nat → Prop)
    (attemptAtomic :
      ∀ time,
        attempt time →
        ∃ occurrence : AtomicOccurrence Value,
          execution.source.event time = .atomic occurrence ∧
            occurrence.toRC11Atom.IsRead)
    (stablePosition : Nat)
    (stableWrite : EventId)
    (stableAt : execution.graphEventId? stablePosition = some stableWrite)
    (readDifferent :
      ∀ time, attempt time → time + 3 ≠ stablePosition)
    (staleBeforeStable :
      ∀ time,
        attempt time →
        execution.observedWrite time ≠ stableWrite →
        execution.modificationOrder site
          (execution.observedWrite time) stableWrite) :
    Liveness.EventuallyAlways (fun time =>
      attempt time → execution.observedWrite time = stableWrite) := by
  refine
    Liveness.eventually_observes_stable_write_at
      (fromRead := execution.FromReadAt site)
      (fromReadFair site)
      attempt
      (fun time => time + 3)
      ?_
      execution.observedWrite
      stableWrite
      stablePosition
      ?_
  · intro bound
    refine ⟨bound, ?_⟩
    intro time afterBound _
    exact Nat.le_trans afterBound (Nat.le_add_right time 3)
  · intro time isAttempt stale
    obtain ⟨occurrence, event, read⟩ := attemptAtomic time isAttempt
    refine
      ⟨occurrence.id,
        execution.observedWrite time,
        stableWrite,
        execution.graphEventId?_atomic time occurrence event,
        stableAt,
        execution.readSource_eq_observedWrite_of_atomic
          time occurrence event read,
        staleBeforeStable time isAttempt stale,
        readDifferent time isAttempt⟩

/-- Conventional per-site memory fairness implies selected-write visibility. -/
theorem eventually_observes_stable_write
    (execution : InfiniteRC11Execution Value threadCount dummy)
    (memoryFair : execution.MemoryFair)
    (site : Site)
    (attempt : Nat → Prop)
    (attemptAtomic :
      ∀ time,
        attempt time →
        ∃ occurrence : AtomicOccurrence Value,
          execution.source.event time = .atomic occurrence ∧
            occurrence.toRC11Atom.IsRead)
    (stablePosition : Nat)
    (stableWrite : EventId)
    (stableAt : execution.graphEventId? stablePosition = some stableWrite)
    (readDifferent :
      ∀ time, attempt time → time + 3 ≠ stablePosition)
    (staleBeforeStable :
      ∀ time,
        attempt time →
        execution.observedWrite time ≠ stableWrite →
        execution.modificationOrder site
          (execution.observedWrite time) stableWrite) :
    Liveness.EventuallyAlways (fun time =>
      attempt time → execution.observedWrite time = stableWrite) :=
  execution.eventually_observes_stable_write_of_fromReadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    site attempt attemptAtomic stablePosition stableWrite stableAt
    readDifferent staleBeforeStable

end InfiniteRC11Execution

end WeakMemory.MSQueue.Source
