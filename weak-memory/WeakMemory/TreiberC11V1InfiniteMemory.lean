import WeakMemory.MemoryFairVisibility
import WeakMemory.TreiberC11V1InfiniteRC11
import WeakMemory.TreiberC11V1LivenessControl

namespace WeakMemory.TreiberC11V1

/-!
# Position-indexed infinite RC11 memory relations

The finite RC11 layer numbers only atomic occurrences, whereas an infinite
source execution also contains invocations, field accesses, and responses.
This module lifts the coherent global identifier relations to natural source
positions.  Position zero represents the initializer; transition `time` has
position `time + 1`.

Using positions makes prefix-finite memory fairness directly compatible with
the generic temporal theory without pretending that an atomic identifier is a
global transition number.
-/

namespace RC11.Valid

/-- Valid candidate identifiers identify at most one carrier atom. -/
theorem atom_eq_of_id_eq
    {candidate : RC11.Candidate α}
    (valid : RC11.Valid candidate)
    {first second : RC11.Atom α}
    (firstMember : first ∈ candidate.atoms)
    (secondMember : second ∈ candidate.atoms)
    (sameId : first.id = second.id) :
    first = second := by
  have identifiersNodup :
      (candidate.atoms.map RC11.Atom.id).Nodup := by
    simpa [RC11.Candidate.atomIds] using
      valid.atomIdsNodup
  generalize candidate.atoms = atoms at firstMember secondMember identifiersNodup
  induction atoms with
  | nil =>
      simp at firstMember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at identifiersNodup
      obtain ⟨headFresh, tailNodup⟩ :=
        identifiersNodup
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with firstIsHead | firstInTail
      · subst first
        rcases secondMember with secondIsHead | secondInTail
        · exact secondIsHead.symm
        · exact False.elim
            (headFresh
              (List.mem_map.mpr
                ⟨second, secondInTail, sameId.symm⟩))
      · rcases secondMember with secondIsHead | secondInTail
        · subst second
          exact False.elim
            (headFresh
              (List.mem_map.mpr
                ⟨first, firstInTail, sameId⟩))
        · exact inductionHypothesis
            firstInTail secondInTail tailNodup

end RC11.Valid

namespace InfiniteRC11Execution

/-- RC11 event identifier represented by one position in the source run. -/
def graphEventId?
    (execution : InfiniteRC11Execution α threadCount) :
    Nat → Option EventId
  | 0 =>
      some 0
  | time + 1 =>
      match execution.source.event time with
      | .atomic occurrence =>
          some occurrence.id
      | _ =>
          none

/-- Global reads-from lifted from event identifiers to source positions. -/
def ReadsFromAt
    (execution : InfiniteRC11Execution α threadCount)
    (source target : Nat) : Prop :=
  ∃ sourceId targetId,
    execution.graphEventId? source = some sourceId ∧
      execution.graphEventId? target = some targetId ∧
      execution.readSource targetId = some sourceId

/-- Global modification order lifted to source positions. -/
def ModificationOrderAt
    (execution : InfiniteRC11Execution α threadCount)
    (first second : Nat) : Prop :=
  ∃ firstId secondId,
    execution.graphEventId? first = some firstId ∧
      execution.graphEventId? second = some secondId ∧
      execution.modificationOrder firstId secondId

/-- Position-indexed from-read (`rf⁻¹ ; mo`). -/
def FromReadAt
    (execution : InfiniteRC11Execution α threadCount)
    (read laterWrite : Nat) : Prop :=
  ∃ readId sourceId writeId,
    execution.graphEventId? read = some readId ∧
      execution.graphEventId? laterWrite = some writeId ∧
      execution.readSource readId = some sourceId ∧
      execution.modificationOrder sourceId writeId ∧
      read ≠ laterWrite

/-- The coherent infinite source run with its position-indexed `mo` and `fr`. -/
def executionGraph
    (execution : InfiniteRC11Execution α threadCount) :
    Liveness.InfiniteExecutionGraph
      (GlobalStep (α := α)) where
  toInfiniteRun :=
    execution.source.toInfiniteRun
  modificationOrder :=
    execution.ModificationOrderAt
  fromRead :=
    execution.FromReadAt

/-- Prefix-finite `mo` and `fr` for the coherent infinite RC11 execution. -/
def MemoryFair
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  Liveness.MemoryFair execution.executionGraph

/--
The exact visibility assumption consumed by the Treiber stable-tail proof.

Full declarative memory fairness also requires prefix-finite modification
order.  The response-progress proof below needs only prefix-finite `fr`;
keeping this predicate separate makes that dependency explicit.
-/
def FromReadFair
    (execution : InfiniteRC11Execution α threadCount) : Prop :=
  Liveness.PrefixFinite execution.FromReadAt

/-- Full memory fairness supplies the `fr`-only visibility assumption. -/
theorem fromReadFair_of_memoryFair
    (execution : InfiniteRC11Execution α threadCount)
    (memoryFair : execution.MemoryFair) :
    execution.FromReadFair :=
  memoryFair.2

@[simp] theorem graphEventId?_initializer
    (execution : InfiniteRC11Execution α threadCount) :
    execution.graphEventId? 0 = some 0 :=
  rfl

@[simp] theorem graphEventId?_atomic
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    execution.graphEventId? (time + 1) =
      some occurrence.id := by
  simp [graphEventId?, event]

/-- One dynamic atomic event belongs to the declarative prefix ending after it. -/
theorem occurrence_mem_declarativePrefix_atoms
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    RC11.Atom.occurrence occurrence ∈
      (execution.declarativePrefix (time + 1)).candidate.atoms := by
  change
    RC11.Atom.occurrence occurrence ∈
      RC11.Atom.initial ::
        ((execution.declarativePrefix (time + 1)).candidate.trace
          |>.filterMap RC11.atomOfTraceEvent?)
  rw [execution.declarativePrefix_trace]
  rw [execution.source.tracePrefix_succ]
  simp [event, RC11.atomOfTraceEvent?]

/-- Every earlier atomic event belongs to every sufficiently long prefix. -/
theorem occurrence_mem_declarativePrefix_atoms_of_lt
    (execution : InfiniteRC11Execution α threadCount)
    (time length : Nat)
    (beforeEnd : time < length)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    RC11.Atom.occurrence occurrence ∈
      (execution.declarativePrefix length).candidate.atoms := by
  change
    RC11.Atom.occurrence occurrence ∈
      RC11.Atom.initial ::
        ((execution.declarativePrefix length).candidate.trace
          |>.filterMap RC11.atomOfTraceEvent?)
  rw [execution.declarativePrefix_trace]
  unfold InfiniteExecution.tracePrefix
  simp only [List.mem_cons]
  apply Or.inr
  apply List.mem_filterMap.mpr
  refine
    ⟨TraceEvent.atomic occurrence, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact
      ⟨time, by simp [beforeEnd], event⟩
  · simp [RC11.atomOfTraceEvent?]

/-- Every source atomic occurrence has one global reads-from source. -/
theorem readSource_exists_of_atomic
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    ∃ sourceId,
      execution.readSource occurrence.id =
        some sourceId := by
  let finiteExecution :=
    execution.declarativePrefix (time + 1)
  have member :
      RC11.Atom.occurrence occurrence ∈
        finiteExecution.candidate.atoms :=
    execution.occurrence_mem_declarativePrefix_atoms
      time occurrence event
  obtain ⟨source, sourceMember, sourceValue,
      chosenSource⟩ := by
    simpa [finiteExecution, RC11.Atom.readValue] using
      finiteExecution.rc11.sourceSpec
        (RC11.Atom.occurrence occurrence)
        member
  refine ⟨source.id, ?_⟩
  have globalSource :=
    (execution.declarativePrefix_readSource
      (time + 1)
      (RC11.Atom.occurrence occurrence)
      member).symm.trans chosenSource
  simpa [RC11.Atom.id] using globalSource

/--
The source write observed at one transition.  The default is irrelevant at
non-atomic positions; every atomic source event has a proved source above.
-/
def observedWrite
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat) : EventId :=
  match execution.source.event time with
  | .atomic occurrence =>
      (execution.readSource occurrence.id).getD 0
  | _ =>
      0

/-- At an atomic transition, `observedWrite` is its actual global RF source. -/
theorem readSource_eq_observedWrite_of_atomic
    (execution : InfiniteRC11Execution α threadCount)
    (time : Nat)
    (occurrence : AtomicOccurrence α)
    (event :
      execution.source.event time = .atomic occurrence) :
    execution.readSource occurrence.id =
      some (execution.observedWrite time) := by
  obtain ⟨sourceId, source⟩ :=
    execution.readSource_exists_of_atomic
      time occurrence event
  simp [observedWrite, event, source]

/-- Two atomic reads with the same global RF source observe the same value. -/
theorem readValue_eq_of_same_readSource
    (execution : InfiniteRC11Execution α threadCount)
    (firstTime secondTime : Nat)
    (first second : AtomicOccurrence α)
    (firstEvent :
      execution.source.event firstTime = .atomic first)
    (secondEvent :
      execution.source.event secondTime = .atomic second)
    (sourceId : EventId)
    (firstSource :
      execution.readSource first.id = some sourceId)
    (secondSource :
      execution.readSource second.id = some sourceId) :
    first.action.readValue =
      second.action.readValue := by
  let length := max firstTime secondTime + 1
  let finiteExecution :=
    execution.declarativePrefix length
  have firstMember :
      RC11.Atom.occurrence first ∈
        finiteExecution.candidate.atoms :=
    execution.occurrence_mem_declarativePrefix_atoms_of_lt
      firstTime length (by omega) first firstEvent
  have secondMember :
      RC11.Atom.occurrence second ∈
        finiteExecution.candidate.atoms :=
    execution.occurrence_mem_declarativePrefix_atoms_of_lt
      secondTime length (by omega) second secondEvent
  obtain ⟨firstWriter, firstWriterMember,
      firstValue, firstChosen⟩ := by
    simpa [finiteExecution, RC11.Atom.readValue] using
      finiteExecution.rc11.sourceSpec
        (RC11.Atom.occurrence first)
        firstMember
  obtain ⟨secondWriter, secondWriterMember,
      secondValue, secondChosen⟩ := by
    simpa [finiteExecution, RC11.Atom.readValue] using
      finiteExecution.rc11.sourceSpec
        (RC11.Atom.occurrence second)
        secondMember
  have firstWriterId :
      firstWriter.id = sourceId := by
    have restriction :=
      execution.declarativePrefix_readSource
        length (RC11.Atom.occurrence first)
        firstMember
    have selected :
        some firstWriter.id = some sourceId := by
      rw [← firstChosen, restriction]
      simpa [RC11.Atom.id] using firstSource
    exact Option.some.inj selected
  have secondWriterId :
      secondWriter.id = sourceId := by
    have restriction :=
      execution.declarativePrefix_readSource
        length (RC11.Atom.occurrence second)
        secondMember
    have selected :
        some secondWriter.id = some sourceId := by
      rw [← secondChosen, restriction]
      simpa [RC11.Atom.id] using secondSource
    exact Option.some.inj selected
  have sameWriter :
      firstWriter = secondWriter :=
    finiteExecution.rc11.atom_eq_of_id_eq
      firstWriterMember secondWriterMember
      (firstWriterId.trans secondWriterId.symm)
  subst secondWriter
  exact Option.some.inj
    (firstValue.symm.trans secondValue)

/--
Prefix-finite `fr` eventually exposes a fixed stable write to selected atomic
attempts, provided every other possible source is modification-order earlier
than that stable write.
-/
theorem eventually_observes_stable_write_of_fromReadFair
    (execution : InfiniteRC11Execution α threadCount)
    (fromReadFair : execution.FromReadFair)
    (attempt : Nat → Prop)
    (attemptAtomic :
      ∀ time,
        attempt time →
        ∃ occurrence : AtomicOccurrence α,
          execution.source.event time =
            .atomic occurrence)
    (stablePosition : Nat)
    (stableWrite : EventId)
    (stableAt :
      execution.graphEventId? stablePosition =
        some stableWrite)
    (readDifferent :
      ∀ time,
        attempt time →
        time + 1 ≠ stablePosition)
    (staleBeforeStable :
      ∀ time,
        attempt time →
        execution.observedWrite time ≠ stableWrite →
        execution.modificationOrder
          (execution.observedWrite time)
          stableWrite) :
    Liveness.EventuallyAlways (fun time =>
      attempt time →
        execution.observedWrite time = stableWrite) := by
  refine
    Liveness.eventually_observes_stable_write_at
      (fromRead := execution.FromReadAt)
      fromReadFair
      attempt
      (fun time => time + 1)
      ?_
      execution.observedWrite
      stableWrite
      stablePosition
      ?_
  · intro bound
    refine ⟨bound, ?_⟩
    intro time afterBound _
    exact
      Nat.le_trans afterBound
        (Nat.le_add_right time 1)
  · intro time isAttempt stale
    obtain ⟨occurrence, event⟩ :=
      attemptAtomic time isAttempt
    refine
      ⟨occurrence.id,
        execution.observedWrite time,
        stableWrite,
        ?_, stableAt, ?_, ?_,
        readDifferent time isAttempt⟩
    · exact
        execution.graphEventId?_atomic
          time occurrence event
    · exact
        execution.readSource_eq_observedWrite_of_atomic
          time occurrence event
    · exact staleBeforeStable time isAttempt stale

/--
Standard paired memory fairness implies the exact `fr`-only visibility
theorem.  This compatibility wrapper preserves the conventional interface.
-/
theorem eventually_observes_stable_write
    (execution : InfiniteRC11Execution α threadCount)
    (memoryFair : execution.MemoryFair)
    (attempt : Nat → Prop)
    (attemptAtomic :
      ∀ time,
        attempt time →
        ∃ occurrence : AtomicOccurrence α,
          execution.source.event time =
            .atomic occurrence)
    (stablePosition : Nat)
    (stableWrite : EventId)
    (stableAt :
      execution.graphEventId? stablePosition =
        some stableWrite)
    (readDifferent :
      ∀ time,
        attempt time →
        time + 1 ≠ stablePosition)
    (staleBeforeStable :
      ∀ time,
        attempt time →
        execution.observedWrite time ≠ stableWrite →
        execution.modificationOrder
          (execution.observedWrite time)
          stableWrite) :
    Liveness.EventuallyAlways (fun time =>
      attempt time →
        execution.observedWrite time = stableWrite) :=
  execution.eventually_observes_stable_write_of_fromReadFair
    (execution.fromReadFair_of_memoryFair memoryFair)
    attempt attemptAtomic stablePosition stableWrite stableAt
    readDifferent staleBeforeStable

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
