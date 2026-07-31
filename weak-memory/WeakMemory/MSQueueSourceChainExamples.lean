import WeakMemory.MSQueueSourceRC11Examples
import WeakMemory.MSQueueChainExamples
import WeakMemory.MSQueueSourceSchedule
import WeakMemory.MSQueueRecordScheduling

namespace WeakMemory.MSQueue.Source.RC11Example.ChainBridge

/-!
# One concrete source-to-chain bridge

This file connects only `Example.sequentialEvents` and its already checked
`supportedExecution` to the finite chain replay.  It is intentionally an
example certificate, not a theorem that arbitrary source executions are
linearizable.

The successful link at occurrence 7 is the enqueue point, the successful
Head CAS at occurrence 13 is the value-dequeue point, and the null next load
at occurrence 16 is the retroactive empty-dequeue point.  The successful
Tail swing at occurrence 8 changes the concrete chain cursor but emits no
abstract queue commit.
-/

open Example

abbrev Record := AtomicOccurrence.CommitRecord Nat

def enqueueLinkOccurrence : AtomicOccurrence Nat :=
  ⟨7, .enqueueLinkCAS 0 10 0 1 7 .null true⟩

def tailHelperOccurrence : AtomicOccurrence Nat :=
  ⟨8, .enqueueFinishTailCAS 0 10 0 1 (.node 0) true⟩

def dequeueHeadOccurrence : AtomicOccurrence Nat :=
  ⟨13, .dequeueHeadCAS 2 30 0 1 7 (.node 0) true⟩

def emptyPointOccurrence : AtomicOccurrence Nat :=
  ⟨16, .dequeueNextLoad 1 20 1 .null⟩

def emptyValidationOccurrence : AtomicOccurrence Nat :=
  ⟨17, .dequeueHeadValidateEmpty 1 20 1 16⟩

def enqueueRecord : Record where
  thread := 0
  operation := 10
  point := 7
  validation := 7
  commit := .enqueue 7

def dequeueValueRecord : Record where
  thread := 2
  operation := 30
  point := 13
  validation := 13
  commit := .dequeueValue 7

def dequeueEmptyRecord : Record where
  thread := 1
  operation := 20
  point := 16
  validation := 17
  commit := .dequeueEmpty

/-- Commit records in the RC11 schedule order of this particular witness. -/
def pointOrderedRecords : List Record :=
  [enqueueRecord, dequeueValueRecord, dequeueEmptyRecord]

def pointOrderedCommits : List (Commit Nat) :=
  pointOrderedRecords.map AtomicOccurrence.CommitRecord.commit

def sourceCommit?
    (occurrence : AtomicOccurrence Nat) : Option (Commit Nat) :=
  occurrence.commitRecord?.map AtomicOccurrence.CommitRecord.commit

theorem source_commitRecords_exact :
    sequentialEvents.filterMap TraceEvent.commitRecord? =
      pointOrderedRecords := by
  rfl

theorem pointOrdered_points :
    pointOrderedRecords.map AtomicOccurrence.CommitRecord.point =
      [7, 13, 16] := by
  rfl

/-- Raw carrier order agrees here; the reusable certificate does not assume it. -/
theorem carrier_points_increasing_for_this_example :
    pointOrderedRecords.Pairwise
      (CommitPointBefore sequentialEvents) := by
  simp [pointOrderedRecords, CommitPointBefore, enqueueRecord,
    dequeueValueRecord, dequeueEmptyRecord, atomicIds,
    atomicOccurrences, TraceEvent.atomicOccurrence?, sequentialEvents,
    enqueueEvents, valueDequeueEvents, emptyDequeueEvents,
    MultiLocationRC11.IdBefore, List.idxOf_cons]

theorem pointOrdered_commits :
    pointOrderedCommits =
      [.enqueue 7, .dequeueValue 7, .dequeueEmpty] := by
  rfl

theorem enqueueLink_record :
    enqueueLinkOccurrence.commitRecord? = some enqueueRecord := by
  rfl

theorem dequeueHead_record :
    dequeueHeadOccurrence.commitRecord? = some dequeueValueRecord := by
  rfl

/-- The validating occurrence emits an empty record anchored at occurrence 16. -/
theorem emptyValidation_record :
    emptyValidationOccurrence.commitRecord? = some dequeueEmptyRecord := by
  rfl

/-- The anchor itself is a load and therefore emits no record. -/
theorem emptyPoint_doesNotEmit :
    emptyPointOccurrence.commitRecord? = none := by
  rfl

/-- The Tail helper is represented by a concrete structural stutter. -/
theorem tailHelper_doesNotEmit :
    tailHelperOccurrence.commitRecord? = none := by
  rfl

theorem bridgeOccurrences_present :
    [TraceEvent.atomic enqueueLinkOccurrence,
     TraceEvent.atomic tailHelperOccurrence,
     TraceEvent.atomic dequeueHeadOccurrence,
     TraceEvent.atomic emptyPointOccurrence,
     TraceEvent.atomic emptyValidationOccurrence].all
        (fun event => event ∈ sequentialEvents) := by
  native_decide

theorem bridgeAtoms_present :
    [enqueueLinkOccurrence.toRC11Atom,
     tailHelperOccurrence.toRC11Atom,
     dequeueHeadOccurrence.toRC11Atom,
     emptyPointOccurrence.toRC11Atom,
     emptyValidationOccurrence.toRC11Atom].all
        (fun atom => atom ∈ supportedExecution.candidate.atoms) := by
  native_decide

def chainInitial : Chain.State Nat :=
  Chain.State.initial 0

def chainLinked : Chain.State Nat := {
  chainInitial with
  nodes := chainInitial.nodes ++ [1]
  payloads := chainInitial.payloads ++ [7]
}

def chainTailAdvanced : Chain.State Nat := {
  chainLinked with tail := chainLinked.tail + 1
}

def chainHeadAdvanced : Chain.State Nat := {
  chainTailAdvanced with head := chainTailAdvanced.head + 1
}

theorem enqueueLink_chainStep :
    Chain.Step chainInitial
      (sourceCommit? enqueueLinkOccurrence) chainLinked := by
  simpa [sourceCommit?, enqueueLinkOccurrence, chainLinked,
    chainInitial, AtomicOccurrence.commitRecord?] using
    (Chain.Step.link chainInitial 1 7 (by decide) (by decide))

theorem tailHelper_chainStep :
    Chain.Step chainLinked
      (sourceCommit? tailHelperOccurrence) chainTailAdvanced := by
  simpa [sourceCommit?, tailHelperOccurrence, chainTailAdvanced,
    AtomicOccurrence.commitRecord?] using
    (Chain.Step.advanceTail chainLinked (by decide))

theorem dequeueHead_chainStep :
    Chain.Step chainTailAdvanced
      (sourceCommit? dequeueHeadOccurrence) chainHeadAdvanced := by
  simpa [sourceCommit?, dequeueHeadOccurrence, chainHeadAdvanced,
    AtomicOccurrence.commitRecord?] using
    (Chain.Step.advanceHead chainTailAdvanced 7
      (by decide) (by decide))

theorem dequeueEmpty_chainStep :
    Chain.Step chainHeadAdvanced
      (sourceCommit? emptyValidationOccurrence) chainHeadAdvanced := by
  simpa [sourceCommit?, emptyValidationOccurrence,
    AtomicOccurrence.commitRecord?] using
    (Chain.Step.empty chainHeadAdvanced (by decide))

/-!
The reusable certificate below is exact in both directions.  Its RC11 atom
schedule covers the whole candidate and respects `PO` and `ECO`; structural
records are then placed definitionally at their anchor atoms.  The successful
Tail swing remains in that record schedule even though it emits no commit.
-/

def enqueueStructuralRecord : Structural.Record Nat := {
  occurrence := enqueueLinkOccurrence
  point := 7
  validation := 7
  action := .link 0 1 7
}

def tailStructuralRecord : Structural.Record Nat := {
  occurrence := tailHelperOccurrence
  point := 8
  validation := 8
  action := .advanceTail 0 1
}

def dequeueStructuralRecord : Structural.Record Nat := {
  occurrence := dequeueHeadOccurrence
  point := 13
  validation := 13
  action := .advanceHead 0 1 7
}

def emptyStructuralRecord : Structural.Record Nat := {
  occurrence := emptyValidationOccurrence
  point := 16
  validation := 17
  action := .empty 1
}

def structuralSchedule : List (Structural.Record Nat) :=
  [enqueueStructuralRecord, tailStructuralRecord,
    dequeueStructuralRecord, emptyStructuralRecord]

theorem structuralRecords_exact :
    Structural.structuralRecords sequentialEvents =
      structuralSchedule := by
  rfl

theorem structuralRecord_points_nodup :
    ((Structural.structuralRecords sequentialEvents).map
      Structural.Record.point).Nodup := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem candidate_id_lt_before
    {source target : MultiLocationRC11.Atom Site Ptr}
    (sourceMember : source ∈ candidate.atoms)
    (targetMember : target ∈ candidate.atoms)
    (increases : source.id < target.id) :
    MultiLocationRC11.IdBefore source.id target.id
      candidate.atomIds := by
  simp only [candidate_atoms_explicit, List.mem_cons,
    List.not_mem_nil, or_false] at sourceMember targetMember
  rcases sourceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases targetMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [candidate, projectCandidate, projectedAtoms,
    staticAtoms, atomicOccurrences, sequentialEvents, enqueueEvents,
    valueDequeueEvents, emptyDequeueEvents, headInitializer,
    tailInitializer, dummyNextInitializer, dynamicNextInitializer,
    enqueueTailRead, enqueueNextRead, enqueueTailValidation,
    enqueueLink, enqueueTailSwing, dequeueHeadRead, dequeueTailRead,
    dequeueNextRead, dequeueHeadValidation, dequeueHeadSwing,
    emptyHeadRead, emptyTailRead, emptyNextRead,
    emptyHeadValidation, TraceEvent.atomicOccurrence?,
    AtomicOccurrence.toRC11Atom, AtomicAction.thread,
    AtomicAction.site, AtomicAction.access, AtomicAction.order,
    MultiLocationRC11.Candidate.atomIds, MultiLocationRC11.IdBefore,
    List.idxOf_cons]

theorem supportedExecution_atomOrderAcyclic :
    Structural.AtomOrderAcyclic supportedExecution.candidate :=
  Structural.atomOrderAcyclic_of_orderWitness orderWitness

theorem generatedAtomSchedule_exists :
    Nonempty (Structural.AtomSchedule supportedExecution) :=
  Structural.AtomSchedule.exists_of_orderWitness supportedExecution
    orderWitness

def atomSchedule : Structural.AtomSchedule supportedExecution where
  atoms := candidate.atoms
  permutation := List.Perm.refl _
  respectsProgramOrder := by
    intro source target edge
    exact candidate_id_lt_before edge.1 edge.2.1 (po_id_lt edge)
  respectsExtendedCoherence := by
    intro source target edge
    exact candidate_id_lt_before
      (Structural.extendedCoherence_closed edge).1
      (Structural.extendedCoherence_closed edge).2
      (orderWitness.extendedCoherenceIncreases edge)

theorem recordsOn_atomSchedule :
    Structural.recordsOn sequentialEvents atomSchedule.atoms =
      structuralSchedule := by
  rfl

theorem enqueueStructural_applies :
    enqueueStructuralRecord.Applies chainInitial chainLinked := by
  simp [Structural.Record.Applies, enqueueStructuralRecord,
    chainInitial, chainLinked, Chain.State.initial]

theorem tailStructural_applies :
    tailStructuralRecord.Applies chainLinked chainTailAdvanced := by
  simp [Structural.Record.Applies, tailStructuralRecord,
    chainInitial, chainLinked, chainTailAdvanced, Chain.State.initial]

theorem dequeueStructural_applies :
    dequeueStructuralRecord.Applies chainTailAdvanced chainHeadAdvanced := by
  simp [Structural.Record.Applies, dequeueStructuralRecord,
    chainInitial, chainLinked, chainTailAdvanced, chainHeadAdvanced,
    Chain.State.initial]

theorem emptyStructural_applies :
    emptyStructuralRecord.Applies chainHeadAdvanced chainHeadAdvanced := by
  simp [Structural.Record.Applies, emptyStructuralRecord,
    chainInitial, chainLinked, chainTailAdvanced, chainHeadAdvanced,
    Chain.State.initial]

theorem structuralReplay :
    Structural.Replay chainInitial structuralSchedule chainHeadAdvanced :=
  Structural.Replay.cons enqueueStructural_applies <|
  Structural.Replay.cons tailStructural_applies <|
  Structural.Replay.cons dequeueStructural_applies <|
  Structural.Replay.cons emptyStructural_applies <|
  Structural.Replay.nil chainHeadAdvanced

def certificate : Structural.Certificate supportedExecution :=
  Structural.Certificate.ofReplay supportedExecution atomSchedule
    chainHeadAdvanced (by
      simpa [chainInitial, recordsOn_atomSchedule] using structuralReplay)

theorem certificate_commits :
    certificate.commits = pointOrderedCommits := by
  rfl

/-- Replay extracted by the reusable exact structural certificate. -/
theorem certificate_replay :
    Chain.Replay chainInitial pointOrderedCommits chainHeadAdvanced := by
  rw [← certificate_commits]
  change Chain.Replay (Chain.State.initial 0)
    certificate.commits certificate.finalState
  exact certificate.chainReplay

/-- FIFO legality for this one supported source/RC11 execution. -/
theorem supportedExecution_fifoLegal :
    QueueSpec.Legal []
      (completedHistory pointOrderedCommits) [] := by
  rw [← certificate_commits]
  change QueueSpec.Legal [] (completedHistory certificate.commits)
    certificate.finalState.contents
  exact certificate.fifoLegal

end WeakMemory.MSQueue.Source.RC11Example.ChainBridge
