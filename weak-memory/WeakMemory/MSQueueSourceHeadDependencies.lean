import WeakMemory.MSQueueSourceHeadProvenance
import WeakMemory.MSQueueSourcePredecessors

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Head-CAS structural dependencies

The source-control theorem identifies the exact `head.next` read used by a
successful Head CAS.  RC11 reads-from then identifies the unique link that
installed the desired node, and `PO`/`ECO` place that link before the CAS in
every admitted atom schedule.
-/

namespace AtomSchedule

/-- A successful Head CAS can only advance across an already scheduled link
edge carrying the same `expected` and `desired` nodes. -/
theorem dequeueHeadCAS_linkDependency
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {thread casId operation expected desired : Nat}
    {dequeued : Value}
    (member :
      TraceEvent.atomic
        ⟨casId, .dequeueHeadCAS thread operation expected desired dequeued
          (.node expected) true⟩ ∈ trace) :
    ∃ link value,
      link ∈ structuralRecords trace ∧
        link.action = .link expected desired value ∧
        MultiLocationRC11.IdBefore link.point casId schedule.ids := by
  obtain ⟨headLoadId, tailLoadId, nextLoadId, validationId, tail,
      different, headTailPO, tailNextPO, nextValidationPO,
      validationCasPO⟩ :=
    execution.dequeueHeadSuccess_programOrder member
  let nextOccurrence : AtomicOccurrence Value :=
    ⟨nextLoadId,
      .dequeueNextLoad thread operation expected (.node desired)⟩
  have nextMember :
      nextOccurrence.toRC11Atom ∈ execution.candidate.atoms := by
    exact nextValidationPO.closed.1
  obtain ⟨source, link, value, readsFrom, linkMember,
      linkShape, linkExact⟩ :=
    nextNodeRead_hasLinkOrigin execution nextMember rfl rfl
  have linkBeforeNext := schedule.readsFrom_before readsFrom
  rw [← linkExact] at linkBeforeNext
  have nextBeforeValidation :=
    schedule.respectsProgramOrder nextValidationPO
  have validationBeforeCas :=
    schedule.respectsProgramOrder validationCasPO
  have linkBeforeCas := MultiLocationRC11.IdBefore.transitive
    linkBeforeNext
    (MultiLocationRC11.IdBefore.transitive
      nextBeforeValidation validationBeforeCas)
  exact ⟨link, value, linkMember, linkShape, by
    simpa [nextOccurrence, AtomicOccurrence.toRC11Atom] using
      linkBeforeCas⟩

/-- The retroactive empty point reads directly from `head.next`'s initializer;
there is no previously scheduled link at that site. -/
theorem dequeueEmpty_nullInitializer
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {thread validationId operation head point : Nat}
    (member :
      TraceEvent.atomic
        ⟨validationId,
          .dequeueHeadValidateEmpty thread operation head point⟩ ∈ trace) :
    ∃ source,
      LatestSource schedule source
          (⟨point,
            .dequeueNextLoad thread operation head .null⟩ :
              AtomicOccurrence Value).toRC11Atom ∧
        execution.candidate.InitializerAt (.next head) source := by
  let pointOccurrence : AtomicOccurrence Value :=
    ⟨point, .dequeueNextLoad thread operation head .null⟩
  have pointEventMember : TraceEvent.atomic pointOccurrence ∈ trace :=
    (execution.sourceWellFormed.emptyAnchor member).1
  have pointOccurrenceMember :
      pointOccurrence ∈ atomicOccurrences trace :=
    List.mem_filterMap.mpr
      ⟨.atomic pointOccurrence, pointEventMember, rfl⟩
  have pointMember :
      pointOccurrence.toRC11Atom ∈ execution.candidate.atoms :=
    execution.atomicAtom_mem pointOccurrenceMember
  obtain ⟨source, readsFrom, initializer⟩ :=
    nextNullRead_hasInitializerSource execution pointMember rfl rfl
  exact ⟨source, schedule.latestSource_of_readsFrom readsFrom,
    initializer⟩

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
