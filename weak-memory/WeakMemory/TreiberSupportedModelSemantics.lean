import WeakMemory.TreiberVerifiedModel

namespace WeakMemory.TreiberRC11

/-!
# Completeness of the checked, proof-carrying model

This module supplies the model-to-validator direction for the normalized
finite semantics.  Its input already carries source generation, relation
scheduling, immutable-field, and client-order proofs.  Canonical relation data
and generated publication-path completeness let that input be serialized and
accepted again by the executable validator.

This is intentionally not a C semantics and not a source-to-model theorem.
It is a non-circular completeness bridge between the proof-carrying Lean model
and its finite raw validator representation.
-/

/--
A normalized execution in the exact initialized-state model consumed by the
top-level validator.

Canonicality removes arbitrary `sourceId` values outside the finite event
carrier, making relation serialization an exact round trip.
-/
structure NormalizedSupportedModelExecution
    (α : Type)
    [DecidableEq α] where
  model :
    ScheduledRelationModelExecution
      (ModelInitial.initialized : TreiberRA.State α)
  relationsCanonical :
    RelationDataCheck.Canonical model.relations
  nextReadValues :
    NextReadValueCertificate model.toSourceAtomicExecution
  crossThreadRealTime :
    CrossThreadRealTimeCompatible
      model.toSourceAtomicExecution
      model.relationSchedule

namespace NormalizedSupportedModelExecution

/--
Choose the complete finite publication input reconstructed from the logical
event-generation proof.
-/
noncomputable def publications
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    List GeneratedEventsCheck.RawPublication :=
  Classical.choose
    (GeneratedEventsCheck.generate?_complete
      execution.model.relations
      (ModelInitial.initialized : TreiberRA.State α)
      execution.model.generated)

/-- The chosen publication list names exactly the successful-pop events. -/
theorem publicationIds
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    execution.publications.map
        GeneratedEventsCheck.RawPublication.popEventId =
      GeneratedEventsCheck.successfulPopEventIds
        execution.model.source.skeleton.events :=
  (Classical.choose_spec
    (GeneratedEventsCheck.generate?_complete
      execution.model.relations
      (ModelInitial.initialized : TreiberRA.State α)
      execution.model.generated)).1

/-- The chosen publication list reconstructs the exact final allocator. -/
theorem publications_roundTrip
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    GeneratedEventsCheck.generate?
        execution.model.relations
        (ModelInitial.initialized : TreiberRA.State α)
        execution.publications =
      some execution.model.allocator :=
  (Classical.choose_spec
    (GeneratedEventsCheck.generate?_complete
      execution.model.relations
      (ModelInitial.initialized : TreiberRA.State α)
      execution.model.generated)).2

/-- Canonical finite serialization of every untrusted validator input field. -/
noncomputable def toRaw
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    RawTreiberModelExecution α where
  sourceLabels :=
    InterleavingCheck.rawLabels execution.model.source
  relationData :=
    RelationDataCheck.serialize execution.model.relations
  relationSchedule :=
    execution.model.relationSchedule.map Event.id
  popPublications :=
    execution.publications

/-- Source-label erasure and ownership checking return the exact source. -/
theorem source_roundTrip
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    InterleavingCheck.validateRaw?
        (ModelInitial.initialized : TreiberRA.State α)
        execution.toRaw.sourceLabels =
      some execution.model.source := by
  simpa [toRaw] using
    InterleavingCheck.validateRaw?_complete
      execution.model.source

/-- Canonical relation serialization returns the exact dependent certificate. -/
theorem relations_roundTrip
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    RelationDataCheck.check?
        execution.model.source.skeleton
        execution.toRaw.relationData =
      some execution.model.relations := by
  simpa [toRaw] using
    RelationDataCheck.check?_serialize_eq_some
      execution.model.relations
      execution.relationsCanonical

/-- Resolving serialized event identifiers returns the exact model schedule. -/
theorem schedule_roundTrip
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    EventScheduleInput.resolve?
        execution.model.source.skeleton.events
        execution.toRaw.relationSchedule =
      some execution.model.relationSchedule := by
  apply EventScheduleInput.resolve?_complete
  intro event member
  exact
    (execution.model.scheduleRespectsGraph.covers event).mpr
      member

/-- The serialized raw publication component returns the exact allocator. -/
theorem allocator_roundTrip
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    GeneratedEventsCheck.generate?
        execution.model.relations
        (ModelInitial.initialized : TreiberRA.State α)
        execution.toRaw.popPublications =
      some execution.model.allocator := by
  simpa [toRaw] using execution.publications_roundTrip

/-- The existing graph-respecting schedule passes the finite relation check. -/
theorem relationScheduleChecked
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    RelationScheduleCheck.check
        execution.model.relations
        execution.model.relationSchedule = true :=
  (RelationScheduleCheck.check_eq_true_iff
    execution.model.relations
    execution.model.relationSchedule).mpr
      execution.model.scheduleRespectsGraph

/-- The logical immutable-field certificate passes its exact finite check. -/
theorem nextReadsChecked
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    NextReadCheck.check
        execution.model.toSourceAtomicExecution = true :=
  NextReadCheck.check_complete execution.nextReadValues

/-- The logical cross-thread client-order certificate passes its finite check. -/
theorem clientOrderChecked
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution.model.toSourceAtomicExecution
        execution.model.relationSchedule = true :=
  (ClientCompatibilityCheck.crossThreadRealTimeCompatible_eq_true_iff
      execution.model.toSourceAtomicExecution
      execution.model.relationSchedule).mpr
        execution.crossThreadRealTime

/--
Every normalized proof-carrying model serializes to a raw input accepted by
the complete executable validation pipeline.
-/
theorem toRaw_supported
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    execution.toRaw.Supported := by
  have sourceAccepted :=
    execution.source_roundTrip
  have relationsAccepted :=
    execution.relations_roundTrip
  have scheduleAccepted :=
    execution.schedule_roundTrip
  have allocatorAccepted :=
    execution.allocator_roundTrip
  have relationScheduleAccepted :=
    execution.relationScheduleChecked
  have nextReadsAccepted :=
    execution.nextReadsChecked
  have clientOrderAccepted :=
    execution.clientOrderChecked
  unfold RawTreiberModelExecution.Supported
  unfold RawTreiberModelExecution.validate?
  dsimp only
  split
  · simp_all
  · rename_i sourceResult source sourceShape
    have sourceSame :
        source = execution.model.source := by
      simp_all
    subst source
    split
    · simp_all
    · rename_i relationResult relations relationShape
      have relationsSame :
          relations = execution.model.relations := by
        simp_all
      subst relations
      split
      · simp_all
      · rename_i scheduleResult schedule scheduleShape
        have scheduleSame :
            schedule = execution.model.relationSchedule := by
          simp_all
        subst schedule
        split <;> simp_all

/--
The accepted serialization therefore receives the checked model's descriptor,
node-safety, and Herlihy--Wing guarantees from the public top-level theorem.
-/
theorem exists_verified
    [DecidableEq α]
    (execution : NormalizedSupportedModelExecution α) :
    ∃ validated : ValidatedTreiberModelExecution α,
      execution.toRaw.validate? = some validated ∧
        TreiberProgramDescriptor.Extracted.treiberProgram.descriptor =
          TreiberProgramDescriptor.controlFlowDescriptor ∧
        NodeAccessCertificate
          validated.atomic.toControlledCandidate ∧
        HerlihyWing.Linearizable []
          (sourceHistory validated.atomic.source.skeleton) :=
  RawTreiberModelExecution.verified_of_supported
    execution.toRaw execution.toRaw_supported

end NormalizedSupportedModelExecution

end WeakMemory.TreiberRC11
