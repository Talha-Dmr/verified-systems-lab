import WeakMemory.TreiberVerifiedModel

namespace WeakMemory.TreiberRC11

/-!
# Proof-relevant provenance for accepted raw Treiber executions

`RawTreiberModelExecution.validate?` deliberately returns the compact
certificate used by the downstream safety and linearizability theorems.  This
module records the successful intermediate validator results as a separate,
proof-relevant package.  In particular, it connects every retained model
component back to the corresponding field of the exact raw input.
-/

/--
The successful intermediate results used to construct one validated model
execution.

The data witness `certifiedLabels` is retained, rather than merely asserting
that some ownership certification exists.  The remaining fields state the
exact optional computations and their strongest convenient consequences.
-/
structure RawValidationProvenance
    (raw : RawTreiberModelExecution α)
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) where
  certifiedLabels :
    List (EventGraph.OwnedLabel α)
  sourceValidation :
    InterleavingCheck.validateRaw?
        (ModelInitial.initialized : TreiberRA.State α)
        raw.sourceLabels =
      some execution.model.source
  labelsCertified :
    InterleavingCheck.certifyLabels? raw.sourceLabels =
      some certifiedLabels
  labelsErased :
    certifiedLabels.map
        InterleavingCheck.RawOwnedLabel.ofOwned =
      raw.sourceLabels
  sourceSkeleton :
    execution.model.source.skeleton =
      ({ labels := certifiedLabels } :
        EventGraph.Skeleton α)
  relationValidation :
    RelationDataCheck.check?
        execution.model.source.skeleton
        raw.relationData =
      some execution.model.relations
  relationChecked :
    RelationDataCheck.validate
        execution.model.source.skeleton
        raw.relationData = true
  writeTail :
    execution.model.relations.writeTail =
      raw.relationData.writeTail
  sourceId :
    execution.model.relations.sourceId =
      RelationDataCheck.sourceFor
        raw.relationData.readSources
  scheduleResolution :
    EventScheduleInput.resolve?
        execution.model.source.skeleton.events
        raw.relationSchedule =
      some execution.model.relationSchedule
  scheduleIds :
    execution.model.relationSchedule.map Event.id =
      raw.relationSchedule
  generatedAllocator :
    GeneratedEventsCheck.generate?
        execution.model.relations
        (ModelInitial.initialized : TreiberRA.State α)
        raw.popPublications =
      some execution.model.allocator
  nextReadsChecked :
    NextReadCheck.check
        execution.model.toSourceAtomicExecution = true
  clientOrderChecked :
    ClientCompatibilityCheck.crossThreadRealTimeCompatible
        execution.model.toSourceAtomicExecution
        execution.model.relationSchedule = true

namespace RawTreiberModelExecution

/--
Acceptance of the top-level validator reconstructs the exact proof-relevant
provenance of all raw fields retained in the validated model.
-/
noncomputable def validate?_provenance
    [DecidableEq α]
    {raw : RawTreiberModelExecution α}
    {execution : ValidatedTreiberModelExecution α}
    (accepted : raw.validate? = some execution) :
    RawValidationProvenance raw execution := by
  unfold validate? at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · split at accepted
        · contradiction
        · split at accepted
          · split at accepted
            · split at accepted
              · rename_i sourceResult source sourceShape
                  relationResult relations relationShape
                  scheduleResult schedule scheduleShape
                  allocator generatedShape scheduleChecked
                  nextReadsChecked clientOrderChecked
                cases Option.some.inj accepted
                have sourceDescription :=
                  InterleavingCheck.validateRaw?_sound
                    sourceShape
                let certifiedLabels :=
                  Classical.choose sourceDescription
                have certificationDescription :=
                  Classical.choose_spec sourceDescription
                have relationDescription :=
                  RelationDataCheck.check?_sound
                    source.skeleton raw.relationData
                    relationShape
                have scheduleDescription :=
                  EventScheduleInput.resolve?_sound
                    scheduleShape
                exact {
                  certifiedLabels :=
                    certifiedLabels
                  sourceValidation :=
                    sourceShape
                  labelsCertified :=
                    certificationDescription.1
                  labelsErased :=
                    certificationDescription.2.1
                  sourceSkeleton :=
                    certificationDescription.2.2
                  relationValidation :=
                    relationShape
                  relationChecked :=
                    relationDescription.1
                  writeTail :=
                    relationDescription.2.1
                  sourceId :=
                    relationDescription.2.2.1
                  scheduleResolution :=
                    scheduleShape
                  scheduleIds :=
                    scheduleDescription.1
                  generatedAllocator :=
                    generatedShape
                  nextReadsChecked :=
                    nextReadsChecked
                  clientOrderChecked :=
                    clientOrderChecked
                }
              · contradiction
            · contradiction
          · contradiction

end RawTreiberModelExecution

end WeakMemory.TreiberRC11
