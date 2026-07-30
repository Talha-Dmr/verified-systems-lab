import WeakMemory.TreiberEventScheduleInput
import WeakMemory.TreiberGeneratedEventsCheck
import WeakMemory.TreiberModelInitial
import WeakMemory.TreiberNextReadCheck
import WeakMemory.TreiberProgramRefinement
import WeakMemory.TreiberRelationDataCheck
import WeakMemory.TreiberRelationScheduleCheck
import WeakMemory.TreiberScheduledModelHistory

namespace WeakMemory.TreiberRC11

/-!
# End-to-end validation of the pinned Treiber model

`RawTreiberModelExecution` contains finite, untrusted execution observations:
source labels, reads-from/modification-order choices, a proposed relation
schedule, and primitive extended-coherence paths for successful pops.

`validate?` checks every layer and returns `ValidatedTreiberModelExecution`
only after constructing the existing Lean certificates.  In particular, the
returned package contains no caller-supplied common rank, `CoreConsistent`,
`OrderAcyclic`, `GraphTyping`, replay, completion, or linearization proof.

The generated descriptor's agreement with the formal control-flow descriptor
is kernel checked.  Source hashes and exact generated artifacts are checked
externally by the trusted Clang AST extractor.  The extractor itself, and the
missing theorem connecting actual C executions to the raw finite inputs below,
remain explicit trust boundaries; this module is not a proved C semantics.
-/

/-- Finite untrusted input to the program-specific model validator. -/
structure RawTreiberModelExecution (α : Type) where
  sourceLabels :
    List (InterleavingCheck.RawOwnedLabel α)
  relationData :
    RelationDataCheck.RawRelationData
  relationSchedule :
    List EventId
  popPublications :
    List GeneratedEventsCheck.RawPublication
  deriving Repr, DecidableEq

/--
A model execution satisfying every certificate required by the executable
validation pipeline.  `validate?` is the public construction path from raw
finite input; the structure's fields state the proof-relevant obligations.

The initial state is fixed to the state immediately after modeled
`treiber_init`: empty published-node heap and null head.
-/
structure ValidatedTreiberModelExecution
    (α : Type)
    [DecidableEq α] where
  model :
    ScheduledRelationModelExecution
      (ModelInitial.initialized : TreiberRA.State α)
  nextReadsChecked :
    NextReadCheck.check model.toSourceAtomicExecution = true
  clientOrderChecked :
    ClientCompatibilityCheck.crossThreadRealTimeCompatible
      model.toSourceAtomicExecution
      model.relationSchedule = true

namespace RawTreiberModelExecution

/--
Validate raw source control, canonical RF/MO data, the finite relation
schedule, generated allocator/event typing, immutable next-field values, and
cross-thread client real time.
-/
def validate?
    [DecidableEq α]
    (raw : RawTreiberModelExecution α) :
    Option (ValidatedTreiberModelExecution α) :=
  let initial :=
    (ModelInitial.initialized : TreiberRA.State α)
  match
      InterleavingCheck.validateRaw?
        initial raw.sourceLabels
  with
  | none =>
      none
  | some source =>
      match
          RelationDataCheck.check?
            source.skeleton raw.relationData
      with
      | none =>
          none
      | some relations =>
          match
              EventScheduleInput.resolve?
                source.skeleton.events
                raw.relationSchedule
          with
          | none =>
              none
          | some schedule =>
              match generatedShape :
                  GeneratedEventsCheck.generate?
                    relations initial raw.popPublications
              with
              | none =>
                  none
              | some allocator =>
                  if scheduleChecked :
                      RelationScheduleCheck.check
                        relations schedule = true
                  then
                    let generated :=
                      GeneratedEventsCheck.generate?_sound
                        relations initial raw.popPublications
                        generatedShape
                    let respects :=
                      RelationScheduleCheck.check_sound
                        scheduleChecked
                    let model :
                        ScheduledRelationModelExecution initial := {
                      source :=
                        source
                      relations :=
                        relations
                      allocator :=
                        allocator
                      initialHeadEmpty :=
                        ModelInitial.initialized_head
                      generated :=
                        generated
                      relationSchedule :=
                        schedule
                      scheduleRespectsGraph :=
                        respects
                    }
                    if nextReadsChecked :
                        NextReadCheck.check
                          model.toSourceAtomicExecution = true
                    then
                      if clientOrderChecked :
                          ClientCompatibilityCheck.crossThreadRealTimeCompatible
                            model.toSourceAtomicExecution
                            model.relationSchedule = true
                      then
                        some {
                          model :=
                            model
                          nextReadsChecked :=
                            nextReadsChecked
                          clientOrderChecked :=
                            clientOrderChecked
                        }
                      else
                        none
                    else
                      none
                  else
                    none

/--
The explicitly supported finite execution semantics: exactly the raw
executions accepted by the program-specific validator.
-/
def Supported
    [DecidableEq α]
    (raw : RawTreiberModelExecution α) : Prop :=
  raw.validate?.isSome = true

end RawTreiberModelExecution

namespace ValidatedTreiberModelExecution

/-- The canonical atomic execution constructed from checked finite data. -/
def atomic
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    SourceAtomicExecution
      (ModelInitial.initialized : TreiberRA.State α) :=
  execution.model.toSourceAtomicExecution

/-- The finite next-read check supplies the publication-value certificate. -/
theorem nextReadValues
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    NextReadValueCertificate execution.atomic :=
  NextReadCheck.check_sound execution.nextReadsChecked

/-- All core RC11 consistency obligations are derived from checked inputs. -/
theorem coreConsistent
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    CoreConsistent execution.atomic.relations.graph :=
  execution.atomic.toCoreConsistent

/-- Combined program-order/extended-coherence scheduling is derived acyclic. -/
theorem orderAcyclic
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    execution.atomic.relations.graph.OrderAcyclic :=
  execution.coreConsistent.orderAcyclic

/-- Allocator provenance and local replay typing are constructed, not assumed. -/
def graphTyping
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    GraphTyping execution.atomic.relations.graph
      (ModelInitial.initialized : TreiberRA.State α) :=
  execution.atomic.toGraphTyping

/--
Main checked-model result.

The first conjunct is exact equality of generated descriptor data with the
formal descriptor.  It does not itself certify source hashes, Clang, or the
C abstract machine; byte and hash checks live at the external extraction
boundary.  The remaining conjuncts are kernel-checked node-access safety and
classical Herlihy--Wing linearizability of the accepted finite client history.
-/
theorem verified
    [DecidableEq α]
    (execution : ValidatedTreiberModelExecution α) :
    TreiberProgramDescriptor.Extracted.treiberProgram.descriptor =
        TreiberProgramDescriptor.controlFlowDescriptor ∧
      NodeAccessCertificate execution.atomic.toControlledCandidate ∧
      HerlihyWing.Linearizable []
        (sourceHistory execution.atomic.source.skeleton) := by
  refine ⟨
    TreiberProgramDescriptor.extractedDescriptor_eq_controlFlowDescriptor,
    ?_⟩
  exact
    execution.model
      |>.herlihyWingLinearizable_and_nodeSafe_of_checked_client_order
        execution.nextReadValues
        execution.clientOrderChecked
        ModelInitial.represents_empty

end ValidatedTreiberModelExecution

namespace RawTreiberModelExecution

/--
Every execution in the explicitly supported checked model yields the complete
descriptor-agreement, node-safety, and Herlihy--Wing result.

This theorem quantifies over arbitrary finite raw inputs accepted by
`validate?`.  It is not a completeness theorem saying every execution of the
C source yields an accepted input.  The source-extraction/C-semantics trust
boundary described above remains explicit.
-/
theorem verified_of_supported
    [DecidableEq α]
    (raw : RawTreiberModelExecution α)
    (supported : raw.Supported) :
    ∃ execution : ValidatedTreiberModelExecution α,
      raw.validate? = some execution ∧
        TreiberProgramDescriptor.Extracted.treiberProgram.descriptor =
          TreiberProgramDescriptor.controlFlowDescriptor ∧
        NodeAccessCertificate
          execution.atomic.toControlledCandidate ∧
        HerlihyWing.Linearizable []
          (sourceHistory execution.atomic.source.skeleton) := by
  cases accepted : raw.validate? with
  | none =>
      simp [Supported, accepted] at supported
  | some execution =>
      exact ⟨execution, rfl,
        execution.verified.1,
        execution.verified.2.1,
        execution.verified.2.2⟩

end RawTreiberModelExecution

end WeakMemory.TreiberRC11
