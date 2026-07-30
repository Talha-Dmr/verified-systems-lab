import WeakMemory.TreiberC11V1ClientFrontend
import WeakMemory.TreiberC11V1DerivedOrder
import WeakMemory.TreiberC11V1GenerationFrontend
import WeakMemory.TreiberC11V1RelationFrontend
import WeakMemory.TreiberC11V1ValidityFrontend
import WeakMemory.TreiberExecutionFrontend
import WeakMemory.TreiberSupportedModelSemantics

namespace WeakMemory.TreiberC11V1

/-!
# End-to-end frontend for the independent C11 execution model

This module is the final assembly point between the independently defined
`TreiberC11V1.DeclarativeExecution` semantics and the checked Treiber model.
Source projection, RC11 relation translation, event generation, immutable
node fields, and client real time are proved in their dedicated frontend
modules and combined here without adding a validator-acceptance premise.

The schedule-carrying `SupportedExecution` package is internal assembly data.
The public declarative execution type supplies only acyclicity of independent
program-order, extended-coherence, and committed real-time edges; a finite
topological construction derives the schedule consumed below.
-/

namespace SupportedExecution

/--
Assemble the target scheduled-relation model once source event generation has
constructed its final allocator.  Every relation and schedule field is the
canonical translation of the independent execution.
-/
def toScheduledRelationModelExecution
    [DecidableEq α]
    (execution : SupportedExecution α)
    (allocator : TreiberRC11.AllocatorTable α)
    (generated :
      TreiberRC11.GeneratedEvents
        execution.relationData.graph
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        allocator
        execution.toControlledSource.skeleton.events) :
    TreiberRC11.ScheduledRelationModelExecution
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α) where
  source :=
    execution.toControlledSource
  relations :=
    execution.relationData
  allocator :=
    allocator
  initialHeadEmpty :=
    TreiberRC11.ModelInitial.initialized_head
  generated :=
    generated
  relationSchedule :=
    execution.relationSchedule
  scheduleRespectsGraph :=
    execution.relationSchedule_respectsGraph

/--
The independent compatible order discharges the target model's cross-thread
real-time condition.  Exact source-history and commit-key projections connect
the two representations; source operation-ID uniqueness supplies key
injectivity.
-/
theorem toScheduledRelationModelExecution_crossThreadRealTime
    [DecidableEq α]
    (execution : SupportedExecution α)
    (allocator : TreiberRC11.AllocatorTable α)
    (generated :
      TreiberRC11.GeneratedEvents
        execution.relationData.graph
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        allocator
        execution.toControlledSource.skeleton.events) :
    TreiberRC11.CrossThreadRealTimeCompatible
      (execution.toScheduledRelationModelExecution
        allocator generated).toSourceAtomicExecution
      (execution.toScheduledRelationModelExecution
        allocator generated).relationSchedule := by
  let model :=
    execution.toScheduledRelationModelExecution
      allocator generated
  apply
    ClientFrontend.crossThreadRealTimeCompatible_of_projection
      execution.order
      model.toSourceAtomicExecution
      model.relationSchedule
  · exact ClientFrontend.sourceHistory_toControlledSource execution
  · simpa [model, toScheduledRelationModelExecution,
      relationSchedule, relationProjection,
      RelationFrontend.Projection.targetSchedule] using
        ClientFrontend.scheduledOperations_keys_toTarget
          execution
          model.toSourceAtomicExecution
          rfl
  · intro left right leftMember rightMember sameKey
    exact
      ClientFrontend.scheduledOperations_keyInjective
        model.toSourceAtomicExecution
        model.scheduleRespectsGraph
        leftMember rightMember sameKey

/--
Package a fully derived generation result, immutable-field certificate, and
client-order proof as the normalized model consumed by the complete validator
theorem.

This is an assembly helper, not an external premise: the concrete frontend
below instantiates its generation arguments from the independent execution,
while client real time is derived above.
-/
def toNormalizedSupportedModelExecutionOf
    [DecidableEq α]
    (execution : SupportedExecution α)
    (allocator : TreiberRC11.AllocatorTable α)
    (generated :
      TreiberRC11.GeneratedEvents
        execution.relationData.graph
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        allocator
        execution.toControlledSource.skeleton.events)
    (nextReadValues :
      TreiberRC11.NextReadValueCertificate
        (execution.toScheduledRelationModelExecution
          allocator generated).toSourceAtomicExecution) :
    TreiberRC11.NormalizedSupportedModelExecution α where
  model :=
    execution.toScheduledRelationModelExecution
      allocator generated
  relationsCanonical := by
    exact
      execution.relationProjection.atomicRelationData_canonical
        execution.rc11
  nextReadValues :=
    nextReadValues
  crossThreadRealTime :=
    execution.toScheduledRelationModelExecution_crossThreadRealTime
      allocator generated

/--
Every independently supported execution constructs its normalized checked
model without an additional graph-typing, publication, scheduling, replay, or
validator-acceptance premise.
-/
noncomputable def toNormalizedSupportedModelExecution
    [DecidableEq α]
    (execution : SupportedExecution α) :
    TreiberRC11.NormalizedSupportedModelExecution α := by
  let generation :=
    GenerationFrontend.generationResult execution
  apply
    execution.toNormalizedSupportedModelExecutionOf
      generation.allocator
      generation.generated
  refine {
    matchesAllocator := ?_
  }
  intro fieldRead operation node next readLabel
  exact
    generation.nextReadValueCertificate.matchesAllocator
      fieldRead operation node next readLabel

end SupportedExecution

namespace DeclarativeExecution

/--
Derive the internal client-compatible order and normalize the resulting
supported execution.  The declarative semantics does not expose the selected
topological schedule.
-/
noncomputable def toNormalizedSupportedModelExecution
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    TreiberRC11.NormalizedSupportedModelExecution α :=
  execution.toSupportedExecution.toNormalizedSupportedModelExecution

/--
Independent RC11 validity directly implies target core consistency, before
the declarative client-order acyclicity condition is used to select a replay
schedule.
-/
theorem projectedCoreConsistent
    (execution : DeclarativeExecution α) :
    TreiberRC11.CoreConsistent
      execution.toSupportedExecution.relationData.graph :=
  execution.toSupportedExecution.relationData_coreConsistent_of_rc11

/-- Target replay-order acyclicity is likewise an RC11 validity consequence. -/
theorem projectedOrderAcyclic
    (execution : DeclarativeExecution α) :
    execution.toSupportedExecution.relationData.graph.OrderAcyclic :=
  execution.toSupportedExecution.relationData_orderAcyclic_of_rc11

/-- RC11 validity alone supplies a finite graph-respecting target schedule. -/
theorem existsProjectedRelationSchedule
    (execution : DeclarativeExecution α) :
    ∃ schedule,
      TreiberRC11.RespectsGraph
        execution.toSupportedExecution.relationData.graph
        schedule :=
  execution.toSupportedExecution.exists_relationSchedule_of_rc11

/--
Concrete source generation supplies graph typing for the same projected graph
whose consistency is derived directly from independent RC11 validity.
-/
noncomputable def projectedGraphTyping
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    TreiberRC11.GraphTyping
      execution.toSupportedExecution.relationData.graph
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α) := by
  let supported :=
    execution.toSupportedExecution
  let generation :=
    GenerationFrontend.generationResult supported
  exact
    generation.toSourceAtomicExecution.toGraphTyping

/--
Direct RC11 core consistency and concrete generated graph typing jointly
construct an accepted operational replay and its certified schedule.  This
theorem deliberately uses `projectedCoreConsistent`, keeping independent
no-thin-air and coherence on the end-to-end replay dependency path.
-/
theorem existsCertifiedReplay_of_rc11
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    ∃ schedule final,
      TreiberRC11.RespectsGraph
          execution.toSupportedExecution.relationData.graph
          schedule ∧
        TreiberRC11.replay?
            (TreiberRC11.ModelInitial.initialized :
              TreiberRA.State α)
            schedule =
          some final ∧
        TreiberRC11.CertifiedSchedule
          execution.toSupportedExecution.relationData.graph
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          schedule final :=
  execution.projectedCoreConsistent
    |>.existsCertifiedSchedule_of_graphTyping
      execution.projectedGraphTyping

/--
The topologically derived schedule also carries the client real-time
certificate required by the Herlihy--Wing bridge.
-/
theorem derivedClientCompatibleSchedule
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    TreiberRC11.ClientCompatibleSchedule
      (execution.toNormalizedSupportedModelExecution
        |>.model.toSourceAtomicExecution)
      (execution.toNormalizedSupportedModelExecution
        |>.model.relationSchedule) where
  respectsGraph :=
    (execution.toNormalizedSupportedModelExecution
      |>.model.scheduleRespectsGraph)
  crossThreadRealTime :=
    (execution.toNormalizedSupportedModelExecution
      |>.crossThreadRealTime)

/--
The exact schedule selected from augmented client-order acyclicity replays
successfully.  Its proof combines the direct RC11-derived `WellFormed`
projection, generated graph typing, and the client-compatible schedule's
graph-order certificate.  The separate certified-replay theorem above retains
the full `CoreConsistent` certificate, including no-thin-air and coherence.
-/
theorem clientScheduleReplay_of_rc11
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    TreiberRC11.replay?
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        (execution.toNormalizedSupportedModelExecution
          |>.model.relationSchedule) =
      some
        (TreiberRC11.advanceUncheckedList
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          (execution.toNormalizedSupportedModelExecution
            |>.model.relationSchedule)) :=
  execution.projectedGraphTyping.replayAccepted
    execution.projectedCoreConsistent.toWellFormed
    execution.derivedClientCompatibleSchedule.respectsGraph

end DeclarativeExecution

namespace ExecutionFrontend

/--
Expose a proof-carrying execution type as an external semantics.  The caller
chooses an execution type whose inhabitants already carry the semantic
admissibility conditions, so every inhabitant is allowed.
-/
def semanticsOf
    {Execution : Type}
    (observedHistory :
      Execution →
        HerlihyWing.History α) :
    TreiberRC11.ExternalExecutionSemantics α where
  Execution :=
    Execution
  program :=
    TreiberProgramDescriptor.Extracted.treiberProgram
  allowed :=
    fun _ => True
  observedHistory :=
    observedHistory

/-- Serialize the normalized image of an independent execution. -/
noncomputable def frontendOf
    [DecidableEq α]
    {Execution : Type}
    (observedHistory :
      Execution →
        HerlihyWing.History α)
    (normalize :
      Execution →
        TreiberRC11.NormalizedSupportedModelExecution α) :
    TreiberRC11.PureExecutionFrontend
      (semanticsOf observedHistory) where
  toRaw :=
    fun execution =>
      (normalize execution).toRaw

/--
Exact normalization plus source-history fidelity supplies the complete
external-frontend contract.  Validator acceptance follows from normalized
model completeness; it is not an input to this theorem.
-/
theorem contractOf
    [DecidableEq α]
    {Execution : Type}
    (observedHistory :
      Execution →
        HerlihyWing.History α)
    (normalize :
      Execution →
        TreiberRC11.NormalizedSupportedModelExecution α)
    (sourceHistoryFidelity :
      ∀ execution,
        observedHistory execution =
          TreiberRC11.sourceHistory
            (normalize execution).model.source.skeleton) :
    TreiberRC11.FrontendContract
      (semanticsOf observedHistory)
      (frontendOf observedHistory normalize) where
  programPinned :=
    rfl
  validationComplete := by
    intro execution _
    have supported :=
      (normalize execution).toRaw_supported
    unfold TreiberRC11.RawTreiberModelExecution.Supported at supported
    exact Option.isSome_iff_exists.mp supported
  historyFidelity := by
    intro execution _ validated accepted
    change
      observedHistory execution =
        TreiberRC11.sourceHistory
          validated.model.source.skeleton
    have provenance :=
      TreiberRC11.RawTreiberModelExecution.validate?_provenance
        accepted
    have sourceSame :
        validated.model.source =
          (normalize execution).model.source :=
      Option.some.inj
        (provenance.sourceValidation.symm.trans
          (normalize execution).source_roundTrip)
    rw [sourceSame]
    exact sourceHistoryFidelity execution

/--
Every inhabitant of the independent execution type inherits the checked
program-identity, node-safety, and Herlihy--Wing guarantees after a concrete
normalization and history projection have been supplied.
-/
theorem verifiedOf
    [DecidableEq α]
    {Execution : Type}
    (observedHistory :
      Execution →
        HerlihyWing.History α)
    (normalize :
      Execution →
        TreiberRC11.NormalizedSupportedModelExecution α)
    (sourceHistoryFidelity :
      ∀ execution,
        observedHistory execution =
          TreiberRC11.sourceHistory
            (normalize execution).model.source.skeleton)
    (execution : Execution) :
    Nonempty
      (TreiberRC11.AllowedExecutionGuarantees
        (semanticsOf observedHistory)
        (frontendOf observedHistory normalize)
        execution) :=
  TreiberRC11.verified_of_external_allowed
    (contractOf observedHistory normalize sourceHistoryFidelity)
    execution
    trivial

/--
Client-visible history of the internal schedule-carrying bridge package.
-/
def supportedObservedHistory
    (execution : SupportedExecution α) :
    HerlihyWing.History α :=
  ClientFrontend.clientHistory execution.candidate

/--
Internal external-semantics view of the schedule-carrying bridge package.
The public declarative semantics below derives this package from acyclicity.
-/
def supportedSemantics :
    TreiberRC11.ExternalExecutionSemantics α :=
  semanticsOf supportedObservedHistory

/-- Every assembled normalized model preserves the independent client history. -/
theorem supportedObservedHistory_toNormalizedSupportedModelExecutionOf
    [DecidableEq α]
    (execution : SupportedExecution α)
    (allocator : TreiberRC11.AllocatorTable α)
    (generated :
      TreiberRC11.GeneratedEvents
        execution.relationData.graph
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        allocator
        execution.toControlledSource.skeleton.events)
    (nextReadValues :
      TreiberRC11.NextReadValueCertificate
        (execution.toScheduledRelationModelExecution
          allocator generated).toSourceAtomicExecution) :
    supportedObservedHistory execution =
      TreiberRC11.sourceHistory
        (execution.toNormalizedSupportedModelExecutionOf
          allocator generated nextReadValues).model.source.skeleton := by
  exact
    (ClientFrontend.sourceHistory_toControlledSource execution).symm

/-- Normalized frontend for the internal schedule-carrying bridge package. -/
noncomputable def supportedFrontend
    [DecidableEq α] :
    TreiberRC11.PureExecutionFrontend
      (supportedSemantics (α := α)) :=
  frontendOf
    supportedObservedHistory
    SupportedExecution.toNormalizedSupportedModelExecution

/-- Internal bridge normalization preserves the independently observed history. -/
theorem supportedObservedHistory_toNormalizedSupportedModelExecution
    [DecidableEq α]
    (execution : SupportedExecution α) :
    supportedObservedHistory execution =
      TreiberRC11.sourceHistory
        (execution.toNormalizedSupportedModelExecution).model.source.skeleton := by
  exact
    (ClientFrontend.sourceHistory_toControlledSource execution).symm

/--
The internal bridge frontend satisfies its exact contract.  This theorem is
consumed only after the public declarative acyclicity condition has been
topologically converted to a `SupportedExecution`.
-/
theorem supportedFrontendContract
    [DecidableEq α] :
    TreiberRC11.FrontendContract
      (supportedSemantics (α := α))
      (supportedFrontend (α := α)) := by
  simpa [supportedSemantics, supportedFrontend] using
    contractOf
      supportedObservedHistory
      SupportedExecution.toNormalizedSupportedModelExecution
      supportedObservedHistory_toNormalizedSupportedModelExecution

/--
Every internal schedule-carrying bridge package receives the checked
guarantees.  The public theorem below derives this package rather than asking
the semantic execution to supply it.
-/
theorem everySupportedExecution_verified
    [DecidableEq α]
    (execution : SupportedExecution α) :
    Nonempty
      (TreiberRC11.AllowedExecutionGuarantees
        (supportedSemantics (α := α))
        (supportedFrontend (α := α))
        execution) :=
  TreiberRC11.verified_of_external_allowed
    supportedFrontendContract
    execution
    trivial

/-- Direct Herlihy--Wing statement for the independent client history. -/
theorem everySupportedExecution_linearizable
    [DecidableEq α]
    (execution : SupportedExecution α) :
    HerlihyWing.Linearizable []
      (supportedObservedHistory execution) := by
  obtain ⟨guarantees⟩ :=
    everySupportedExecution_verified execution
  exact guarantees.linearizable

/-! ## Public declarative execution frontend -/

/-- Client-visible history read directly from a declarative source execution. -/
def declarativeObservedHistory
    (execution : DeclarativeExecution α) :
    HerlihyWing.History α :=
  ClientFrontend.clientHistory execution.candidate

/--
The public external semantics carries no selected event schedule: client-order
acyclicity is its only global scheduling condition.
-/
def declarativeSemantics :
    TreiberRC11.ExternalExecutionSemantics α :=
  semanticsOf declarativeObservedHistory

/-- Pure serialization frontend for declaratively admitted executions. -/
noncomputable def declarativeFrontend
    [DecidableEq α] :
    TreiberRC11.PureExecutionFrontend
      (declarativeSemantics (α := α)) :=
  frontendOf
    declarativeObservedHistory
    DeclarativeExecution.toNormalizedSupportedModelExecution

/-- Topological-order derivation and normalization preserve source history. -/
theorem declarativeObservedHistory_toNormalized
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    declarativeObservedHistory execution =
      TreiberRC11.sourceHistory
        (execution.toNormalizedSupportedModelExecution).model.source.skeleton := by
  exact
    (ClientFrontend.sourceHistory_toControlledSource
      execution.toSupportedExecution).symm

/--
The schedule-free declarative semantics satisfies the exact frontend contract.
-/
theorem declarativeFrontendContract
    [DecidableEq α] :
    TreiberRC11.FrontendContract
      (declarativeSemantics (α := α))
      (declarativeFrontend (α := α)) := by
  simpa [declarativeSemantics, declarativeFrontend] using
    contractOf
      declarativeObservedHistory
      DeclarativeExecution.toNormalizedSupportedModelExecution
      declarativeObservedHistory_toNormalized

/--
Every declaratively allowed execution receives exact validation provenance,
program identity, node-access safety, and Herlihy--Wing linearizability.
-/
theorem everyDeclarativeExecution_verified
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    Nonempty
      (TreiberRC11.AllowedExecutionGuarantees
        (declarativeSemantics (α := α))
        (declarativeFrontend (α := α))
        execution) :=
  TreiberRC11.verified_of_external_allowed
    declarativeFrontendContract
    execution
    trivial

/-- Direct Herlihy--Wing statement for every declaratively allowed history. -/
theorem everyDeclarativeExecution_linearizable
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    HerlihyWing.Linearizable []
      (declarativeObservedHistory execution) := by
  obtain ⟨guarantees⟩ :=
    everyDeclarativeExecution_verified execution
  exact guarantees.linearizable

/--
All end-to-end guarantees for one declaratively admitted execution.

`coreConsistent` and `orderAcyclic` come directly from independent
`RC11.Valid`, including its no-thin-air and coherence fields.  `graphTyping`
comes independently from concrete source-event generation.  `certifiedReplay`
is then constructed from those two certificates for that exact projected
graph.  The additional global scheduling condition is the augmented
PO/ECO/real-time acyclicity stored by `DeclarativeExecution`; its topological
construction supplies `clientCompatibleSchedule`.
-/
structure FullDeclarativeGuarantees
    [DecidableEq α]
    (execution : DeclarativeExecution α) where
  coreConsistent :
    TreiberRC11.CoreConsistent
      execution.toSupportedExecution.relationData.graph
  orderAcyclic :
    execution.toSupportedExecution.relationData.graph.OrderAcyclic
  graphTyping :
    TreiberRC11.GraphTyping
      execution.toSupportedExecution.relationData.graph
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α)
  certifiedReplay :
    ∃ schedule final,
      TreiberRC11.RespectsGraph
          execution.toSupportedExecution.relationData.graph
          schedule ∧
        TreiberRC11.replay?
            (TreiberRC11.ModelInitial.initialized :
              TreiberRA.State α)
            schedule =
          some final ∧
        TreiberRC11.CertifiedSchedule
          execution.toSupportedExecution.relationData.graph
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          schedule final
  clientCompatibleSchedule :
    TreiberRC11.ClientCompatibleSchedule
      (execution.toNormalizedSupportedModelExecution
        |>.model.toSourceAtomicExecution)
      (execution.toNormalizedSupportedModelExecution
        |>.model.relationSchedule)
  clientScheduleReplay :
    TreiberRC11.replay?
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        (execution.toNormalizedSupportedModelExecution
          |>.model.relationSchedule) =
      some
        (TreiberRC11.advanceUncheckedList
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          (execution.toNormalizedSupportedModelExecution
            |>.model.relationSchedule))
  allowedExecution :
    TreiberRC11.AllowedExecutionGuarantees
      (declarativeSemantics (α := α))
      (declarativeFrontend (α := α))
      execution
  linearizable :
    HerlihyWing.Linearizable []
      (declarativeObservedHistory execution)

/--
Every declarative execution receives the combined RC11-consistency,
generated-typing, certified-replay, client-schedule, validator-provenance,
node-safety, and Herlihy--Wing result.

The certified replay is built explicitly from the direct `RC11.Valid`
consistency proof and the generated graph typing proof, so the final bundle
does not bypass independent no-thin-air or coherence.
-/
theorem everyDeclarativeExecution_fullyVerified
    [DecidableEq α]
    (execution : DeclarativeExecution α) :
    Nonempty (FullDeclarativeGuarantees execution) := by
  obtain ⟨allowedExecution⟩ :=
    everyDeclarativeExecution_verified execution
  let coreConsistent :=
    execution.projectedCoreConsistent
  let graphTyping :=
    execution.projectedGraphTyping
  have certifiedReplay :=
    coreConsistent.existsCertifiedSchedule_of_graphTyping
      graphTyping
  exact ⟨{
    coreConsistent :=
      coreConsistent
    orderAcyclic :=
      execution.projectedOrderAcyclic
    graphTyping :=
      graphTyping
    certifiedReplay :=
      certifiedReplay
    clientCompatibleSchedule :=
      execution.derivedClientCompatibleSchedule
    clientScheduleReplay :=
      execution.clientScheduleReplay_of_rc11
    allowedExecution :=
      allowedExecution
    linearizable :=
      allowedExecution.linearizable
  }⟩

/-- The public declarative execution semantics is non-vacuously inhabited. -/
theorem declarativeSemantics_nonempty
    (payload : NodeId → α) :
    Nonempty
      (declarativeSemantics (α := α)).Execution :=
  ⟨DeclarativeExecution.empty payload⟩

end ExecutionFrontend

end WeakMemory.TreiberC11V1
