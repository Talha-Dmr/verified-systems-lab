import WeakMemory.TreiberVerifiedModel
import WeakMemory.TreiberVerifiedModelProvenance

namespace WeakMemory.TreiberRC11

/-!
# Contract for an external execution frontend

This module states the remaining source/execution frontend obligation without
choosing or postulating a language semantics.  An external semantics supplies
its own execution type, allowed-execution predicate, pinned program identity,
and client-visible history.  A pure frontend only translates one such
execution into the finite raw data consumed by the checked Treiber validator.

`FrontendContract` is deliberately explicit about the unproved boundary.  It
requires every allowed external execution to produce an exact successful
`validate?` result, and requires the externally observed history to equal the
history reconstructed from that result.  Validator acceptance alone is not
called a C or C11 semantics.
-/

/--
The data exposed by an independently defined execution semantics.

Nothing in this structure constrains how executions are generated.  In
particular, `allowed` is owned by the external semantics rather than being
defined in terms of the Lean validator.
-/
structure ExternalExecutionSemantics (α : Type) where
  Execution : Type
  program : TreiberProgramDescriptor.PinnedExtraction
  allowed : Execution → Prop
  observedHistory : Execution → HerlihyWing.History α

/--
A pure translation from external executions to untrusted validator inputs.

This field contains data only: it carries no proof that the translation is
complete, faithful, or accepted.
-/
structure PureExecutionFrontend
    (semantics : ExternalExecutionSemantics α) where
  toRaw :
    semantics.Execution →
      RawTreiberModelExecution α

/--
The proof obligations for refining an external execution semantics into the
checked Treiber model.

`validationComplete` is exact: it produces the particular validated value
returned by `validate?`, not merely an `isSome` fact.  `historyFidelity`
connects the independently observed client history to the source history of
that exact validated value.
-/
structure FrontendContract
    [DecidableEq α]
    (semantics : ExternalExecutionSemantics α)
    (frontend : PureExecutionFrontend semantics) : Prop where
  programPinned :
    semantics.program =
      TreiberProgramDescriptor.Extracted.treiberProgram
  validationComplete :
    ∀ execution,
      semantics.allowed execution →
        ∃ validated : ValidatedTreiberModelExecution α,
          (frontend.toRaw execution).validate? =
            some validated
  historyFidelity :
    ∀ execution,
      semantics.allowed execution →
        ∀ validated : ValidatedTreiberModelExecution α,
          (frontend.toRaw execution).validate? =
              some validated →
            semantics.observedHistory execution =
              sourceHistory
                validated.atomic.source.skeleton

/--
All guarantees transferred to one allowed external execution.

The validation provenance retains the exact raw fields emitted by the
frontend.  Program pinning is kept separate from descriptor refinement:
pinning identifies the external semantics' intended source artifact, while
descriptor refinement is the kernel-checked equality used by the Treiber
proof.
-/
structure AllowedExecutionGuarantees
    [DecidableEq α]
    (semantics : ExternalExecutionSemantics α)
    (frontend : PureExecutionFrontend semantics)
    (execution : semantics.Execution) where
  validated :
    ValidatedTreiberModelExecution α
  validationResult :
    (frontend.toRaw execution).validate? =
      some validated
  validationProvenance :
    RawValidationProvenance
      (frontend.toRaw execution)
      validated
  programIdentity :
    semantics.program =
      TreiberProgramDescriptor.Extracted.treiberProgram
  descriptorAgreement :
    TreiberProgramDescriptor.Extracted.treiberProgram.descriptor =
      TreiberProgramDescriptor.controlFlowDescriptor
  historyFidelity :
    semantics.observedHistory execution =
      sourceHistory validated.atomic.source.skeleton
  nodeAccessSafe :
    NodeAccessCertificate
      validated.atomic.toControlledCandidate
  linearizable :
    HerlihyWing.Linearizable []
      (semantics.observedHistory execution)

/--
An exact frontend refinement contract transfers proof-relevant validator
provenance, pinned-program identity, descriptor agreement, node-access safety,
and Herlihy--Wing linearizability to every execution allowed by the external
semantics.

This theorem is conditional on `FrontendContract`; it does not construct a
frontend for any particular C or weak-memory semantics.
-/
theorem verified_of_external_allowed
    [DecidableEq α]
    {semantics : ExternalExecutionSemantics α}
    {frontend : PureExecutionFrontend semantics}
    (contract : FrontendContract semantics frontend)
    (execution : semantics.Execution)
    (allowed : semantics.allowed execution) :
    Nonempty
      (AllowedExecutionGuarantees semantics frontend execution) := by
  obtain ⟨validated, accepted⟩ :=
    contract.validationComplete execution allowed
  have modelVerified :=
    validated.verified
  have historyFidelity :=
    contract.historyFidelity execution allowed validated accepted
  exact ⟨{
    validated :=
      validated
    validationResult :=
      accepted
    validationProvenance :=
      RawTreiberModelExecution.validate?_provenance accepted
    programIdentity :=
      contract.programPinned
    descriptorAgreement :=
      modelVerified.1
    historyFidelity :=
      historyFidelity
    nodeAccessSafe :=
      modelVerified.2.1
    linearizable := by
      rw [historyFidelity]
      exact modelVerified.2.2
  }⟩

end WeakMemory.TreiberRC11
