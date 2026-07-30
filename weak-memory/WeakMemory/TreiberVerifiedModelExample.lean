import WeakMemory.TreiberVerifiedModel

namespace WeakMemory.TreiberRC11.VerifiedModelExample

/-!
# Executable validator example

One thread pushes payload `7` at node `1` and then pops it.  The raw input
contains only observed source labels, finite RF/MO choices, an ID schedule,
and the successful-pop publication path.
-/

private def owned
    (label : ControlFlow.Label Nat) :
    InterleavingCheck.RawOwnedLabel Nat where
  thread :=
    0
  label :=
    label

/-- Raw finite execution: `push(7); pop()`. -/
def raw : RawTreiberModelExecution Nat where
  sourceLabels := [
    owned (.invokePush 1 1 7),
    owned (.atomic 1 (.pushLoad 0 none)),
    owned (.writeNext 1 1 none),
    owned (.atomic 1 (.pushSuccess 0 1 7 none)),
    owned (.respond 1 .pushed),
    owned (.invokePop 2),
    owned (.atomic 2 (.popLoad 0 (some 1))),
    owned (.readNext 2 1 none),
    owned (.atomic 2 (.popSuccess 0 1 7 none)),
    owned (.respond 2 (.popped (some 7)))
  ]
  relationData := {
    writeTail := [2, 4]
    readSources := [
      (1, 0),
      (2, 0),
      (3, 2),
      (4, 2)
    ]
  }
  relationSchedule := [0, 1, 2, 3, 4]
  popPublications := [{
    popEventId := 4
    path := {
      source := 2
      first := {
        tag := .rf
        target := 4
      }
      rest := []
    }
  }]

/-- The complete raw pipeline accepts the example by computation. -/
theorem raw_isAccepted :
    raw.validate?.isSome = true := by
  rfl

/-- Acceptance yields the full checked-model safety and linearizability result. -/
theorem exists_verified :
    ∃ execution : ValidatedTreiberModelExecution Nat,
      raw.validate? = some execution ∧
        NodeAccessCertificate
          execution.atomic.toControlledCandidate ∧
        HerlihyWing.Linearizable []
          (sourceHistory execution.atomic.source.skeleton) := by
  cases accepted : raw.validate? with
  | none =>
      have impossible := raw_isAccepted
      simp [accepted] at impossible
  | some execution =>
      exact ⟨execution, rfl,
        execution.verified.2.1,
        execution.verified.2.2⟩

end WeakMemory.TreiberRC11.VerifiedModelExample
