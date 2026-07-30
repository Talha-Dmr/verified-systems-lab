import WeakMemory.TreiberNodeAccessDerivation

namespace WeakMemory.TreiberRC11

/-!
# Executable immutable `next`-read checking

The source trace records the value returned by every non-atomic
`node->next` read.  The canonical allocator table records the immutable node
published by each successful push.  This finite checker compares those two
representations and constructs `NextReadValueCertificate`.
-/

namespace NextReadCheck

/-- Check one owned source label against the final allocator table. -/
def label
    (allocator : AllocatorTable α)
    (owned : EventGraph.OwnedLabel α) :
    Bool :=
  match owned.label with
  | .readNext _ node next =>
      match allocator node with
      | none =>
          false
      | some (_, record) =>
          decide (record.next = next)
  | _ =>
      true

/-- Check every finite source-label occurrence. -/
def check
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    Bool :=
  execution.source.skeleton.labels.all
    (label execution.allocator)

/-- A selected occurrence is a member of its source skeleton. -/
private theorem SourceOccurrence.selected_mem
    {skeleton : EventGraph.Skeleton α}
    (occurrence : EventGraph.SourceOccurrence skeleton) :
    occurrence.selected ∈ skeleton.labels := by
  rw [occurrence.labelsShape]
  simp

/-- Passing the finite check constructs the full immutable-value certificate. -/
theorem check_sound
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    (checked : check execution = true) :
    NextReadValueCertificate execution := by
  refine {
    matchesAllocator := ?_
  }
  intro fieldRead operation node next readLabel
  have allLabels :
      ∀ owned ∈ execution.source.skeleton.labels,
        label execution.allocator owned = true := by
    simpa [check] using checked
  have selected :=
    allLabels fieldRead.selected
      (SourceOccurrence.selected_mem fieldRead)
  simp only [label, readLabel] at selected
  cases lookup : execution.allocator node with
  | none =>
      simp [lookup] at selected
  | some allocation =>
      rcases allocation with ⟨publisher, record⟩
      have nextShape : record.next = next := by
        simpa [lookup] using selected
      refine ⟨publisher, record.value, ?_⟩
      cases record
      simp_all

/--
Every logical immutable-value certificate makes the finite checker pass.

For a selected `readNext` label, finite list membership supplies its concrete
source occurrence; the certificate then supplies the allocator lookup used by
the Boolean label check.
-/
theorem check_complete
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    (certificate : NextReadValueCertificate execution) :
    check execution = true := by
  simp only [check, List.all_eq_true]
  intro owned member
  cases labelShape : owned.label with
  | invokePush operation reserved value =>
      simp [label, labelShape]
  | invokePop operation =>
      simp [label, labelShape]
  | invokeIsEmpty operation =>
      simp [label, labelShape]
  | writeNext operation node next =>
      simp [label, labelShape]
  | readNext operation node next =>
      obtain ⟨leading, trailing, labelsShape⟩ :=
        List.append_of_mem member
      let occurrence :
          EventGraph.SourceOccurrence
            execution.source.skeleton := {
        leading :=
          leading
        selected :=
          owned
        trailing :=
          trailing
        labelsShape :=
          labelsShape
      }
      obtain ⟨publisher, payload, allocatorShape⟩ :=
        certificate.matchesAllocator
          occurrence operation node next (by
            change owned.label =
              .readNext operation node next
            exact labelShape)
      simp [label, labelShape, allocatorShape]
  | atomic operation action =>
      simp [label, labelShape]
  | respond operation response =>
      simp [label, labelShape]

/-- The finite Boolean checker exactly characterizes its logical certificate. -/
theorem check_eq_true_iff
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) :
    check execution = true ↔
      NextReadValueCertificate execution :=
  ⟨check_sound, check_complete⟩

/-- Checked input wrapper for validator composition. -/
structure Checked
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial) : Prop where
  accepted :
    check execution = true

namespace Checked

/-- Forget the Boolean result after constructing its logical certificate. -/
theorem toCertificate
    {initial : TreiberRA.State α}
    {execution : SourceAtomicExecution initial}
    (checked : Checked execution) :
    NextReadValueCertificate execution :=
  check_sound checked.accepted

end Checked

end NextReadCheck

end WeakMemory.TreiberRC11
