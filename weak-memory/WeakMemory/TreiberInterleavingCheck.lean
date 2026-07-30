import WeakMemory.TreiberControlFlowCheck
import WeakMemory.TreiberControlledCandidate

namespace WeakMemory.TreiberRC11

/-!
# Executable checking of source interleavings

The global source list is checked in one pass while maintaining a local state
for every client thread.  Threads absent from the finite prefix remain idle.
The soundness theorem projects an accepted global run back to the existing
per-thread `ControlFlow.Execution` judgments.

The remaining source conditions are finite too: invocation IDs and push
reservations are duplicate-free, and every reserved node is absent from the
initial heap.
-/

namespace InterleavingCheck

/-- External source-label data before atomic thread ownership is certified. -/
structure RawOwnedLabel (α : Type) where
  thread : Nat
  label : ControlFlow.Label α
  deriving Repr, DecidableEq

namespace RawOwnedLabel

/-- Forget a certified ownership proof while preserving its exact raw data. -/
def ofOwned
    (owned : EventGraph.OwnedLabel α) :
    RawOwnedLabel α where
  thread :=
    owned.thread
  label :=
    owned.label

/-- Check and attach the ownership proof required by `EventGraph.OwnedLabel`. -/
def certify?
    (raw : RawOwnedLabel α) :
    Option (EventGraph.OwnedLabel α) :=
  match labelShape : raw.label with
  | .invokePush .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .invokePop .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .invokeIsEmpty .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .writeNext .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .readNext .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .respond .. =>
      some ⟨raw.thread, raw.label, by
        rw [labelShape]
        trivial⟩
  | .atomic _ action =>
      if owner : ControlFlow.actionThread action = raw.thread then
        some ⟨raw.thread, raw.label, by
          rw [labelShape]
          exact owner⟩
      else
        none

/-- Successful ownership certification preserves the submitted raw label. -/
theorem certify?_sound
    {raw : RawOwnedLabel α}
    {owned : EventGraph.OwnedLabel α}
    (accepted : raw.certify? = some owned) :
    ofOwned owned = raw := by
  rcases raw with ⟨thread, label⟩
  cases label with
  | invokePush operation reserved value =>
      simp [certify?] at accepted
      subst owned
      rfl
  | invokePop operation =>
      simp [certify?] at accepted
      subst owned
      rfl
  | invokeIsEmpty operation =>
      simp [certify?] at accepted
      subst owned
      rfl
  | writeNext operation node next =>
      simp [certify?] at accepted
      subst owned
      rfl
  | readNext operation node next =>
      simp [certify?] at accepted
      subst owned
      rfl
  | atomic operation action =>
      by_cases owner :
          ControlFlow.actionThread action = thread
      · simp [certify?, owner] at accepted
        subst owned
        rfl
      · simp [certify?, owner] at accepted
  | respond operation response =>
      simp [certify?] at accepted
      subst owned
      rfl

/--
Erasing and recertifying an already owned label returns that exact label.
Ownership proofs may be reconstructed differently, but proof irrelevance
identifies the resulting `OwnedLabel` values.
-/
theorem certify?_ofOwned
    (owned : EventGraph.OwnedLabel α) :
    (ofOwned owned).certify? = some owned := by
  rcases owned with ⟨thread, label, ownership⟩
  cases label with
  | invokePush operation reserved value =>
      simp [ofOwned, certify?]
  | invokePop operation =>
      simp [ofOwned, certify?]
  | invokeIsEmpty operation =>
      simp [ofOwned, certify?]
  | writeNext operation node next =>
      simp [ofOwned, certify?]
  | readNext operation node next =>
      simp [ofOwned, certify?]
  | atomic operation action =>
      have owner :
          ControlFlow.actionThread action = thread :=
        ownership
      simp [ofOwned, certify?, owner]
  | respond operation response =>
      simp [ofOwned, certify?]

end RawOwnedLabel

/-- Certify every raw owned label, preserving its finite order. -/
def certifyLabels? :
    List (RawOwnedLabel α) →
      Option (List (EventGraph.OwnedLabel α))
  | [] =>
      some []
  | raw :: rest =>
      match raw.certify?, certifyLabels? rest with
      | some owned, some certified =>
          some (owned :: certified)
      | _, _ =>
          none

/--
Successful list certification preserves every submitted thread and label in
the same order.
-/
theorem certifyLabels?_sound
    {rawLabels : List (RawOwnedLabel α)}
    {ownedLabels : List (EventGraph.OwnedLabel α)}
    (accepted :
      certifyLabels? rawLabels = some ownedLabels) :
    ownedLabels.map RawOwnedLabel.ofOwned = rawLabels := by
  induction rawLabels generalizing ownedLabels with
  | nil =>
      simp [certifyLabels?] at accepted
      subst ownedLabels
      rfl
  | cons raw rest inductionHypothesis =>
      unfold certifyLabels? at accepted
      cases headCertified : raw.certify? with
      | none =>
          simp [headCertified] at accepted
      | some owned =>
          cases restCertified : certifyLabels? rest with
          | none =>
              simp [headCertified, restCertified] at accepted
          | some certified =>
              simp only [headCertified, restCertified,
                Option.some.injEq] at accepted
              subst ownedLabels
              simp [RawOwnedLabel.certify?_sound headCertified,
                inductionHypothesis restCertified]

/-- Erasing and recertifying a finite owned-label list is an exact round trip. -/
theorem certifyLabels?_ofOwned
    (ownedLabels : List (EventGraph.OwnedLabel α)) :
    certifyLabels?
        (ownedLabels.map RawOwnedLabel.ofOwned) =
      some ownedLabels := by
  induction ownedLabels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      simp [certifyLabels?,
        RawOwnedLabel.certify?_ofOwned,
        inductionHypothesis]

/-- Current local control state for every possible client thread. -/
abbrev ThreadStates (α : Type) :=
  Nat → ControlFlow.LocalState α

/-- Before the source prefix, every client thread is idle. -/
def initialStates : ThreadStates α :=
  fun _ => .idle

/-- Change exactly one thread's local control state. -/
def update
    (states : ThreadStates α)
    (thread : Nat)
    (next : ControlFlow.LocalState α) :
    ThreadStates α :=
  fun query =>
    if query = thread then next else states query

@[simp] theorem update_same
    (states : ThreadStates α)
    (thread : Nat)
    (next : ControlFlow.LocalState α) :
    update states thread next thread = next := by
  simp [update]

theorem update_other
    (states : ThreadStates α)
    {owner thread : Nat}
    (different : thread ≠ owner)
    (next : ControlFlow.LocalState α) :
    update states owner next thread = states thread := by
  simp [update, different]

/--
Check one globally interleaved source prefix.

Ownership is already attached to `OwnedLabel`; `ControlFlow.step?` checks that
the label is enabled in its owner's current local state.
-/
def run?
    [DecidableEq α] :
    ThreadStates α →
      List (EventGraph.OwnedLabel α) →
      Option (ThreadStates α)
  | states, [] =>
      some states
  | states, owned :: rest =>
      match ControlFlow.step?
          owned.thread (states owned.thread) owned.label with
      | none =>
          none
      | some next =>
          run? (update states owned.thread next) rest

/--
An accepted global source run induces the exact existing local execution for
every thread projection.
-/
theorem run?_sound
    [DecidableEq α]
    {states finalStates : ThreadStates α}
    {labels : List (EventGraph.OwnedLabel α)}
    (accepted :
      run? states labels = some finalStates) :
    ∀ thread,
      ControlFlow.Execution thread
        (states thread)
        (Interleaving.labelsForThread thread labels)
        (finalStates thread) := by
  induction labels generalizing states with
  | nil =>
      simp only [run?, Option.some.injEq] at accepted
      subst finalStates
      intro thread
      exact .nil (states thread)
  | cons owned rest inductionHypothesis =>
      unfold run? at accepted
      cases checked :
          ControlFlow.step?
            owned.thread (states owned.thread) owned.label with
      | none =>
          simp [checked] at accepted
      | some next =>
          simp only [checked] at accepted
          have restExecution :=
            inductionHypothesis accepted
          intro thread
          by_cases sameOwner : owned.thread = thread
          · subst thread
            simp only [Interleaving.labelsForThread,
              ↓reduceIte]
            exact .cons owned.label
              (Interleaving.labelsForThread owned.thread rest)
              (ControlFlow.step?_sound checked)
              (by
                simpa using restExecution owned.thread)
          · have threadNeOwner : thread ≠ owned.thread :=
              Ne.symm sameOwner
            simp only [Interleaving.labelsForThread,
              sameOwner, ↓reduceIte]
            simpa [update_other states threadNeOwner next] using
              restExecution thread

/--
If every thread projection is an inductive local execution, the global
one-pass checker accepts.  Thus the interleaving checker does not narrow the
existing logical source semantics.
-/
theorem run?_complete_of_local
    [DecidableEq α]
    {states : ThreadStates α}
    {labels : List (EventGraph.OwnedLabel α)}
    (executions :
      ∀ thread,
        ∃ final,
          ControlFlow.Execution thread
            (states thread)
            (Interleaving.labelsForThread thread labels)
            final) :
    ∃ finalStates,
      run? states labels = some finalStates := by
  induction labels generalizing states with
  | nil =>
      exact ⟨states, rfl⟩
  | cons owned rest inductionHypothesis =>
      obtain ⟨ownerFinal, ownerExecution⟩ :=
        executions owned.thread
      simp only [Interleaving.labelsForThread,
        ↓reduceIte] at ownerExecution
      cases ownerExecution with
      | @cons initialState middle finalState label tail first later =>
          have checked :
              ControlFlow.step? owned.thread
                  (states owned.thread) owned.label =
                some middle :=
            ControlFlow.step?_complete first
          have restLocal :
              ∀ thread,
                ∃ final,
                  ControlFlow.Execution thread
                    (update states owned.thread middle thread)
                    (Interleaving.labelsForThread thread rest)
                    final := by
            intro thread
            by_cases sameOwner : owned.thread = thread
            · subst thread
              exact ⟨ownerFinal, by
                simpa using later⟩
            · obtain ⟨final, execution⟩ := executions thread
              have threadNeOwner :
                  thread ≠ owned.thread :=
                Ne.symm sameOwner
              simp only [Interleaving.labelsForThread,
                sameOwner, ↓reduceIte] at execution
              exact ⟨final, by
                simpa [update_other states
                  threadNeOwner middle] using execution⟩
          obtain ⟨finalStates, restAccepted⟩ :=
            inductionHypothesis restLocal
          refine ⟨finalStates, ?_⟩
          unfold run?
          rw [checked]
          exact restAccepted

/-- Test whether an allocator lookup is empty without comparing payloads. -/
def isNone : Option γ → Bool
  | none =>
      true
  | some _ =>
      false

/-- Every finite push reservation is absent from the initial heap. -/
def reservationsFresh
    (initial : TreiberRA.State α)
    (skeleton : EventGraph.Skeleton α) :
    Bool :=
  (Interleaving.pushReservations skeleton.labels).all
    fun reserved => isNone (initial.heap reserved)

/-- The finite freshness check is sound. -/
theorem reservationsFresh_sound
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (checked : reservationsFresh initial skeleton = true)
    {reserved : TreiberRA.NodeId}
    (member :
      reserved ∈
        Interleaving.pushReservations skeleton.labels) :
    initial.heap reserved = none := by
  simp only [reservationsFresh, List.all_eq_true] at checked
  have empty := checked reserved member
  cases lookup : initial.heap reserved with
  | none =>
      rfl
  | some record =>
      simp [isNone, lookup] at empty

/-- Logical reservation freshness makes the finite check pass. -/
theorem reservationsFresh_complete
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (fresh :
      ∀ {reserved : TreiberRA.NodeId},
        reserved ∈
            Interleaving.pushReservations skeleton.labels →
          initial.heap reserved = none) :
    reservationsFresh initial skeleton = true := by
  simp only [reservationsFresh, List.all_eq_true]
  intro reserved member
  simp [isNone, fresh member]

/--
Finite executable source-skeleton checker.

The successful interleaving run is inspected only for success; its final
thread-state function is recovered again in the soundness proof.
-/
def sourceSkeleton
    [DecidableEq α]
    (initial : TreiberRA.State α)
    (skeleton : EventGraph.Skeleton α) :
    Bool :=
  match run? initialStates skeleton.labels with
  | none =>
      false
  | some _ =>
      decide
          (Interleaving.invocationOperations
            skeleton.labels).Nodup &&
        decide
          (Interleaving.pushReservations
            skeleton.labels).Nodup &&
        reservationsFresh initial skeleton

/-- Passing the finite checker constructs the full logical source certificate. -/
theorem sourceSkeleton_sound
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (checked :
      sourceSkeleton initial skeleton = true) :
    Interleaving.SourceSkeleton initial skeleton := by
  unfold sourceSkeleton at checked
  cases accepted : run? initialStates skeleton.labels with
  | none =>
      simp [accepted] at checked
  | some finalStates =>
      have rawChecks :
          ((Interleaving.invocationOperations
                skeleton.labels).Nodup ∧
              (Interleaving.pushReservations
                skeleton.labels).Nodup) ∧
            reservationsFresh initial skeleton = true := by
        simpa [accepted] using checked
      have finiteChecks :
          (Interleaving.invocationOperations
              skeleton.labels).Nodup ∧
            (Interleaving.pushReservations
              skeleton.labels).Nodup ∧
            reservationsFresh initial skeleton = true :=
        ⟨rawChecks.1.1, rawChecks.1.2, rawChecks.2⟩
      refine {
        execution := ?_
        operationIdsNodup :=
          finiteChecks.1
        reservationsNodup :=
          finiteChecks.2.1
        reservationsFresh := ?_
      }
      · intro thread
        exact ⟨finalStates thread,
          run?_sound accepted thread⟩
      · intro reserved member
        exact reservationsFresh_sound
          finiteChecks.2.2 member

/-- Every logical source certificate is accepted by the executable checker. -/
theorem sourceSkeleton_complete
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (valid :
      Interleaving.SourceSkeleton initial skeleton) :
    sourceSkeleton initial skeleton = true := by
  obtain ⟨finalStates, accepted⟩ :=
    run?_complete_of_local
      (states := initialStates)
      (labels := skeleton.labels)
      (by
        intro thread
        simpa [initialStates] using
          valid.execution thread)
  simp [sourceSkeleton, accepted,
    valid.operationIdsNodup,
    valid.reservationsNodup,
    reservationsFresh_complete valid.reservationsFresh]

/-- The finite checker exactly characterizes the logical source certificate. -/
theorem sourceSkeleton_eq_true_iff
    [DecidableEq α]
    (initial : TreiberRA.State α)
    (skeleton : EventGraph.Skeleton α) :
    sourceSkeleton initial skeleton = true ↔
      Interleaving.SourceSkeleton initial skeleton :=
  ⟨sourceSkeleton_sound, sourceSkeleton_complete⟩

/-- A source skeleton paired only with the result of its executable check. -/
structure CheckedSource
    [DecidableEq α]
    (initial : TreiberRA.State α) where
  skeleton :
    EventGraph.Skeleton α
  checked :
    sourceSkeleton initial skeleton = true

namespace CheckedSource

/-- Turn checked finite data into the existing proof-carrying source package. -/
def toControlledSource
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (source : CheckedSource initial) :
    ControlledSource initial where
  skeleton :=
    source.skeleton
  valid :=
    sourceSkeleton_sound source.checked

end CheckedSource

/--
Run the source checker and return the existing certified package on success.
No caller supplies a local-execution or freshness proof.
-/
def validate?
    [DecidableEq α]
    (initial : TreiberRA.State α)
    (skeleton : EventGraph.Skeleton α) :
    Option (ControlledSource initial) :=
  if checked : sourceSkeleton initial skeleton = true then
    some {
      skeleton := skeleton
      valid := sourceSkeleton_sound checked
    }
  else
    none

/-- Every value returned by the validator contains the submitted skeleton. -/
theorem validate?_sound
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    {source : ControlledSource initial}
    (accepted : validate? initial skeleton = some source) :
    source.skeleton = skeleton := by
  unfold validate? at accepted
  split at accepted
  · have same := Option.some.inj accepted
    exact (congrArg ControlledSource.skeleton same).symm
  · contradiction

/--
Validating the skeleton already carried by a `ControlledSource` returns that
same package.  The reconstructed validity proof is identified with the
original one by proof irrelevance.
-/
theorem validate?_complete
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (source : ControlledSource initial) :
    validate? initial source.skeleton = some source := by
  have checked :
      sourceSkeleton initial source.skeleton = true :=
    sourceSkeleton_complete source.valid
  unfold validate?
  simp [checked]

/-- Canonical raw owner/label serialization of a controlled source. -/
def rawLabels
    {initial : TreiberRA.State α}
    (source : ControlledSource initial) :
    List (RawOwnedLabel α) :=
  source.skeleton.labels.map RawOwnedLabel.ofOwned

/--
Complete source-front validator for raw owner/label pairs.  Success returns a
`ControlledSource`, not an unchecked Boolean.
-/
def validateRaw?
    [DecidableEq α]
    (initial : TreiberRA.State α)
    (labels : List (RawOwnedLabel α)) :
    Option (ControlledSource initial) :=
  match certifyLabels? labels with
  | none =>
      none
  | some owned =>
      validate? initial { labels := owned }

/--
Every accepted raw validation exposes the exact certified list used to build
the returned source skeleton.  Forgetting its ownership proofs recovers the
submitted raw list without reordering or changing data.
-/
theorem validateRaw?_sound
    [DecidableEq α]
    {initial : TreiberRA.State α}
    {rawLabels : List (RawOwnedLabel α)}
    {source : ControlledSource initial}
    (accepted :
      validateRaw? initial rawLabels = some source) :
    ∃ ownedLabels : List (EventGraph.OwnedLabel α),
      certifyLabels? rawLabels = some ownedLabels ∧
        ownedLabels.map RawOwnedLabel.ofOwned = rawLabels ∧
        source.skeleton =
          ({ labels := ownedLabels } :
            EventGraph.Skeleton α) := by
  unfold validateRaw? at accepted
  cases certifiedShape : certifyLabels? rawLabels with
  | none =>
      simp [certifiedShape] at accepted
  | some ownedLabels =>
      simp only [certifiedShape] at accepted
      exact ⟨ownedLabels, rfl,
        certifyLabels?_sound certifiedShape,
        validate?_sound accepted⟩

/--
Erasing a controlled source to raw labels and running the complete raw
validator reconstructs the original `ControlledSource`.
-/
theorem validateRaw?_complete
    [DecidableEq α]
    {initial : TreiberRA.State α}
    (source : ControlledSource initial) :
    validateRaw? initial (rawLabels source) =
      some source := by
  unfold validateRaw? rawLabels
  rw [certifyLabels?_ofOwned]
  exact validate?_complete source

end InterleavingCheck

end WeakMemory.TreiberRC11
