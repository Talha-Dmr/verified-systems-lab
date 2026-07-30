import WeakMemory.TreiberC11V1ClientFrontend

namespace WeakMemory.TreiberC11V1.PushUniqueness

/-!
# Uniqueness of successful push publishers

The independent client contract reserves every pushed node exactly once.
This module connects that reservation discipline to successful source CAS
occurrences.  The proof uses the source state machine to recover each
successful push's invocation and the already-derived source-completion
certificate to exclude two commits with the same operation identifier.
-/

private theorem eq_of_filterMap_nodup
    {extract : β → Option γ}
    {items : List β}
    (noDuplicates : (items.filterMap extract).Nodup)
    {first second : β}
    {value : γ}
    (firstMember : first ∈ items)
    (secondMember : second ∈ items)
    (firstExtracts : extract first = some value)
    (secondExtracts : extract second = some value) :
    first = second := by
  induction items generalizing first second with
  | nil =>
      simp at firstMember
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp firstMember with
          firstIsHead | firstInRest
      · subst first
        rcases List.mem_cons.mp secondMember with
            secondIsHead | secondInRest
        · exact secondIsHead.symm
        · have valueMember :
              value ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr
              ⟨second, secondInRest, secondExtracts⟩
          have shapedNodup :
              (value :: rest.filterMap extract).Nodup := by
            simpa [firstExtracts] using noDuplicates
          exact
            ((List.nodup_cons.mp shapedNodup).1
              valueMember).elim
      · rcases List.mem_cons.mp secondMember with
            secondIsHead | secondInRest
        · subst second
          have valueMember :
              value ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr
              ⟨first, firstInRest, firstExtracts⟩
          have shapedNodup :
              (value :: rest.filterMap extract).Nodup := by
            simpa [secondExtracts] using noDuplicates
          exact
            ((List.nodup_cons.mp shapedNodup).1
              valueMember).elim
        · have restNodup :
              (rest.filterMap extract).Nodup :=
            ((List.sublist_cons_self head rest).filterMap extract).nodup
              noDuplicates
          exact inductionHypothesis restNodup
            firstInRest secondInRest
            firstExtracts secondExtracts

/-! ## Recovering the invocation of a successful push -/

/-- Local states belonging to one in-flight push invocation. -/
def InFlightPush
    (state : LocalState α)
    (operation : OperationId)
    (node : NodeId)
    (value : α) : Prop :=
  state = .pushLoading operation node value ∨
    ∃ expected,
      state = .pushWriting operation node value expected ∨
        state = .pushing operation node value expected

/-- Entering an in-flight push either preserves it or is its invocation. -/
theorem LocalStep.inFlightPush_predecessor
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    {operation : OperationId}
    {node : NodeId}
    {value : α}
    (step : LocalStep thread before event after)
    (active : InFlightPush after operation node value) :
    InFlightPush before operation node value ∨
      event = .invokePush thread operation node value := by
  cases step <;>
    simp [InFlightPush] at active ⊢
  all_goals exact active

namespace Run

/--
A successful push is attached to its invocation unless the supplied run
prefix already starts inside that invocation.
-/
theorem successfulPush_active_or_invoked
    {thread : ThreadId}
    {initial final : LocalState α}
    {events : List (TraceEvent α)}
    {id operation node : Nat}
    {value : α}
    {expected : Ptr}
    (run : Run thread initial events final)
    (member :
      TraceEvent.atomic
          ⟨id,
            .pushCas thread operation node value
              expected expected true⟩ ∈ events) :
    InFlightPush initial operation node value ∨
      TraceEvent.invokePush thread operation node value ∈ events := by
  induction run with
  | nil state =>
      simp at member
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with isFirst | inRest
      · subst event
        cases first
        exact Or.inl (by simp [InFlightPush])
      · rcases inductionHypothesis inRest with
          middleActive | invokedLater
        · rcases
            PushUniqueness.LocalStep.inFlightPush_predecessor
              first middleActive with
            initialActive | isInvocation
          · exact Or.inl initialActive
          · exact Or.inr (by simp [isInvocation])
        · exact Or.inr (by simp [invokedLater])

end Run

/-- Every successful push in an idle-started global run has its invocation. -/
theorem GlobalRun.successfulPush_hasInvocation
    {trace : List (TraceEvent α)}
    {id thread operation node : Nat}
    {value : α}
    {expected : Ptr}
    (run : GlobalRun trace)
    (member :
      TraceEvent.atomic
          ⟨id,
            .pushCas thread operation node value
              expected expected true⟩ ∈ trace) :
    TraceEvent.invokePush thread operation node value ∈ trace := by
  obtain ⟨final, localRun⟩ := run thread
  have projectedMember :
      TraceEvent.atomic
          ⟨id,
            .pushCas thread operation node value
              expected expected true⟩ ∈
        eventsForThread thread trace :=
    mem_eventsForThread_of_mem member rfl
  rcases Run.successfulPush_active_or_invoked
      localRun projectedMember with active | invoked
  · simp [InFlightPush] at active
  · exact mem_eventsForThread invoked

/-! ## Independent commit identifiers -/

/-- Operation identifier of one source linearization point, if present. -/
def traceCommitId? :
    TraceEvent α → Option OperationId
  | .atomic occurrence =>
      occurrence.action.toTarget.commit?.map
        (fun _ => occurrence.action.operation)
  | _ =>
      none

/-- Target source-commit projection retains exactly the independent ID. -/
@[simp] theorem sourceCommitId?_toOwnedLabel
    (payload : NodeId → α)
    (event : TraceEvent α) :
    (TreiberRC11.sourceCommit?
        (event.toOwnedLabel payload)).map
          HerlihyWing.IdentifiedCompleted.id =
      traceCommitId? event := by
  cases event with
  | invokePush | invokePop | invokeIsEmpty
  | writeNext | readNext
  | respondPush | respondIsEmpty =>
      rfl
  | respondPop thread operation result =>
      cases result <;> rfl
  | atomic occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | pushLoad thread operation observed =>
          cases observed <;> rfl
      | pushCas thread operation node value expected observed succeeded =>
          cases expected <;> cases observed <;> cases succeeded <;> rfl
      | popLoad thread operation observed =>
          cases observed <;> rfl
      | popCas thread operation expected value next observed succeeded =>
          cases next <;> cases observed <;> cases succeeded <;> rfl
      | isEmptyLoad thread operation observed =>
          cases observed <;> rfl

/-- Source completion IDs are the independent trace's commit-ID extraction. -/
theorem sourceCommitIds_projectedOwnedLabels
    (payload : NodeId → α)
    (trace : List (TraceEvent α)) :
    (TreiberRC11.sourceCommittedOperations
        ({ labels :=
            SourceFrontend.projectedOwnedLabels payload trace } :
          TreiberRC11.EventGraph.Skeleton α)).map
          HerlihyWing.IdentifiedCompleted.id =
      trace.filterMap traceCommitId? := by
  unfold TreiberRC11.sourceCommittedOperations
  unfold SourceFrontend.projectedOwnedLabels
  induction trace with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      simp only [List.map_cons, List.filterMap_cons]
      cases commit :
          TreiberRC11.sourceCommit?
            (event.toOwnedLabel payload) with
      | none =>
          have noCommit :
              traceCommitId? event = none := by
            have pointwise :=
              sourceCommitId?_toOwnedLabel payload event
            rw [commit] at pointwise
            exact pointwise.symm
          simp only [noCommit, inductionHypothesis]
      | some entry =>
          have hasCommit :
              traceCommitId? event = some entry.id := by
            have pointwise :=
              sourceCommitId?_toOwnedLabel payload event
            rw [commit] at pointwise
            exact pointwise.symm
          simp only [hasCommit, List.map_cons,
            inductionHypothesis]

/-- Independent commit identifiers are duplicate-free. -/
theorem SupportedExecution.traceCommitIdsNodup
    (execution : SupportedExecution α) :
    (execution.candidate.trace.filterMap traceCommitId?).Nodup := by
  have targetNodup :=
    execution.toControlledSource.valid.sourceCompletion.operationIdsNodup
  change
    ((TreiberRC11.sourceCommittedOperations
        ({ labels :=
            SourceFrontend.projectedOwnedLabels
              execution.candidate.payload
              execution.candidate.trace } :
          TreiberRC11.EventGraph.Skeleton α)).map
        HerlihyWing.IdentifiedCompleted.id).Nodup at targetNodup
  rw [sourceCommitIds_projectedOwnedLabels] at targetNodup
  exact targetNodup

/-! ## Publisher uniqueness -/

/--
Two successful push atoms allocating the same reclamation-free node are the
same source occurrence.  Consequently their immutable links are equal as
well.
-/
theorem SupportedExecution.successfulPush_unique
    (execution : SupportedExecution α)
    {leftId rightId leftThread rightThread
      leftOperation rightOperation node : Nat}
    {leftValue rightValue : α}
    {leftNext rightNext : Ptr}
    (leftMember :
      RC11.Atom.occurrence
          ⟨leftId,
            .pushCas leftThread leftOperation node leftValue
              leftNext leftNext true⟩ ∈
        execution.candidate.atoms)
    (rightMember :
      RC11.Atom.occurrence
          ⟨rightId,
            .pushCas rightThread rightOperation node rightValue
              rightNext rightNext true⟩ ∈
        execution.candidate.atoms) :
    RC11.Atom.occurrence
        ⟨leftId,
          .pushCas leftThread leftOperation node leftValue
            leftNext leftNext true⟩ =
      RC11.Atom.occurrence
        ⟨rightId,
          .pushCas rightThread rightOperation node rightValue
            rightNext rightNext true⟩ := by
  have leftTrace :
      TraceEvent.atomic
          ⟨leftId,
            .pushCas leftThread leftOperation node leftValue
              leftNext leftNext true⟩ ∈
        execution.candidate.trace :=
    execution.candidate.atomic_mem_trace_of_mem_atoms leftMember
  have rightTrace :
      TraceEvent.atomic
          ⟨rightId,
            .pushCas rightThread rightOperation node rightValue
              rightNext rightNext true⟩ ∈
        execution.candidate.trace :=
    execution.candidate.atomic_mem_trace_of_mem_atoms rightMember
  have leftInvocation :=
    PushUniqueness.GlobalRun.successfulPush_hasInvocation
      execution.client.globalRun leftTrace
  have rightInvocation :=
    PushUniqueness.GlobalRun.successfulPush_hasInvocation
      execution.client.globalRun rightTrace
  have sameInvocation :
      TraceEvent.invokePush
          leftThread leftOperation node leftValue =
        TraceEvent.invokePush
          rightThread rightOperation node rightValue := by
    apply eq_of_filterMap_nodup
        execution.client.pushNodesNodup
        leftInvocation rightInvocation
    · rfl
    · rfl
  have sameOperation :
      leftOperation = rightOperation := by
    simpa only [TraceEvent.operation] using
      congrArg TraceEvent.operation sameInvocation
  have sameAtomic :
      TraceEvent.atomic
          ⟨leftId,
            .pushCas leftThread leftOperation node leftValue
              leftNext leftNext true⟩ =
        TraceEvent.atomic
          ⟨rightId,
            .pushCas rightThread rightOperation node rightValue
              rightNext rightNext true⟩ := by
    apply eq_of_filterMap_nodup
        (PushUniqueness.SupportedExecution.traceCommitIdsNodup
          execution)
        leftTrace rightTrace
        (value := leftOperation)
    · rfl
    · change some rightOperation = some leftOperation
      exact congrArg some sameOperation.symm
  exact congrArg RC11.Atom.occurrence
    (TraceEvent.atomic.inj sameAtomic)

end WeakMemory.TreiberC11V1.PushUniqueness
