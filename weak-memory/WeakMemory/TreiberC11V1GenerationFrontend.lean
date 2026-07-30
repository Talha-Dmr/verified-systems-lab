import WeakMemory.TreiberC11V1ClientFrontend
import WeakMemory.TreiberC11V1PushUniqueness
import WeakMemory.TreiberC11V1RelationFrontend
import WeakMemory.TreiberGeneratedEventsCheck
import WeakMemory.TreiberNodeAccessSource

namespace WeakMemory.TreiberC11V1.GenerationFrontend

/-!
# Generated-event refinement for the independent Treiber C11-v1 semantics

This module proves the finite modification-order facts needed to recover the
unique successful-push origin of every non-null head write.  The construction
uses only the independent source run, client contract, and RC11 candidate; no
target `GraphTyping` or publication premise is assumed.
-/

open RC11

private theorem eq_of_mem_of_map_nodup
    {items : List β}
    {mapKey : β → γ}
    (keysNodup : (items.map mapKey).Nodup)
    {left right : β}
    (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (sameKey : mapKey left = mapKey right) :
    left = right := by
  induction items with
  | nil =>
      simp at leftMember
  | cons head tail inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp keysNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with leftIsHead | leftInTail
      · subst left
        rcases rightMember with rightIsHead | rightInTail
        · exact rightIsHead.symm
        · exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨right, rightInTail, sameKey.symm⟩)
      · rcases rightMember with rightIsHead | rightInTail
        · subst right
          exfalso
          exact nodupParts.1
            (List.mem_map.mpr
              ⟨left, leftInTail, sameKey⟩)
        · exact inductionHypothesis nodupParts.2
            leftInTail rightInTail

/-- Valid candidate identifiers identify at most one carrier atom. -/
theorem atom_eq_of_id_eq
    {candidate : Candidate α}
    (valid : Valid candidate)
    {left right : Atom α}
    (leftMember : left ∈ candidate.atoms)
    (rightMember : right ∈ candidate.atoms)
    (sameId : left.id = right.id) :
    left = right :=
  eq_of_mem_of_map_nodup valid.atomIdsNodup
    leftMember rightMember sameId

/-- Strict modification order is transitive. -/
theorem mo_transitive
    {candidate : Candidate α}
    {first middle last : Atom α}
    (firstMiddle : MO candidate first middle)
    (middleLast : MO candidate middle last) :
    MO candidate first last := by
  refine ⟨firstMiddle.1, middleLast.2.1, ?_⟩
  exact ⟨firstMiddle.2.2.1, middleLast.2.2.2.1,
    Nat.lt_trans firstMiddle.2.2.2.2
      middleLast.2.2.2.2⟩

/-- Immediate modification order contains an ordinary modification-order edge. -/
theorem mo_of_immediate
    {candidate : Candidate α}
    {source target : Atom α}
    (edge : ImmediateMO candidate source target) :
    MO candidate source target :=
  ⟨edge.1, edge.2.1, edge.2.2.2.2.1⟩

/-- Every independent successful RMW is also a write. -/
theorem isWrite_of_isRMW
    {atom : Atom α}
    (rmwShape : atom.IsRMW) :
    atom.IsWrite := by
  cases atom with
  | initial =>
      simp [Atom.IsRMW, Atom.isRMW] at rmwShape
  | occurrence occurrence =>
      rcases occurrence with ⟨id, action⟩
      cases action with
      | pushLoad =>
          simp [Atom.IsRMW, Atom.isRMW,
            AtomicAction.isRMW] at rmwShape
      | pushCas thread operation node value expected observed
          succeeded =>
          cases succeeded <;>
            simp [Atom.IsRMW, Atom.isRMW,
              Atom.IsWrite, Atom.writtenValue,
              AtomicAction.isRMW,
              AtomicAction.writtenValue] at rmwShape ⊢
      | popLoad =>
          simp [Atom.IsRMW, Atom.isRMW,
            AtomicAction.isRMW] at rmwShape
      | popCas thread operation expected value next observed
          succeeded =>
          cases succeeded <;>
            simp [Atom.IsRMW, Atom.isRMW,
              Atom.IsWrite, Atom.writtenValue,
              AtomicAction.isRMW,
              AtomicAction.writtenValue] at rmwShape ⊢
      | isEmptyLoad =>
          simp [Atom.IsRMW, Atom.isRMW,
            AtomicAction.isRMW] at rmwShape

/-- A successful RMW reads from its immediate modification-order predecessor. -/
theorem immediate_of_rmw_rf
    {candidate : Candidate α}
    (valid : Valid candidate)
    {source rmw : Atom α}
  (readsFrom : RF candidate source rmw)
  (rmwShape : rmw.IsRMW) :
    ImmediateMO candidate source rmw := by
  refine ⟨readsFrom.1, readsFrom.2.1, ?_, ?_, ?_⟩
  · have rmwReads :
        ∃ value, rmw.readValue = some value := by
      cases rmw with
      | initial =>
          simp [Atom.IsRMW, Atom.isRMW] at rmwShape
      | occurrence occurrence =>
          rcases occurrence with ⟨id, action⟩
          cases action <;>
            simp [Atom.IsRMW, Atom.isRMW,
              Atom.readValue] at rmwShape ⊢
    obtain ⟨readValue, readShape⟩ := rmwReads
    have sourceSpec :=
      valid.sourceSpec rmw readsFrom.2.1
    rw [readShape] at sourceSpec
    obtain ⟨chosen, chosenMember, chosenWrites,
        chosenId⟩ := sourceSpec
    have sameId : source.id = chosen.id :=
      Option.some.inj
        (readsFrom.2.2.symm.trans chosenId)
    have sameAtom :=
      atom_eq_of_id_eq valid readsFrom.1 chosenMember sameId
    subst chosen
    exact ⟨readValue, chosenWrites⟩
  · exact isWrite_of_isRMW rmwShape
  · exact valid.rmwAdjacent
      readsFrom.1 readsFrom.2.1 readsFrom.2.2 rmwShape

/-- Source atomic occurrences belong to the atom carrier exactly when their
trace event belongs to the candidate trace. -/
@[simp] theorem occurrence_mem_atoms_iff
    {candidate : Candidate α}
    {occurrence : AtomicOccurrence α} :
    Atom.occurrence occurrence ∈ candidate.atoms ↔
      TraceEvent.atomic occurrence ∈ candidate.trace := by
  constructor
  · intro member
    simp only [Candidate.atoms, List.mem_cons] at member
    rcases member with impossible | filtered
    · cases impossible
    · change
        Atom.occurrence occurrence ∈
          candidate.trace.filterMap atomOfTraceEvent? at filtered
      obtain ⟨event, eventMember, projects⟩ :=
        List.mem_filterMap.mp filtered
      cases event <;>
        simp [atomOfTraceEvent?] at projects
      next sourceOccurrence =>
        cases projects
        exact eventMember
  · intro eventMember
    simp only [Candidate.atoms, List.mem_cons]
    apply Or.inr
    change
      Atom.occurrence occurrence ∈
        candidate.trace.filterMap atomOfTraceEvent?
    exact List.mem_filterMap.mpr
      ⟨.atomic occurrence, eventMember,
        by simp [atomOfTraceEvent?]⟩

namespace Run

/--
A selected successful pop is either enabled by the starting local state or is
immediately preceded, in the same thread projection, by the matching
immutable-link read.
-/
theorem popSuccess_predecessor
    {thread : ThreadId}
    {initial final : LocalState α}
    {events leading suffix : List (TraceEvent α)}
    {id operation expected : Nat}
    {value : α}
    {next : Ptr}
    (run : Run thread initial events final)
    (shape :
      events =
        leading ++
          .atomic
            ⟨id,
              .popCas thread operation expected value next
                (.node expected) true⟩ ::
          suffix) :
    (leading = [] ∧
      initial =
        .popping operation expected value next) ∨
    ∃ earlier,
      leading =
        earlier ++
          [.readNext thread operation expected next] := by
  induction run generalizing leading with
  | nil state =>
      simp at shape
  | @cons initial middle final event rest first later
      inductionHypothesis =>
      cases leading with
      | nil =>
          simp only [List.nil_append] at shape
          have eventShape :
              event =
                .atomic
                  ⟨id,
                    .popCas thread operation expected value next
                      (.node expected) true⟩ :=
            (List.cons.inj shape).1
          subst event
          cases first
          exact Or.inl ⟨rfl, rfl⟩
      | cons leadingHead leadingTail =>
          simp only [List.cons_append] at shape
          have eventsMatch := List.cons.inj shape
          have restShape :
              rest =
                leadingTail ++
                  .atomic
                    ⟨id,
                      .popCas thread operation expected value next
                        (.node expected) true⟩ ::
                  suffix :=
            eventsMatch.2
          rcases inductionHypothesis restShape with
            startsReady | prior
          · rcases startsReady with
              ⟨leadingTailEmpty, middleReady⟩
            subst leadingTail
            subst middle
            have eventShape : event = leadingHead :=
              eventsMatch.1
            subst leadingHead
            cases first
            exact Or.inr ⟨[], by simp⟩
          · rcases prior with ⟨earlier, leadingTailShape⟩
            exact Or.inr
              ⟨leadingHead :: earlier,
                by simp [leadingTailShape]⟩

/-- An idle-started run always supplies the matching prior `readNext`. -/
theorem popSuccess_hasNextRead
    {thread : ThreadId}
    {final : LocalState α}
    {events leading suffix : List (TraceEvent α)}
    {id operation expected : Nat}
    {value : α}
    {next : Ptr}
    (run : Run thread .idle events final)
    (shape :
      events =
        leading ++
          .atomic
            ⟨id,
              .popCas thread operation expected value next
                (.node expected) true⟩ ::
          suffix) :
    ∃ earlier,
      leading =
        earlier ++
          [.readNext thread operation expected next] := by
  rcases popSuccess_predecessor run shape with
    startsReady | prior
  · cases startsReady.2
  · exact prior

end Run

/-- Thread projection distributes over global-trace concatenation. -/
theorem eventsForThread_append
    (thread : ThreadId)
    (first second : List (TraceEvent α)) :
    eventsForThread thread (first ++ second) =
      eventsForThread thread first ++
        eventsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, eventsForThread]
      split
      · simp [inductionHypothesis]
      · exact inductionHypothesis

/-- A projected thread event was present in the original global trace. -/
theorem mem_of_mem_eventsForThread
    {thread : ThreadId}
    {trace : List (TraceEvent α)}
    {event : TraceEvent α}
    (member : event ∈ eventsForThread thread trace) :
    event ∈ trace := by
  induction trace with
  | nil =>
      simp [eventsForThread] at member
  | cons first rest inductionHypothesis =>
      by_cases owned : first.thread = thread
      · simp only [eventsForThread, owned, if_true,
          List.mem_cons] at member
        exact member.elim
          (fun same => by simp [same])
          (fun inRest => by
            simp [inductionHypothesis inRest])
      · simp only [eventsForThread, owned, if_false] at member
        exact by simp [inductionHypothesis member]

namespace GlobalRun

/--
Every successful pop in a global run has the matching `readNext` in its strict
global prefix.  Interleaved events of other threads may occur between them.
-/
theorem popSuccess_hasNextRead
    {trace leading trailing : List (TraceEvent α)}
    {id thread operation expected : Nat}
    {value : α}
    {next : Ptr}
    (run : GlobalRun trace)
    (shape :
      trace =
        leading ++
          .atomic
            ⟨id,
              .popCas thread operation expected value next
                (.node expected) true⟩ ::
          trailing) :
    ∃ before after,
      leading =
        before ++
          .readNext thread operation expected next :: after := by
  obtain ⟨final, threadRun⟩ := run thread
  have projectedShape :
      eventsForThread thread trace =
        eventsForThread thread leading ++
          .atomic
            ⟨id,
              .popCas thread operation expected value next
                (.node expected) true⟩ ::
          eventsForThread thread trailing := by
    rw [shape, eventsForThread_append]
    simp [eventsForThread, TraceEvent.thread,
      AtomicAction.thread]
  obtain ⟨earlier, earlierShape⟩ :=
    Run.popSuccess_hasNextRead threadRun projectedShape
  have readMember :
      TraceEvent.readNext thread operation expected next ∈
        eventsForThread thread leading := by
    rw [earlierShape]
    simp
  have globalMember :
      TraceEvent.readNext thread operation expected next ∈
        leading :=
    mem_of_mem_eventsForThread readMember
  obtain ⟨before, after, leadingShape⟩ :=
    List.append_of_mem globalMember
  exact ⟨before, after, leadingShape⟩

end GlobalRun

/--
`publisher` is the successful push that permanently initialized `node` with
the immutable link `next`.
-/
def Publishes
    (candidate : Candidate α)
    (node : NodeId)
    (next : Ptr)
    (publisher : Atom α) : Prop :=
  ∃ id thread operation,
    publisher =
      .occurrence
        ⟨id,
          .pushCas thread operation node
            (candidate.payload node) next next true⟩

namespace Publishes

theorem writesNode
    {candidate : Candidate α}
    {node : NodeId}
    {next : Ptr}
    {publisher : Atom α}
    (publishes : Publishes candidate node next publisher) :
    publisher.writtenValue = some (.node node) := by
  obtain ⟨id, thread, operation, publisherShape⟩ :=
    publishes
  subst publisher
  rfl

theorem readsNext
    {candidate : Candidate α}
    {node : NodeId}
    {next : Ptr}
    {publisher : Atom α}
    (publishes : Publishes candidate node next publisher) :
    publisher.readValue = some next := by
  obtain ⟨id, thread, operation, publisherShape⟩ :=
    publishes
  subst publisher
  rfl

theorem isRMW
    {candidate : Candidate α}
    {node : NodeId}
    {next : Ptr}
    {publisher : Atom α}
    (publishes : Publishes candidate node next publisher) :
    publisher.IsRMW := by
  obtain ⟨id, thread, operation, publisherShape⟩ :=
    publishes
  subst publisher
  rfl

theorem functional
    {candidate : Candidate α}
    {node₁ node₂ : NodeId}
    {next₁ next₂ : Ptr}
    {publisher : Atom α}
    (first : Publishes candidate node₁ next₁ publisher)
    (second : Publishes candidate node₂ next₂ publisher) :
    node₁ = node₂ ∧ next₁ = next₂ := by
  obtain ⟨id₁, thread₁, operation₁, firstShape⟩ := first
  obtain ⟨id₂, thread₂, operation₂, secondShape⟩ := second
  rw [firstShape] at secondShape
  cases secondShape
  exact ⟨rfl, rfl⟩

end Publishes

/--
The source `readNext` immediately preceding a successful pop recovers the
successful push that published the popped node and its exact immutable link.
-/
theorem popSuccess_hasLinkPublisher
    (execution : SupportedExecution α)
    {id thread operation expected : Nat}
    {value : α}
    {next : Ptr}
    (writerMember :
      Atom.occurrence
          ⟨id,
            .popCas thread operation expected value next
              (.node expected) true⟩ ∈
        execution.candidate.atoms) :
    ∃ publisher,
      publisher ∈ execution.candidate.atoms ∧
        Publishes execution.candidate expected next publisher ∧
        OccursBefore publisher
          (.occurrence
            ⟨id,
              .popCas thread operation expected value next
                (.node expected) true⟩)
          execution.candidate.atoms := by
  have writerTraceMember :
      TraceEvent.atomic
          ⟨id,
            .popCas thread operation expected value next
              (.node expected) true⟩ ∈
        execution.candidate.trace :=
    occurrence_mem_atoms_iff.mp writerMember
  obtain ⟨leading, trailing, traceShape⟩ :=
    List.append_of_mem writerTraceMember
  obtain ⟨before, after, leadingShape⟩ :=
    GlobalRun.popSuccess_hasNextRead
      execution.client.globalRun traceShape
  have readShape :
      execution.candidate.trace =
        before ++
          .readNext thread operation expected next ::
            (after ++
              .atomic
                ⟨id,
                  .popCas thread operation expected value next
                    (.node expected) true⟩ ::
              trailing) := by
    rw [traceShape, leadingShape]
    simp [List.append_assoc]
  obtain ⟨publisherId, publisherThread, publisherOperation,
      publisherPrefixMember⟩ :=
    execution.client.immutableNextReads
      before
      (after ++
        .atomic
          ⟨id,
            .popCas thread operation expected value next
              (.node expected) true⟩ ::
        trailing)
      thread operation expected next readShape
  let publisher : Atom α :=
    .occurrence
      ⟨publisherId,
        .pushCas publisherThread publisherOperation expected
          (execution.candidate.payload expected)
          next next true⟩
  have publisherTraceMember :
      TraceEvent.atomic
          ⟨publisherId,
            .pushCas publisherThread publisherOperation expected
              (execution.candidate.payload expected)
              next next true⟩ ∈
        execution.candidate.trace := by
    rw [readShape]
    simp [publisherPrefixMember]
  obtain ⟨publisherBefore, publisherAfter,
      beforeShape⟩ :=
    List.append_of_mem publisherPrefixMember
  have publisherBeforePop :
      OccursBefore publisher
        (.occurrence
          ⟨id,
            .popCas thread operation expected value next
              (.node expected) true⟩)
        execution.candidate.atoms := by
    refine
      ⟨.initial ::
          publisherBefore.filterMap atomOfTraceEvent?,
        (publisherAfter ++
          [TraceEvent.readNext thread operation expected next] ++
          after).filterMap atomOfTraceEvent?,
        trailing.filterMap atomOfTraceEvent?, ?_⟩
    unfold Candidate.atoms Candidate.nonInitialAtoms
    rw [readShape, beforeShape]
    simp [publisher, atomOfTraceEvent?,
      List.filterMap_append, List.append_assoc]
  refine ⟨publisher, ?_, ?_, publisherBeforePop⟩
  · exact occurrence_mem_atoms_iff.mpr publisherTraceMember
  · exact ⟨publisherId, publisherThread,
      publisherOperation, rfl⟩

/-- Local control states that still belong to one in-flight push. -/
def PushActive
    (state : LocalState α)
    (operation : OperationId)
    (node : NodeId)
    (value : α) : Prop :=
  state = .pushLoading operation node value ∨
    ∃ expected,
      state = .pushWriting operation node value expected ∨
        state = .pushing operation node value expected

/-- Entering an active push either preserves an already-active push or is its
exact invocation step. -/
theorem LocalStep.pushActive_predecessor
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    {operation : OperationId}
    {node : NodeId}
    {value : α}
    (step : LocalStep thread before event after)
    (active : PushActive after operation node value) :
    PushActive before operation node value ∨
      event = .invokePush thread operation node value := by
  cases step <;>
    simp [PushActive] at active ⊢
  all_goals exact active

namespace Run

/-- A successful push is attached to its unique in-flight invocation unless
the supplied run suffix already starts inside that invocation. -/
theorem pushSuccess_active_or_invoked
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
    PushActive initial operation node value ∨
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
        exact Or.inl
          (by simp [PushActive])
      · rcases inductionHypothesis inRest with
          middleActive | invokedLater
        · rcases
            WeakMemory.TreiberC11V1.GenerationFrontend.LocalStep.pushActive_predecessor
              first middleActive with
            initialActive | isInvocation
          · exact Or.inl initialActive
          · exact Or.inr (by simp [isInvocation])
        · exact Or.inr (by simp [invokedLater])

end Run

/-- Every successful push in an idle-started global run has its exact push
invocation in the global trace. -/
theorem GlobalRun.pushSuccess_hasInvocation
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
  rcases Run.pushSuccess_active_or_invoked
      localRun projectedMember with active | invoked
  · simp [PushActive] at active
  · exact mem_of_mem_eventsForThread invoked

/-- Functional uniqueness of the successful push that publishes a node. -/
def PublisherUnique
    (execution : SupportedExecution α) : Prop :=
  ∀ {node next₁ next₂ publisher₁ publisher₂},
    publisher₁ ∈ execution.candidate.atoms →
      publisher₂ ∈ execution.candidate.atoms →
      Publishes execution.candidate node next₁ publisher₁ →
      Publishes execution.candidate node next₂ publisher₂ →
      publisher₁ = publisher₂

/-- The independent source contract derives publisher functionality. -/
theorem publisherUnique
    (execution : SupportedExecution α) :
    PublisherUnique execution := by
  intro node next₁ next₂ publisher₁ publisher₂
      publisher₁Member publisher₂Member
      publishes₁ publishes₂
  obtain ⟨id₁, thread₁, operation₁, publisher₁Shape⟩ :=
    publishes₁
  obtain ⟨id₂, thread₂, operation₂, publisher₂Shape⟩ :=
    publishes₂
  subst publisher₁
  subst publisher₂
  exact
    PushUniqueness.SupportedExecution.successfulPush_unique
      execution publisher₁Member publisher₂Member

/-- Origin data recovered for one write of a non-null head value. -/
def NodeOrigin
    (execution : SupportedExecution α)
    (node : NodeId)
    (writer : Atom α) : Prop :=
  ∃ next publisher,
    publisher ∈ execution.candidate.atoms ∧
      Publishes execution.candidate node next publisher ∧
      (publisher = writer ∨
        MO execution.candidate publisher writer)

/-- Read-source lookup with its exact value equation. -/
theorem rfSource
    (execution : SupportedExecution α)
    {target : Atom α}
    (targetMember :
      target ∈ execution.candidate.atoms)
    {value : Ptr}
    (readsValue :
      target.readValue = some value) :
    ∃ source,
      RF execution.candidate source target ∧
        source.writtenValue = some value := by
  have sourceSpec :=
    execution.rc11.sourceSpec target targetMember
  rw [readsValue] at sourceSpec
  obtain ⟨source, sourceMember, sourceWrites,
      sourceChosen⟩ := sourceSpec
  exact
    ⟨source,
      ⟨sourceMember, targetMember, sourceChosen⟩,
      sourceWrites⟩

/--
Assuming publisher functionality, every non-null write has that publisher as
its own atom or strictly earlier in modification order.

`publisher_unique` is discharged from the source contract below; it is exposed
separately because the well-founded modification-order argument is useful on
its own.
-/
theorem nodeOrigin_of_publisherUnique
    (execution : SupportedExecution α)
    (publisherUnique : PublisherUnique execution)
    {node : NodeId}
    {writer : Atom α}
    (writerMember :
      writer ∈ execution.candidate.atoms)
    (writesNode :
      writer.writtenValue = some (.node node)) :
    NodeOrigin execution node writer := by
  generalize rankShape :
      execution.candidate.writeOrder.idxOf writer.id =
        writerRank
  induction writerRank using Nat.strongRecOn
      generalizing writer node with
  | ind writerRank inductionHypothesis =>
      cases writer with
      | initial =>
          simp [Atom.writtenValue] at writesNode
      | occurrence sourceOccurrence =>
          rcases sourceOccurrence with ⟨writerId, action⟩
          cases action with
          | pushLoad =>
              simp [Atom.writtenValue,
                AtomicAction.writtenValue] at writesNode
          | pushCas thread operation allocated value expected observed
              succeeded =>
              cases succeeded with
              | false =>
                  simp [Atom.writtenValue,
                    AtomicAction.writtenValue] at writesNode
              | true =>
                  simp only [Atom.writtenValue,
                    AtomicAction.writtenValue,
                    Option.some.injEq, Ptr.node.injEq] at writesNode
                  subst allocated
                  have successfulRead :=
                    execution.atom_successfulReadConsistent
                      (.occurrence
                        ⟨writerId,
                          .pushCas thread operation node value
                            expected observed true⟩)
                      writerMember
                  simp [RC11.Atom.SuccessfulReadConsistent,
                    AtomicAction.SuccessfulReadConsistent] at successfulRead
                  subst observed
                  have writerTraceMember :
                      TraceEvent.atomic
                          ⟨writerId,
                            .pushCas thread operation node value
                              expected expected true⟩ ∈
                        execution.candidate.trace :=
                    occurrence_mem_atoms_iff.mp writerMember
                  have payloadShape :
                      value = execution.candidate.payload node := by
                    simpa [TracePayloadConsistent,
                      AtomicPayloadConsistent] using
                      execution.rc11.payloadConsistent _
                        writerTraceMember
                  subst value
                  exact
                    ⟨expected,
                      .occurrence
                        ⟨writerId,
                          .pushCas thread operation node
                            (execution.candidate.payload node)
                            expected expected true⟩,
                      writerMember,
                      ⟨writerId, thread, operation, rfl⟩,
                      Or.inl rfl⟩
          | popLoad =>
              simp [Atom.writtenValue,
                AtomicAction.writtenValue] at writesNode
          | popCas thread operation popped value next observed
              succeeded =>
              cases succeeded with
              | false =>
                  simp [Atom.writtenValue,
                    AtomicAction.writtenValue] at writesNode
              | true =>
                  simp only [Atom.writtenValue,
                    AtomicAction.writtenValue,
                    Option.some.injEq] at writesNode
                  have successfulRead :=
                    execution.atom_successfulReadConsistent
                      (.occurrence
                        ⟨writerId,
                          .popCas thread operation popped value next
                            observed true⟩)
                      writerMember
                  simp [RC11.Atom.SuccessfulReadConsistent,
                    AtomicAction.SuccessfulReadConsistent] at successfulRead
                  subst observed
                  subst next
                  obtain ⟨poppedPublisher, poppedPublisherMember,
                      poppedPublishes, _⟩ :=
                    popSuccess_hasLinkPublisher execution writerMember
                  obtain ⟨source, sourceReadsFrom,
                      sourceWritesPopped⟩ :=
                    rfSource execution writerMember
                      (value := .node popped) rfl
                  have sourceImmediateWriter :=
                    immediate_of_rmw_rf execution.rc11
                      sourceReadsFrom (by rfl)
                  have sourceBeforeWriter :=
                    mo_of_immediate sourceImmediateWriter
                  have sourceRankLt :
                      execution.candidate.writeOrder.idxOf source.id <
                        writerRank := by
                    rw [← rankShape]
                    exact sourceBeforeWriter.2.2.2.2
                  have poppedOrigin :=
                    inductionHypothesis
                      (execution.candidate.writeOrder.idxOf source.id)
                      sourceRankLt
                      (node := popped)
                      (writer := source)
                      sourceReadsFrom.1
                      sourceWritesPopped
                      rfl
                  obtain
                      ⟨poppedOriginNext, poppedOriginPublisher,
                        poppedOriginMember, poppedOriginPublishes,
                        poppedOriginOrder⟩ :=
                    poppedOrigin
                  have samePoppedPublisher :
                      poppedPublisher =
                        poppedOriginPublisher :=
                    publisherUnique
                      poppedPublisherMember
                      poppedOriginMember
                      poppedPublishes
                      poppedOriginPublishes
                  have poppedPublisherBeforeWriter :
                      MO execution.candidate poppedPublisher
                        (.occurrence
                          ⟨writerId,
                            .popCas thread operation popped value
                              (.node node) (.node popped) true⟩) := by
                    rcases poppedOriginOrder with
                      publisherIsSource | publisherBeforeSource
                    · rw [samePoppedPublisher,
                        publisherIsSource]
                      exact sourceBeforeWriter
                    · rw [samePoppedPublisher]
                      exact mo_transitive publisherBeforeSource
                        sourceBeforeWriter
                  have poppedPublisherReadsNode :
                      poppedPublisher.readValue =
                        some (.node node) :=
                    poppedPublishes.readsNext
                  obtain ⟨earlierWriter, earlierReadsFrom,
                      earlierWritesNode⟩ :=
                    rfSource execution poppedPublisherMember
                      poppedPublisherReadsNode
                  have earlierImmediatePublisher :=
                    immediate_of_rmw_rf execution.rc11
                      earlierReadsFrom poppedPublishes.isRMW
                  have earlierBeforePublisher :=
                    mo_of_immediate earlierImmediatePublisher
                  have earlierBeforeWriter :=
                    mo_transitive earlierBeforePublisher
                      poppedPublisherBeforeWriter
                  have earlierRankLt :
                      execution.candidate.writeOrder.idxOf
                          earlierWriter.id <
                        writerRank := by
                    rw [← rankShape]
                    exact earlierBeforeWriter.2.2.2.2
                  have nodeOrigin :=
                    inductionHypothesis
                      (execution.candidate.writeOrder.idxOf
                        earlierWriter.id)
                      earlierRankLt
                      (node := node)
                      (writer := earlierWriter)
                      earlierReadsFrom.1
                      earlierWritesNode
                      rfl
                  obtain
                      ⟨originNext, originPublisher,
                        originPublisherMember, originPublishes,
                        originOrder⟩ :=
                    nodeOrigin
                  refine
                    ⟨originNext, originPublisher,
                      originPublisherMember, originPublishes, ?_⟩
                  exact Or.inr <|
                    originOrder.elim
                      (fun publisherIsEarlier => by
                        rw [publisherIsEarlier]
                        exact earlierBeforeWriter)
                      (fun publisherBeforeEarlier =>
                        mo_transitive publisherBeforeEarlier
                          earlierBeforeWriter)
          | isEmptyLoad =>
              simp [Atom.writtenValue,
                AtomicAction.writtenValue] at writesNode

/--
The exact immutable-link publisher of a successful pop reaches that pop in
independent extended coherence.
-/
theorem successfulPop_publication_of_publisherUnique
    (execution : SupportedExecution α)
    (publisherUnique : PublisherUnique execution)
    {id thread operation node : Nat}
    {value : α}
    {next : Ptr}
    (popMember :
      Atom.occurrence
          ⟨id,
            .popCas thread operation node value next
              (.node node) true⟩ ∈
        execution.candidate.atoms) :
    ∃ publisher,
      publisher ∈ execution.candidate.atoms ∧
        Publishes execution.candidate node next publisher ∧
        ECO execution.candidate publisher
          (.occurrence
            ⟨id,
              .popCas thread operation node value next
                (.node node) true⟩) := by
  obtain ⟨publisher, publisherMember, publishes, _⟩ :=
    popSuccess_hasLinkPublisher execution popMember
  obtain ⟨source, readsFrom, sourceWritesNode⟩ :=
    rfSource execution popMember
      (value := .node node) rfl
  obtain ⟨originNext, originPublisher,
      originPublisherMember, originPublishes,
      originOrder⟩ :=
    nodeOrigin_of_publisherUnique execution publisherUnique
      readsFrom.1 sourceWritesNode
  have samePublisher : publisher = originPublisher :=
    publisherUnique publisherMember originPublisherMember
      publishes originPublishes
  refine ⟨publisher, publisherMember, publishes, ?_⟩
  rw [samePublisher]
  rcases originOrder with isSource | beforeSource
  · rw [isSource]
    exact .readsFrom readsFrom
  · exact .transitive
      (.modificationOrder beforeSource)
      (.readsFrom readsFrom)

/--
Premise-free finite-MO node origin for the independent supported execution.
-/
theorem nodeOrigin
    (execution : SupportedExecution α)
    {node : NodeId}
    {writer : Atom α}
    (writerMember :
      writer ∈ execution.candidate.atoms)
    (writesNode :
      writer.writtenValue = some (.node node)) :
    NodeOrigin execution node writer :=
  nodeOrigin_of_publisherUnique execution
    (publisherUnique execution) writerMember writesNode

/-- Premise-free exact publication edge for every successful pop. -/
theorem successfulPop_publication
    (execution : SupportedExecution α)
    {id thread operation node : Nat}
    {value : α}
    {next : Ptr}
    (popMember :
      Atom.occurrence
          ⟨id,
            .popCas thread operation node value next
              (.node node) true⟩ ∈
        execution.candidate.atoms) :
    ∃ publisher,
      publisher ∈ execution.candidate.atoms ∧
        Publishes execution.candidate node next publisher ∧
        ECO execution.candidate publisher
          (.occurrence
            ⟨id,
              .popCas thread operation node value next
                (.node node) true⟩) :=
  successfulPop_publication_of_publisherUnique execution
    (publisherUnique execution) popMember

/-! ## Chronological allocator construction -/

private theorem nodup_of_map_nodup
    {items : List β}
    {project : β → γ}
    (mappedNodup : (items.map project).Nodup) :
    items.Nodup := by
  induction items with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headInTail
        exact parts.1
          (List.mem_map.mpr
            ⟨head, headInTail, rfl⟩)
      · exact inductionHypothesis parts.2

private inductive PrefixPrecedes
    (first second : β) : List β → Prop where
  | here {tail} :
      second ∈ tail →
      PrefixPrecedes first second (first :: tail)
  | there {head tail} :
      PrefixPrecedes first second tail →
      PrefixPrecedes first second (head :: tail)

private theorem PrefixPrecedes.second_mem
    {first second : β}
    {items : List β}
    (precedes : PrefixPrecedes first second items) :
    second ∈ items := by
  induction precedes with
  | here member =>
      simp [member]
  | there later inductionHypothesis =>
      simp [inductionHypothesis]

private theorem PrefixPrecedes.of_occursBefore
    {first second : β}
    {items : List β}
    (before : OccursBefore first second items) :
    PrefixPrecedes first second items := by
  obtain ⟨earlier, between, trailing, shape⟩ := before
  subst items
  induction earlier with
  | nil =>
      simp only [List.nil_append]
      exact .here (by simp)
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]
      exact .there inductionHypothesis

private theorem PrefixPrecedes.first_mem_prefix
    {first second : β}
    {processed suffix : List β}
    (noDuplicates :
      (processed ++ second :: suffix).Nodup)
    (precedes :
      PrefixPrecedes first second
        (processed ++ second :: suffix)) :
    first ∈ processed := by
  induction processed with
  | nil =>
      simp only [List.nil_append] at noDuplicates precedes
      have secondNotInSuffix :=
        (List.nodup_cons.mp noDuplicates).1
      cases precedes with
      | here secondInSuffix =>
          exact (secondNotInSuffix secondInSuffix).elim
      | there later =>
          exact
            (secondNotInSuffix later.second_mem).elim
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append] at noDuplicates precedes ⊢
      cases precedes with
      | here =>
          simp
      | there later =>
          exact List.mem_cons_of_mem head
            (inductionHypothesis
              (List.nodup_cons.mp noDuplicates).2 later)

private theorem publisher_mem_processed
    (execution : SupportedExecution α)
    {processed suffix : List (Atom α)}
    {publisher pop : Atom α}
    (carrierShape :
      execution.candidate.atoms =
        processed ++ pop :: suffix)
    (before :
      OccursBefore publisher pop
        execution.candidate.atoms) :
    publisher ∈ processed := by
  have carrierNodup :
      execution.candidate.atoms.Nodup :=
    nodup_of_map_nodup execution.rc11.atomIdsNodup
  rw [carrierShape] at carrierNodup before
  exact
    (PrefixPrecedes.of_occursBefore before)
      |>.first_mem_prefix carrierNodup

/--
The partial allocator records exactly the successful publishers already
processed in an atom prefix.
-/
structure AllocatorMatches
    (execution : SupportedExecution α)
    (processed : List (Atom α))
    (allocator : TreiberRC11.AllocatorTable α) : Prop where
  processedAtoms :
    ∀ {atom}, atom ∈ processed →
      atom ∈ execution.candidate.atoms
  records :
    ∀ {node next publisher},
      publisher ∈ processed →
        Publishes execution.candidate node next publisher →
        allocator node =
          some
            (publisher.toTarget,
              { value := execution.candidate.payload node,
                next := next.toTarget })
  sound :
    ∀ {node event record},
      allocator node = some (event, record) →
        ∃ next publisher,
          publisher ∈ processed ∧
            Publishes execution.candidate node next publisher ∧
            event = publisher.toTarget ∧
            record =
              { value := execution.candidate.payload node,
                next := next.toTarget }

theorem AllocatorMatches.empty
    (execution : SupportedExecution α) :
    AllocatorMatches execution []
      (TreiberRC11.AllocatorTable.empty :
        TreiberRC11.AllocatorTable α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    simp at member
  · intro node next publisher member
    simp at member
  · intro node event record allocation
    simp [TreiberRC11.AllocatorTable.empty] at allocation

/--
Inserting a fresh publisher preserves exact prefix/allocator agreement.
-/
theorem AllocatorMatches.insert
    (execution : SupportedExecution α)
    {processed : List (Atom α)}
    {allocator : TreiberRC11.AllocatorTable α}
    (agreement : AllocatorMatches execution processed allocator)
    {node : NodeId}
    {next : Ptr}
    {publisher : Atom α}
    (publisherMember :
      publisher ∈ execution.candidate.atoms)
    (publisherNotProcessed :
      publisher ∉ processed)
    (publishes :
      Publishes execution.candidate node next publisher) :
    allocator node = none ∧
      AllocatorMatches execution (processed ++ [publisher])
        (TreiberRC11.AllocatorTable.insert allocator node
          publisher.toTarget
          { value := execution.candidate.payload node,
            next := next.toTarget }) := by
  have unused : allocator node = none := by
    cases allocation : allocator node with
    | none =>
        rfl
    | some record =>
        obtain ⟨event, stored⟩ := record
        obtain ⟨oldNext, oldPublisher, oldMember,
            oldPublishes, eventShape, storedShape⟩ :=
          agreement.sound allocation
        have samePublisher : oldPublisher = publisher :=
          publisherUnique execution
            (agreement.processedAtoms oldMember)
            publisherMember
            oldPublishes publishes
        exact (publisherNotProcessed
          (samePublisher ▸ oldMember)).elim
  refine ⟨unused, ?_⟩
  let newAllocator :=
    TreiberRC11.AllocatorTable.insert allocator node
      publisher.toTarget
      { value := execution.candidate.payload node,
        next := next.toTarget }
  refine {
    processedAtoms := ?_
    records := ?_
    sound := ?_
  }
  · intro atom member
    simp only [List.mem_append, List.mem_singleton] at member
    exact member.elim agreement.processedAtoms
      (fun same => same ▸ publisherMember)
  · intro query queryNext queryPublisher queryMember
      queryPublishes
    simp only [List.mem_append, List.mem_singleton] at queryMember
    rcases queryMember with oldMember | isCurrent
    · exact
        TreiberRC11.AllocatorTable.insert_extends
          allocator node publisher.toTarget
          { value := execution.candidate.payload node,
            next := next.toTarget }
          unused
          (agreement.records oldMember queryPublishes)
    · subst queryPublisher
      have shapes := publishes.functional queryPublishes
      obtain ⟨queryShape, nextShape⟩ := shapes
      subst query
      subst queryNext
      exact TreiberRC11.AllocatorTable.insert_same
        allocator node publisher.toTarget
          { value := execution.candidate.payload node,
            next := next.toTarget }
  · intro query event record allocation
    by_cases sameNode : query = node
    · subst query
      rw [TreiberRC11.AllocatorTable.insert_same] at allocation
      have pairShape := Option.some.inj allocation
      cases pairShape
      exact
        ⟨next, publisher, by simp, publishes, rfl, rfl⟩
    · rw [TreiberRC11.AllocatorTable.insert_other
          allocator node query publisher.toTarget
          { value := execution.candidate.payload node,
            next := next.toTarget }
          sameNode] at allocation
      obtain ⟨oldNext, oldPublisher, oldMember,
          oldPublishes, eventShape, recordShape⟩ :=
        agreement.sound allocation
      exact
        ⟨oldNext, oldPublisher, by simp [oldMember],
          oldPublishes, eventShape, recordShape⟩

/-- A non-publisher atom leaves the allocator unchanged. -/
theorem AllocatorMatches.skip
    (execution : SupportedExecution α)
    {processed : List (Atom α)}
    {allocator : TreiberRC11.AllocatorTable α}
    (agreement : AllocatorMatches execution processed allocator)
    {atom : Atom α}
    (atomMember :
      atom ∈ execution.candidate.atoms)
    (notPublisher :
      ∀ node next,
        ¬ Publishes execution.candidate node next atom) :
    AllocatorMatches execution (processed ++ [atom]) allocator := by
  refine {
    processedAtoms := ?_
    records := ?_
    sound := ?_
  }
  · intro candidate member
    simp only [List.mem_append, List.mem_singleton] at member
    exact member.elim agreement.processedAtoms
      (fun same => same ▸ atomMember)
  · intro node next publisher member publishes
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with oldMember | isCurrent
    · exact agreement.records oldMember publishes
    · subst publisher
      exact (notPublisher node next publishes).elim
  · intro node event record allocation
    obtain ⟨next, publisher, publisherMember,
        publishes, eventShape, recordShape⟩ :=
      agreement.sound allocation
    exact
      ⟨next, publisher, by simp [publisherMember],
        publishes, eventShape, recordShape⟩

private theorem next_not_mem_processed
    (execution : SupportedExecution α)
    {processed suffix : List (Atom α)}
    {next : Atom α}
    (carrierShape :
      execution.candidate.atoms =
        processed ++ next :: suffix) :
    next ∉ processed := by
  have carrierNodup :
      execution.candidate.atoms.Nodup :=
    nodup_of_map_nodup execution.rc11.atomIdsNodup
  rw [carrierShape] at carrierNodup
  have parts := List.nodup_append.mp carrierNodup
  intro member
  exact
    (parts.2.2 next member next (by simp)) rfl

/--
Extend a generated atom prefix across the remaining independent carrier in
source chronology.
-/
theorem generated_suffix
    (execution : SupportedExecution α)
    {processed remaining : List (Atom α)}
    {allocator : TreiberRC11.AllocatorTable α}
    (carrierShape :
      execution.candidate.atoms =
        processed ++ remaining)
    (generated :
      TreiberRC11.GeneratedEvents execution.relationData.graph
        (TreiberRC11.ModelInitial.initialized :
          TreiberRA.State α)
        allocator
        (processed.map RC11.Atom.toTarget))
    (agreement :
      AllocatorMatches execution processed allocator) :
    ∃ finalAllocator,
      TreiberRC11.GeneratedEvents execution.relationData.graph
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          finalAllocator
          (execution.candidate.atoms.map RC11.Atom.toTarget) ∧
        AllocatorMatches execution execution.candidate.atoms
          finalAllocator := by
  induction remaining generalizing processed allocator with
  | nil =>
      have processedShape :
          execution.candidate.atoms = processed := by
        simpa using carrierShape
      refine ⟨allocator, ?_, ?_⟩
      · simpa [processedShape] using generated
      · simpa [processedShape] using agreement
  | cons atom rest inductionHypothesis =>
      have atomMember :
          atom ∈ execution.candidate.atoms := by
        rw [carrierShape]
        simp
      have atomNotProcessed :
          atom ∉ processed :=
        next_not_mem_processed execution carrierShape
      have nextCarrierShape :
          execution.candidate.atoms =
            (processed ++ [atom]) ++ rest := by
        simpa [List.append_assoc] using carrierShape
      cases atom with
      | initial =>
          have nextAgreement :=
            agreement.skip execution atomMember
              (by
                intro node next
                simp [Publishes])
          have nextGenerated :
              TreiberRC11.GeneratedEvents
                execution.relationData.graph
                (TreiberRC11.ModelInitial.initialized :
                  TreiberRA.State α)
                allocator
                ((processed ++
                  [(.initial : Atom α)]).map
                    RC11.Atom.toTarget) := by
            simpa [RC11.Atom.toTarget,
              TreiberRC11.EventGraph.Skeleton.initialEvent] using
              TreiberRC11.GeneratedEvents.initializer
                generated 0
          exact inductionHypothesis nextCarrierShape
            nextGenerated nextAgreement
      | occurrence sourceOccurrence =>
          rcases sourceOccurrence with ⟨id, action⟩
          cases action with
          | pushLoad thread operation observed =>
              have nextAgreement :=
                agreement.skip execution atomMember
                  (by
                    intro node next
                    simp [Publishes])
              have nextGenerated :
                  TreiberRC11.GeneratedEvents
                    execution.relationData.graph
                    (TreiberRC11.ModelInitial.initialized :
                      TreiberRA.State α)
                    allocator
                    ((processed ++
                      [RC11.Atom.occurrence
                        ⟨id,
                          .pushLoad thread operation observed⟩]).map
                        RC11.Atom.toTarget) := by
                simpa [RC11.Atom.toTarget,
                  AtomicAction.toTarget] using
                  TreiberRC11.GeneratedEvents.pushLoad
                    generated id thread observed.toTarget
              exact inductionHypothesis nextCarrierShape
                nextGenerated nextAgreement
          | pushCas thread operation node value expected observed
              succeeded =>
              cases succeeded with
              | false =>
                  have nextAgreement :=
                    agreement.skip execution atomMember
                      (by
                        intro query next
                        simp [Publishes])
                  have nextGenerated :
                      TreiberRC11.GeneratedEvents
                        execution.relationData.graph
                        (TreiberRC11.ModelInitial.initialized :
                          TreiberRA.State α)
                        allocator
                        ((processed ++
                          [RC11.Atom.occurrence
                            ⟨id,
                              .pushCas thread operation node value
                                expected observed false⟩]).map
                            RC11.Atom.toTarget) := by
                    simpa [RC11.Atom.toTarget,
                      AtomicAction.toTarget] using
                      TreiberRC11.GeneratedEvents.pushFailure
                        generated id thread node value
                          expected.toTarget observed.toTarget
                  exact inductionHypothesis nextCarrierShape
                    nextGenerated nextAgreement
              | true =>
                  have successfulRead :=
                    execution.atom_successfulReadConsistent
                      (.occurrence
                        ⟨id,
                          .pushCas thread operation node value
                            expected observed true⟩)
                      atomMember
                  simp [RC11.Atom.SuccessfulReadConsistent,
                    AtomicAction.SuccessfulReadConsistent] at successfulRead
                  subst observed
                  have traceMember :
                      TraceEvent.atomic
                          ⟨id,
                            .pushCas thread operation node value
                              expected expected true⟩ ∈
                        execution.candidate.trace :=
                    occurrence_mem_atoms_iff.mp atomMember
                  have payloadShape :
                      value = execution.candidate.payload node := by
                    simpa [TracePayloadConsistent,
                      AtomicPayloadConsistent] using
                      execution.rc11.payloadConsistent _ traceMember
                  subst value
                  have publishes :
                      Publishes execution.candidate node expected
                        (.occurrence
                          ⟨id,
                            .pushCas thread operation node
                              (execution.candidate.payload node)
                              expected expected true⟩) :=
                    ⟨id, thread, operation, rfl⟩
                  obtain ⟨unused, nextAgreement⟩ :=
                    agreement.insert execution atomMember
                      atomNotProcessed publishes
                  let nextAllocator :=
                    TreiberRC11.AllocatorTable.insert allocator node
                      (RC11.Atom.occurrence
                        ⟨id,
                          .pushCas thread operation node
                            (execution.candidate.payload node)
                            expected expected true⟩).toTarget
                      { value := execution.candidate.payload node,
                        next := expected.toTarget }
                  have nextGenerated :
                      TreiberRC11.GeneratedEvents
                        execution.relationData.graph
                        (TreiberRC11.ModelInitial.initialized :
                          TreiberRA.State α)
                        nextAllocator
                        ((processed ++
                          [RC11.Atom.occurrence
                            ⟨id,
                              .pushCas thread operation node
                                (execution.candidate.payload node)
                                expected expected true⟩]).map
                            RC11.Atom.toTarget) := by
                    simpa [nextAllocator, RC11.Atom.toTarget,
                      AtomicAction.toTarget] using
                      TreiberRC11.GeneratedEvents.pushSuccess
                        generated id thread node
                          (execution.candidate.payload node)
                          expected.toTarget
                          (TreiberRC11.ModelInitial.initialized_heap node)
                          unused
                  exact inductionHypothesis nextCarrierShape
                    nextGenerated nextAgreement
          | popLoad thread operation observed =>
              have nextAgreement :=
                agreement.skip execution atomMember
                  (by
                    intro node next
                    simp [Publishes])
              have nextGenerated :
                  TreiberRC11.GeneratedEvents
                    execution.relationData.graph
                    (TreiberRC11.ModelInitial.initialized :
                      TreiberRA.State α)
                    allocator
                    ((processed ++
                      [RC11.Atom.occurrence
                        ⟨id,
                          .popLoad thread operation observed⟩]).map
                        RC11.Atom.toTarget) := by
                simpa [RC11.Atom.toTarget,
                  AtomicAction.toTarget] using
                  TreiberRC11.GeneratedEvents.popLoad
                    generated id thread observed.toTarget
              exact inductionHypothesis nextCarrierShape
                nextGenerated nextAgreement
          | popCas thread operation node value next observed
              succeeded =>
              cases succeeded with
              | false =>
                  have nextAgreement :=
                    agreement.skip execution atomMember
                      (by
                        intro query link
                        simp [Publishes])
                  have nextGenerated :
                      TreiberRC11.GeneratedEvents
                        execution.relationData.graph
                        (TreiberRC11.ModelInitial.initialized :
                          TreiberRA.State α)
                        allocator
                        ((processed ++
                          [RC11.Atom.occurrence
                            ⟨id,
                              .popCas thread operation node value next
                                observed false⟩]).map
                            RC11.Atom.toTarget) := by
                    simpa [RC11.Atom.toTarget,
                      AtomicAction.toTarget] using
                      TreiberRC11.GeneratedEvents.popFailure
                        generated id thread (some node)
                          observed.toTarget
                  exact inductionHypothesis nextCarrierShape
                    nextGenerated nextAgreement
              | true =>
                  have successfulRead :=
                    execution.atom_successfulReadConsistent
                      (.occurrence
                        ⟨id,
                          .popCas thread operation node value next
                            observed true⟩)
                      atomMember
                  simp [RC11.Atom.SuccessfulReadConsistent,
                    AtomicAction.SuccessfulReadConsistent] at successfulRead
                  subst observed
                  have traceMember :
                      TraceEvent.atomic
                          ⟨id,
                            .popCas thread operation node value next
                              (.node node) true⟩ ∈
                        execution.candidate.trace :=
                    occurrence_mem_atoms_iff.mp atomMember
                  have payloadShape :
                      value = execution.candidate.payload node := by
                    simpa [TracePayloadConsistent,
                      AtomicPayloadConsistent] using
                      execution.rc11.payloadConsistent _ traceMember
                  subst value
                  obtain ⟨publisher, publisherMember, publishes,
                      publisherBefore⟩ :=
                    popSuccess_hasLinkPublisher execution atomMember
                  have publisherProcessed :
                      publisher ∈ processed :=
                    publisher_mem_processed execution carrierShape
                      publisherBefore
                  have recorded :=
                    agreement.records publisherProcessed publishes
                  obtain ⟨edgePublisher, edgePublisherMember,
                      edgePublishes, edge⟩ :=
                    successfulPop_publication execution atomMember
                  have samePublisher :
                      publisher = edgePublisher :=
                    publisherUnique execution publisherMember
                      edgePublisherMember publishes edgePublishes
                  have independentPublication :
                      ECO execution.candidate publisher
                        (.occurrence
                          ⟨id,
                            .popCas thread operation node
                              (execution.candidate.payload node) next
                              (.node node) true⟩) := by
                    rw [samePublisher]
                    exact edge
                  have targetPublication :
                      execution.relationData.graph.ExtendedCoherence
                        publisher.toTarget
                        (RC11.Atom.occurrence
                          ⟨id,
                            .popCas thread operation node
                              (execution.candidate.payload node) next
                              (.node node) true⟩).toTarget :=
                    (execution.relationData_extendedCoherence_iff
                      publisherMember atomMember).mpr
                        independentPublication
                  have nextAgreement :=
                    agreement.skip execution atomMember
                      (by
                        intro query link
                        simp [Publishes])
                  have nextGenerated :
                      TreiberRC11.GeneratedEvents
                        execution.relationData.graph
                        (TreiberRC11.ModelInitial.initialized :
                          TreiberRA.State α)
                        allocator
                        ((processed ++
                          [RC11.Atom.occurrence
                            ⟨id,
                              .popCas thread operation node
                                (execution.candidate.payload node) next
                                (.node node) true⟩]).map
                            RC11.Atom.toTarget) := by
                    simpa [RC11.Atom.toTarget,
                      AtomicAction.toTarget] using
                      TreiberRC11.GeneratedEvents.popSuccess
                        generated id thread node
                          (execution.candidate.payload node)
                          next.toTarget publisher.toTarget
                          recorded targetPublication
                  exact inductionHypothesis nextCarrierShape
                    nextGenerated nextAgreement
          | isEmptyLoad thread operation observed =>
              have nextAgreement :=
                agreement.skip execution atomMember
                  (by
                    intro node next
                    simp [Publishes])
              have nextGenerated :
                  TreiberRC11.GeneratedEvents
                    execution.relationData.graph
                    (TreiberRC11.ModelInitial.initialized :
                      TreiberRA.State α)
                    allocator
                    ((processed ++
                      [RC11.Atom.occurrence
                        ⟨id,
                          .isEmptyLoad thread operation observed⟩]).map
                        RC11.Atom.toTarget) := by
                simpa [RC11.Atom.toTarget,
                  AtomicAction.toTarget] using
                  TreiberRC11.GeneratedEvents.isEmptyLoad
                    generated id thread observed.toTarget
              exact inductionHypothesis nextCarrierShape
                nextGenerated nextAgreement

/-- The exact source chronology admits a generated target allocator. -/
theorem generation_exists
    (execution : SupportedExecution α) :
    ∃ allocator,
      TreiberRC11.GeneratedEvents execution.relationData.graph
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          allocator
          execution.toControlledSource.skeleton.events ∧
        AllocatorMatches execution execution.candidate.atoms
          allocator := by
  obtain ⟨allocator, generated, agreement⟩ :=
    generated_suffix execution
      (processed := [])
      (remaining := execution.candidate.atoms)
      (allocator := TreiberRC11.AllocatorTable.empty)
      (by simp)
      (TreiberRC11.GeneratedEvents.nil)
      (AllocatorMatches.empty execution)
  rw [execution.atoms_toTarget_eq_events] at generated
  exact ⟨allocator, generated, agreement⟩

/-- Constructive output package consumed by the integration frontend. -/
structure GenerationResult
    (execution : SupportedExecution α) where
  allocator :
    TreiberRC11.AllocatorTable α
  generated :
    TreiberRC11.GeneratedEvents execution.relationData.graph
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α)
      allocator
      execution.toControlledSource.skeleton.events
  allocatorMatches :
    AllocatorMatches execution execution.candidate.atoms
      allocator

/-- Canonical no-premise generation result. -/
noncomputable def generationResult
    (execution : SupportedExecution α) :
    GenerationResult execution := by
  classical
  let existence := generation_exists execution
  exact {
    allocator := Classical.choose existence
    generated := (Classical.choose_spec existence).1
    allocatorMatches := (Classical.choose_spec existence).2
  }

namespace GenerationResult

/-- Package the generated allocator with the exact source, relations, and
derived common-rank witness. -/
def toSourceAtomicExecution
    [DecidableEq α]
    {execution : SupportedExecution α}
    (result : GenerationResult execution) :
    TreiberRC11.SourceAtomicExecution
      (TreiberRC11.ModelInitial.initialized :
        TreiberRA.State α) where
  source :=
    execution.toControlledSource
  relations :=
    execution.relationData
  order :=
    (execution.relationSchedule_respectsGraph)
      |>.toRC11OrderWitness
  allocator :=
    result.allocator
  initialHeadEmpty := by
    simp
  generated :=
    result.generated

/--
Logical generation yields raw publication paths containing exactly the
successful-pop IDs, and the executable generator accepts them with the exact
same allocator.
-/
theorem generate?_accepted
    [DecidableEq α]
    {execution : SupportedExecution α}
    (result : GenerationResult execution) :
    ∃ publications,
      publications.map
          TreiberRC11.GeneratedEventsCheck.RawPublication.popEventId =
        TreiberRC11.GeneratedEventsCheck.successfulPopEventIds
          execution.toControlledSource.skeleton.events ∧
      TreiberRC11.GeneratedEventsCheck.generate?
          execution.relationData
          (TreiberRC11.ModelInitial.initialized :
            TreiberRA.State α)
          publications =
        some result.allocator :=
  TreiberRC11.GeneratedEventsCheck.generate?_complete
    execution.relationData
    (TreiberRC11.ModelInitial.initialized :
      TreiberRA.State α)
    result.generated

private theorem sourceEvent_of_occurrence
    {execution : SupportedExecution α}
    (occurrence :
      TreiberRC11.EventGraph.SourceOccurrence
        execution.toControlledSource.skeleton) :
    ∃ event,
      event ∈ execution.candidate.trace ∧
        event.toOwnedLabel execution.candidate.payload =
          occurrence.selected := by
  have selectedMember :
      occurrence.selected ∈
        execution.toControlledSource.skeleton.labels := by
    rw [occurrence.labelsShape]
    simp
  change
    occurrence.selected ∈
      SourceFrontend.projectedOwnedLabels
        execution.candidate.payload
        execution.candidate.trace at selectedMember
  rw [SourceFrontend.projectedOwnedLabels,
    List.mem_map] at selectedMember
  obtain ⟨event, eventMember, eventShape⟩ :=
    selectedMember
  exact ⟨event, eventMember, eventShape⟩

/--
Every projected `readNext` agrees with the final allocator constructed from
the independent immutable-link contract.
-/
theorem nextReadValueCertificate
    [DecidableEq α]
    {execution : SupportedExecution α}
    (result : GenerationResult execution) :
    TreiberRC11.NextReadValueCertificate
      result.toSourceAtomicExecution := by
  refine {
    matchesAllocator := ?_
  }
  intro fieldRead operation node next readLabel
  obtain ⟨event, eventMember, eventShape⟩ :=
    sourceEvent_of_occurrence fieldRead
  have sourceLabel :
      event.toTargetLabel execution.candidate.payload =
        .readNext operation node next := by
    exact
      (congrArg
        TreiberRC11.EventGraph.OwnedLabel.label
        eventShape).trans readLabel
  cases event <;>
    simp [TraceEvent.toTargetLabel] at sourceLabel
  next readNext thread sourceOperation sourceNode sourceNext =>
    obtain ⟨operationShape, nodeShape, nextShape⟩ :=
      sourceLabel
    subst sourceOperation
    subst sourceNode
    obtain ⟨leading, trailing, traceShape⟩ :=
      List.append_of_mem eventMember
    obtain ⟨publisherId, publisherThread, publisherOperation,
        publisherPrefixMember⟩ :=
      execution.client.immutableNextReads
        leading trailing thread operation node sourceNext traceShape
    let publisher : Atom α :=
      .occurrence
        ⟨publisherId,
          .pushCas publisherThread publisherOperation node
            (execution.candidate.payload node)
            sourceNext sourceNext true⟩
    have publisherTraceMember :
        TraceEvent.atomic
            ⟨publisherId,
              .pushCas publisherThread publisherOperation node
                (execution.candidate.payload node)
                sourceNext sourceNext true⟩ ∈
          execution.candidate.trace := by
      rw [traceShape]
      simp [publisherPrefixMember]
    have publisherMember :
        publisher ∈ execution.candidate.atoms :=
      occurrence_mem_atoms_iff.mpr publisherTraceMember
    have publishes :
        Publishes execution.candidate node sourceNext publisher :=
      ⟨publisherId, publisherThread, publisherOperation, rfl⟩
    have recorded :=
      result.allocatorMatches.records publisherMember publishes
    refine
      ⟨publisher.toTarget, execution.candidate.payload node, ?_⟩
    simpa [toSourceAtomicExecution, nextShape] using recorded

end GenerationResult

end WeakMemory.TreiberC11V1.GenerationFrontend
