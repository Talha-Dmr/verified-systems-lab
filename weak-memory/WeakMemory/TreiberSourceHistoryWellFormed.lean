import WeakMemory.TreiberMethodTrace

namespace WeakMemory

open List

/-!
# Structural well-formedness of source client histories

The per-thread method machine already proves that every projected source
trace has the shape

```text
invoke ; commit ; respond
```

with at most one unfinished suffix.  This module transfers that local shape
to the globally interleaved client history.  Global freshness of invocation
identities then also makes return identities unique.
-/

namespace HerlihyWing.Before

/-- A before witness is equivalently a two-element ordered sublist. -/
theorem iff_pair_sublist
    {first second : β}
    {items : List β} :
    WeakMemory.HerlihyWing.Before first second items ↔
      [first, second] <+ items := by
  constructor
  · rintro ⟨earlier, between, later, rfl⟩
    simp
  · intro ordered
    obtain ⟨firstPrefix, afterFirst, itemsShape,
        firstMember, secondSublist⟩ :=
      List.cons_sublist_iff.mp ordered
    have secondMember : second ∈ afterFirst :=
      secondSublist.subset (by simp)
    obtain ⟨earlier, between, firstShape⟩ :=
      List.mem_iff_append.mp firstMember
    obtain ⟨afterBetween, later, secondShape⟩ :=
      List.mem_iff_append.mp secondMember
    refine ⟨earlier, between ++ afterBetween, later, ?_⟩
    rw [itemsShape, firstShape, secondShape]
    simp [List.append_assoc]

/-- Removing unrelated leading elements preserves a before witness. -/
theorem prepend
    (leading : List β)
    {first second : β}
    {items : List β}
    (before : WeakMemory.HerlihyWing.Before first second items) :
    WeakMemory.HerlihyWing.Before
      first second (leading ++ items) := by
  rw [iff_pair_sublist] at before ⊢
  exact before.trans
    ((List.nil_sublist leading).append (List.Sublist.refl items))

/-- A list head occurs before every element of its tail. -/
theorem head_before
    {first second : β}
    {rest : List β}
    (member : second ∈ rest) :
    WeakMemory.HerlihyWing.Before
      first second (first :: rest) := by
  obtain ⟨between, later, restShape⟩ :=
    List.mem_iff_append.mp member
  subst rest
  exact ⟨[], between, later, rfl⟩

/-- Dropping a head distinct from both endpoints preserves their order. -/
theorem of_cons
    {head first second : β}
    {rest : List β}
    (before :
      WeakMemory.HerlihyWing.Before first second (head :: rest))
    (firstNe : first ≠ head) :
    WeakMemory.HerlihyWing.Before first second rest := by
  rw [iff_pair_sublist] at before ⊢
  cases before with
  | cons _ ordered =>
      exact ordered
  | cons_cons _ ordered =>
      exact (firstNe rfl).elim

/-- Ordered endpoints that survive `filterMap` remain ordered. -/
theorem filterMap
    {extract : β → Option γ}
    {first second : β}
    {firstValue secondValue : γ}
    {items : List β}
    (before :
      WeakMemory.HerlihyWing.Before first second items)
    (firstExtracts : extract first = some firstValue)
    (secondExtracts : extract second = some secondValue) :
    WeakMemory.HerlihyWing.Before
      firstValue secondValue (items.filterMap extract) := by
  rcases before with ⟨earlier, between, later, rfl⟩
  refine
    ⟨earlier.filterMap extract,
      between.filterMap extract,
      later.filterMap extract, ?_⟩
  simp [firstExtracts, secondExtracts]

/-- Duplicate-free lists cannot contain one value before itself. -/
theorem endpoints_ne
    {first second : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (before :
      WeakMemory.HerlihyWing.Before first second items) :
    first ≠ second :=
  noDuplicates.forall_sublist (iff_pair_sublist.mp before)

end HerlihyWing.Before

namespace HerlihyWing

/-- Thread projection distributes over history concatenation. -/
theorem eventsForThread_append
    (thread : Nat)
    (first second : History α) :
    eventsForThread thread (first ++ second) =
      eventsForThread thread first ++
        eventsForThread thread second := by
  induction first with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, eventsForThread]
      split <;> simp [inductionHypothesis]

/-- A thread projection is an ordered sublist of the global history. -/
theorem eventsForThread_sublist
    (thread : Nat)
    (history : History α) :
    eventsForThread thread history <+ history := by
  induction history with
  | nil =>
      exact .slnil
  | cons event rest inductionHypothesis =>
      by_cases sameThread : event.thread = thread
      · simp only [eventsForThread, sameThread, ↓reduceIte]
        exact inductionHypothesis.cons_cons event
      · simp only [eventsForThread, sameThread, ↓reduceIte]
        exact inductionHypothesis.cons event

namespace Before

/-- Global order between same-thread events survives thread projection. -/
theorem eventsForThread
    {thread : Nat}
    {first second : HistoryEvent α}
    {history : History α}
    (before : Before first second history)
    (firstThread : first.thread = thread)
    (secondThread : second.thread = thread) :
    Before first second
      (HerlihyWing.eventsForThread thread history) := by
  rcases before with ⟨earlier, between, later, rfl⟩
  refine
    ⟨HerlihyWing.eventsForThread thread earlier,
      HerlihyWing.eventsForThread thread between,
      HerlihyWing.eventsForThread thread later, ?_⟩
  simp [HerlihyWing.eventsForThread_append,
    HerlihyWing.eventsForThread, firstThread, secondThread]

/-- Order in a thread projection lifts back to the global history. -/
theorem of_eventsForThread
    {thread : Nat}
    {first second : HistoryEvent α}
    {history : History α}
    (before :
      Before first second
        (HerlihyWing.eventsForThread thread history)) :
    Before first second history := by
  rw [iff_pair_sublist] at before ⊢
  exact before.trans
    (HerlihyWing.eventsForThread_sublist thread history)

end Before

end HerlihyWing

/--
If a filtered extraction is duplicate-free, two source values extracting the
same retained value must themselves be equal.
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

namespace TreiberRC11

namespace MethodTrace

/-- Method-event thread projection commutes with commit erasure. -/
theorem history_eventsForThread
    (thread : Nat)
    (events : List (Event α)) :
    history (eventsForThread thread events) =
      HerlihyWing.eventsForThread thread (history events) := by
  induction events with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases event with
      | invoke invocation =>
          by_cases sameThread : invocation.thread = thread
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?,
              HerlihyWing.eventsForThread,
              HerlihyWing.HistoryEvent.thread] using
              congrArg (List.cons (.invoke invocation))
                inductionHypothesis
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?,
              HerlihyWing.eventsForThread,
              HerlihyWing.HistoryEvent.thread] using
              inductionHypothesis
      | commit entry =>
          by_cases sameThread : entry.thread = thread
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?] using
              inductionHypothesis
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?] using
              inductionHypothesis
      | respond returned =>
          by_cases sameThread : returned.thread = thread
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?,
              HerlihyWing.eventsForThread,
              HerlihyWing.HistoryEvent.thread] using
              congrArg (List.cons (.respond returned))
                inductionHypothesis
          · simpa [eventsForThread, Event.thread, sameThread,
              history, Event.historyEvent?,
              HerlihyWing.eventsForThread,
              HerlihyWing.HistoryEvent.thread] using
              inductionHypothesis

/--
The client-visible projection of one method-machine run.  Every completed
method contributes an invocation/response pair and the final method may have
only its invocation visible.
-/
inductive ClientForm : HerlihyWing.History α → Prop where
  | nil :
      ClientForm []
  | pending
      (invocation : HerlihyWing.Invocation α) :
      ClientForm [.invoke invocation]
  | complete
      (entry : HerlihyWing.IdentifiedCompleted α)
      {rest : HerlihyWing.History α} :
      ClientForm rest →
      ClientForm
        (.invoke entry.invocation ::
          .respond entry.returned :: rest)

/-- Erasing commits from a thread-form method trace yields `ClientForm`. -/
theorem ThreadForm.toClientForm :
    ∀ {events : List (Event α)},
      ThreadForm events →
      ClientForm (history events)
  | _, .nil _ => by
      exact .nil
  | _, .invoke pending => by
      cases pending with
      | nil =>
          exact .pending _
      | commit committed =>
          cases committed with
          | nil =>
              exact .pending _
          | respond rest =>
              simpa [history, Event.historyEvent?] using
                ClientForm.complete _ (ThreadForm.toClientForm rest)

namespace ClientForm

/-- Invocation identifiers at ordered invocations remain ordered. -/
theorem invocationIds_before
    {history : HerlihyWing.History α}
    {first second : HerlihyWing.Invocation α}
    (before :
      HerlihyWing.Before
        (.invoke first) (.invoke second) history) :
    HerlihyWing.Before first.id second.id
      (HerlihyWing.invocationIds history) := by
  exact before.filterMap rfl rfl

/-- Distinct invocation occurrences have distinct globally fresh identities. -/
theorem invocationIds_ne
    {history : HerlihyWing.History α}
    {first second : HerlihyWing.Invocation α}
    (noDuplicates :
      (HerlihyWing.invocationIds history).Nodup)
    (before :
      HerlihyWing.Before
        (.invoke first) (.invoke second) history) :
    first.id ≠ second.id :=
  HerlihyWing.Before.endpoints_ne
    noDuplicates (invocationIds_before before)

/-- Every response in a client-form trace has its matching invocation first. -/
theorem returnHasInvocation
    {history : HerlihyWing.History α}
    (form : ClientForm history)
    {returned : HerlihyWing.Return α}
    (member : HerlihyWing.HistoryEvent.respond returned ∈ history) :
    ∃ invocation,
      HerlihyWing.Matches invocation returned ∧
        HerlihyWing.Before
          (.invoke invocation) (.respond returned) history := by
  induction form with
  | nil =>
      simp at member
  | pending invocation =>
      simp at member
  | @complete entry rest restForm inductionHypothesis =>
      rcases List.mem_cons.mp member with atInvocation | afterInvocation
      · cases atInvocation
      · rcases List.mem_cons.mp afterInvocation with
          atResponse | inRest
        · cases atResponse
          exact ⟨entry.invocation, ⟨rfl, rfl⟩,
            ⟨[], [], rest, rfl⟩⟩
        · obtain ⟨invocation, matching, before⟩ :=
            inductionHypothesis inRest
          exact ⟨invocation, matching,
            by
              simpa using
                before.prepend
                  ([
                    .invoke entry.invocation,
                    .respond entry.returned
                  ] : HerlihyWing.History α)⟩

/--
Within one client-form trace, an earlier invocation must respond before the
next invocation can occur.
-/
theorem threadSequential
    {history : HerlihyWing.History α}
    (form : ClientForm history)
    (noDuplicates :
      (HerlihyWing.invocationIds history).Nodup)
    {first second : HerlihyWing.Invocation α}
    (firstMember :
      HerlihyWing.HistoryEvent.invoke first ∈ history)
    (secondMember :
      HerlihyWing.HistoryEvent.invoke second ∈ history)
    (sameThread : first.thread = second.thread)
    (before :
      HerlihyWing.Before
        (.invoke first) (.invoke second) history) :
    ∃ returned,
      HerlihyWing.Matches first returned ∧
        HerlihyWing.Before
          (.invoke first) (.respond returned) history ∧
        HerlihyWing.Before
          (.respond returned) (.invoke second) history := by
  induction form with
  | nil =>
      simp at firstMember
  | pending invocation =>
      have idsNe := invocationIds_ne noDuplicates before
      simp only [List.mem_singleton] at firstMember secondMember
      cases firstMember
      cases secondMember
      exact (idsNe rfl).elim
  | @complete entry rest restForm inductionHypothesis =>
      have splitNodup :
          entry.id ∉ HerlihyWing.invocationIds rest ∧
            (HerlihyWing.invocationIds rest).Nodup := by
        simpa [HerlihyWing.invocationIds,
          HerlihyWing.HistoryEvent.invocationId?,
          HerlihyWing.IdentifiedCompleted.invocation] using
          noDuplicates
      by_cases firstIsHead : first = entry.invocation
      · subst first
        have idsNe := invocationIds_ne noDuplicates before
        have secondInRest :
            HerlihyWing.HistoryEvent.invoke second ∈ rest := by
          rcases List.mem_cons.mp secondMember with
              atInvocation | afterInvocation
          · cases atInvocation
            exact (idsNe rfl).elim
          · rcases List.mem_cons.mp afterInvocation with
              atResponse | inRest
            · cases atResponse
            · exact inRest
        refine ⟨entry.returned, ⟨rfl, rfl⟩,
          ⟨[], [], rest, rfl⟩, ?_⟩
        exact
          (HerlihyWing.Before.head_before secondInRest).prepend
            [.invoke entry.invocation]
      · have firstInRest :
            HerlihyWing.HistoryEvent.invoke first ∈ rest := by
          rcases List.mem_cons.mp firstMember with
              atInvocation | afterInvocation
          · have : first = entry.invocation := by
              injection atInvocation
            exact (firstIsHead this).elim
          · rcases List.mem_cons.mp afterInvocation with
              atResponse | inRest
            · cases atResponse
            · exact inRest
        have afterInvocation :
            HerlihyWing.Before
              (.invoke first) (.invoke second)
              (.respond entry.returned :: rest) := by
          apply HerlihyWing.Before.of_cons before
          intro same
          injection same with sameInvocation
          exact firstIsHead sameInvocation
        have inRest :
            HerlihyWing.Before
              (.invoke first) (.invoke second) rest := by
          apply HerlihyWing.Before.of_cons afterInvocation
          intro same
          cases same
        have secondInRest :
            HerlihyWing.HistoryEvent.invoke second ∈ rest :=
          inRest.second_mem
        obtain ⟨returned, matching, invocationBeforeReturn,
            returnBeforeInvocation⟩ :=
          inductionHypothesis splitNodup.2
            firstInRest secondInRest inRest
        exact ⟨returned, matching,
          by
            simpa using
              invocationBeforeReturn.prepend
                ([
                  .invoke entry.invocation,
                  .respond entry.returned
                ] : HerlihyWing.History α),
          by
            simpa using
              returnBeforeInvocation.prepend
                ([
                  .invoke entry.invocation,
                  .respond entry.returned
                ] : HerlihyWing.History α)⟩

/--
Fresh invocation identities make response identities duplicate-free in a
client-form trace.
-/
theorem returnIdsNodup
    {history : HerlihyWing.History α}
    (form : ClientForm history)
    (noDuplicates :
      (HerlihyWing.invocationIds history).Nodup) :
    (HerlihyWing.returnIds history).Nodup := by
  induction form with
  | nil =>
      simp [HerlihyWing.returnIds]
  | pending invocation =>
      simp [HerlihyWing.returnIds,
        HerlihyWing.HistoryEvent.returnId?]
  | @complete entry rest restForm inductionHypothesis =>
      have splitNodup :
          entry.id ∉ HerlihyWing.invocationIds rest ∧
            (HerlihyWing.invocationIds rest).Nodup := by
        simpa [HerlihyWing.invocationIds,
          HerlihyWing.HistoryEvent.invocationId?,
          HerlihyWing.IdentifiedCompleted.invocation] using
          noDuplicates
      have headNotReturned :
          entry.id ∉ HerlihyWing.returnIds rest := by
        intro member
        obtain ⟨event, eventMember, extracts⟩ :=
          List.mem_filterMap.mp member
        cases event with
        | invoke invocation =>
            simp [HerlihyWing.HistoryEvent.returnId?] at extracts
        | respond returned =>
            have returnedId : returned.id = entry.id := by
              simpa [HerlihyWing.HistoryEvent.returnId?] using
                Option.some.inj extracts
            obtain ⟨invocation, matching, before⟩ :=
              restForm.returnHasInvocation eventMember
            have invocationMember :
                invocation.id ∈
                  HerlihyWing.invocationIds rest :=
              List.mem_filterMap.mpr
                ⟨.invoke invocation, before.first_mem, rfl⟩
            have sameId : invocation.id = entry.id :=
              matching.2.trans returnedId
            apply splitNodup.1
            simpa [sameId] using invocationMember
      simpa [HerlihyWing.returnIds,
        HerlihyWing.HistoryEvent.returnId?,
        HerlihyWing.IdentifiedCompleted.returned] using
        List.nodup_cons.mpr
          ⟨headNotReturned,
            inductionHypothesis splitNodup.2⟩

/-- A client-form trace with fresh invocation identities is well formed. -/
theorem wellFormed
    {history : HerlihyWing.History α}
    (form : ClientForm history)
    (noDuplicates :
      (HerlihyWing.invocationIds history).Nodup) :
    HerlihyWing.WellFormed history where
  invocationIdsNodup :=
    noDuplicates
  returnIdsNodup :=
    form.returnIdsNodup noDuplicates
  returnHasInvocation :=
    form.returnHasInvocation
  threadSequential firstMember secondMember sameThread before :=
    form.threadSequential noDuplicates
      firstMember secondMember sameThread before

end ClientForm

/--
Every projected client history is well formed when the global invocation
identities are fresh.
-/
theorem threadProjectionWellFormed
    {events : List (Event α)}
    (executions :
      ∀ thread,
        ∃ final,
          Execution .idle
            (eventsForThread thread events) final)
    (globalNodup :
      (HerlihyWing.invocationIds (history events)).Nodup)
    (thread : Nat) :
    HerlihyWing.WellFormed
      (HerlihyWing.eventsForThread thread (history events)) := by
  obtain ⟨final, execution⟩ := executions thread
  have form :
      ClientForm
        (HerlihyWing.eventsForThread thread (history events)) := by
    rw [← history_eventsForThread]
    exact execution.toThreadForm.toClientForm
  have localNodup :
      (HerlihyWing.invocationIds
        (HerlihyWing.eventsForThread thread
          (history events))).Nodup := by
    exact
      ((HerlihyWing.eventsForThread_sublist thread
        (history events)).filterMap
          HerlihyWing.HistoryEvent.invocationId?).nodup
        globalNodup
  exact form.wellFormed localNodup

/-- Every global response has a matching earlier invocation. -/
theorem returnHasInvocation
    {events : List (Event α)}
    (executions :
      ∀ thread,
        ∃ final,
          Execution .idle
            (eventsForThread thread events) final)
    (globalNodup :
      (HerlihyWing.invocationIds (history events)).Nodup)
    {returned : HerlihyWing.Return α}
    (member :
      HerlihyWing.HistoryEvent.respond returned ∈ history events) :
    ∃ invocation,
      HerlihyWing.Matches invocation returned ∧
        HerlihyWing.Before
          (.invoke invocation) (.respond returned)
          (history events) := by
  have projectedMember :
      HerlihyWing.HistoryEvent.respond returned ∈
        HerlihyWing.eventsForThread returned.thread
          (history events) :=
    HerlihyWing.mem_eventsForThread.mpr ⟨member, rfl⟩
  obtain ⟨invocation, matching, before⟩ :=
    (threadProjectionWellFormed executions globalNodup
      returned.thread).returnHasInvocation projectedMember
  exact ⟨invocation, matching, before.of_eventsForThread⟩

/--
Globally fresh invocations and the per-thread method machines make global
response identities duplicate-free, even when different threads interleave.
-/
theorem returnIdsNodup
    {events : List (Event α)}
    (executions :
      ∀ thread,
        ∃ final,
          Execution .idle
            (eventsForThread thread events) final)
    (globalNodup :
      (HerlihyWing.invocationIds (history events)).Nodup) :
    (HerlihyWing.returnIds (history events)).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  change
    List.Pairwise (fun first second => first ≠ second)
      ((history events).filterMap
        HerlihyWing.HistoryEvent.returnId?)
  rw [List.pairwise_filterMap]
  apply List.pairwise_of_forall_sublist
  intro firstEvent secondEvent ordered
  intro firstId firstExtracts secondId secondExtracts
  cases firstEvent with
  | invoke invocation =>
      simp [HerlihyWing.HistoryEvent.returnId?] at firstExtracts
  | respond firstReturned =>
      cases secondEvent with
      | invoke invocation =>
          simp [HerlihyWing.HistoryEvent.returnId?] at secondExtracts
      | respond secondReturned =>
          have firstIdShape : firstReturned.id = firstId := by
            simpa [HerlihyWing.HistoryEvent.returnId?] using
              Option.some.inj firstExtracts
          have secondIdShape : secondReturned.id = secondId := by
            simpa [HerlihyWing.HistoryEvent.returnId?] using
              Option.some.inj secondExtracts
          subst firstId
          subst secondId
          intro sameReturnId
          have responseBefore :
              HerlihyWing.Before
                (.respond firstReturned)
                (.respond secondReturned)
                (history events) :=
            HerlihyWing.Before.iff_pair_sublist.mpr ordered
          obtain ⟨firstInvocation, firstMatches,
              firstInvocationBefore⟩ :=
            returnHasInvocation executions globalNodup
              responseBefore.first_mem
          obtain ⟨secondInvocation, secondMatches,
              secondInvocationBefore⟩ :=
            returnHasInvocation executions globalNodup
              responseBefore.second_mem
          have invocationIdsSame :
              secondInvocation.id = firstInvocation.id := by
            exact secondMatches.2.trans
              (sameReturnId.symm.trans firstMatches.2.symm)
          have invocationEventsSame :
              (HerlihyWing.HistoryEvent.invoke firstInvocation) =
                .invoke secondInvocation := by
            apply eq_of_filterMap_nodup globalNodup
              firstInvocationBefore.first_mem
              secondInvocationBefore.first_mem
              rfl
            simp [HerlihyWing.HistoryEvent.invocationId?,
              invocationIdsSame]
          have invocationsSame :
              firstInvocation = secondInvocation := by
            injection invocationEventsSame
          have sameReturnedThread :
              firstReturned.thread = secondReturned.thread := by
            calc
              firstReturned.thread = firstInvocation.thread :=
                firstMatches.1.symm
              _ = secondInvocation.thread := by
                rw [invocationsSame]
              _ = secondReturned.thread :=
                secondMatches.1
          have projectedBefore :
              HerlihyWing.Before
                (.respond firstReturned)
                (.respond secondReturned)
                (HerlihyWing.eventsForThread
                  firstReturned.thread (history events)) :=
            responseBefore.eventsForThread
              rfl sameReturnedThread.symm
          have projectedIdBefore :
              HerlihyWing.Before
                firstReturned.id secondReturned.id
                (HerlihyWing.returnIds
                  (HerlihyWing.eventsForThread
                    firstReturned.thread (history events))) :=
            projectedBefore.filterMap rfl rfl
          exact
            (HerlihyWing.Before.endpoints_ne
              (threadProjectionWellFormed executions globalNodup
                firstReturned.thread).returnIdsNodup
              projectedIdBefore)
              sameReturnId

/--
Per-thread method executions plus globally fresh invocation identities are
exactly the structural obligations of a well-formed global client history.
-/
theorem historyWellFormed
    {events : List (Event α)}
    (executions :
      ∀ thread,
        ∃ final,
          Execution .idle
            (eventsForThread thread events) final)
    (globalNodup :
      (HerlihyWing.invocationIds (history events)).Nodup) :
    HerlihyWing.WellFormed (history events) where
  invocationIdsNodup :=
    globalNodup
  returnIdsNodup :=
    returnIdsNodup executions globalNodup
  returnHasInvocation member :=
    returnHasInvocation executions globalNodup member
  threadSequential
      {first} {second}
      firstMember secondMember sameThread before := by
    have firstProjected :
        HerlihyWing.HistoryEvent.invoke first ∈
          HerlihyWing.eventsForThread first.thread
            (history events) :=
      HerlihyWing.mem_eventsForThread.mpr
        ⟨firstMember, rfl⟩
    have secondProjected :
        HerlihyWing.HistoryEvent.invoke second ∈
          HerlihyWing.eventsForThread first.thread
            (history events) :=
      HerlihyWing.mem_eventsForThread.mpr
        ⟨secondMember, sameThread.symm⟩
    have projectedBefore :
        HerlihyWing.Before
          (.invoke first) (.invoke second)
          (HerlihyWing.eventsForThread first.thread
            (history events)) :=
      before.eventsForThread rfl sameThread.symm
    obtain ⟨returned, matching, invocationBeforeReturn,
        returnBeforeInvocation⟩ :=
      (threadProjectionWellFormed executions globalNodup
        first.thread).threadSequential
          firstProjected secondProjected sameThread projectedBefore
    exact ⟨returned, matching,
      invocationBeforeReturn.of_eventsForThread,
      returnBeforeInvocation.of_eventsForThread⟩

end MethodTrace

/--
The invocation identities in the client projection are exactly the operation
identities collected by the source-skeleton freshness check.
-/
theorem invocationIds_sourceHistory
    (skeleton : EventGraph.Skeleton α) :
    HerlihyWing.invocationIds (sourceHistory skeleton) =
      Interleaving.invocationOperations skeleton.labels := by
  change
    (skeleton.labels.filterMap sourceHistoryEvent?).filterMap
        HerlihyWing.HistoryEvent.invocationId? =
      skeleton.labels.filterMap
        Interleaving.invocationOperation?
  induction skeleton.labels with
  | nil =>
      rfl
  | cons owned rest inductionHypothesis =>
      rcases owned with ⟨thread, label, ownership⟩
      cases label <;>
        simp [sourceHistoryEvent?,
          Interleaving.invocationOperation?,
          HerlihyWing.HistoryEvent.invocationId?,
          inductionHypothesis]

namespace Interleaving.SourceSkeleton

/--
Every certified source skeleton produces a structurally well-formed
Herlihy–Wing client history.
-/
theorem historyWellFormed
    {initial : TreiberRA.State α}
    {skeleton : EventGraph.Skeleton α}
    (certificate :
      Interleaving.SourceSkeleton initial skeleton) :
    HerlihyWing.WellFormed (sourceHistory skeleton) := by
  have invocationNodup :
      (HerlihyWing.invocationIds
        (MethodTrace.history
          (MethodTrace.ofSkeleton skeleton))).Nodup := by
    rw [MethodTrace.history_ofSkeleton,
      invocationIds_sourceHistory]
    exact certificate.operationIdsNodup
  have wellFormed :=
    MethodTrace.historyWellFormed
      (events := MethodTrace.ofSkeleton skeleton)
      (fun thread => certificate.methodExecution thread)
      invocationNodup
  rw [MethodTrace.history_ofSkeleton] at wellFormed
  exact wellFormed

end Interleaving.SourceSkeleton

end TreiberRC11

end WeakMemory
