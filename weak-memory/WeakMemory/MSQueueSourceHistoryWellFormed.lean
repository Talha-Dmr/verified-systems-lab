import WeakMemory.MSQueueSourceMethodTrace

namespace WeakMemory.MSQueue.Source

open List

/-!
# Well-formed source histories

This module closes the structural Herlihy--Wing history obligations directly
from the source machine.  Fresh operation identifiers come from
`SourceWellFormed`; ordering and response obligations come from each thread's
checked `Run`.
-/

namespace TraceEvent

/-- Extract a response operation identifier and discard all other events. -/
def returnId? : TraceEvent Value → Option OperationId
  | .respondEnqueue _ operation => some operation
  | .respondDequeue _ operation _ => some operation
  | _ => none

end TraceEvent

/-- Response identities in global source order. -/
def sourceReturnIds (trace : List (TraceEvent Value)) : List OperationId :=
  trace.filterMap TraceEvent.returnId?

/-- The history invocation projection is exactly the source freshness projection. -/
theorem invocationIds_sourceHistory
    (trace : List (TraceEvent Value)) :
    MSQueue.HW.invocationIds (sourceHistory trace) = invocationIds trace := by
  induction trace with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases event <;>
        simp [sourceHistory, sourceHistoryEvent?, invocationIds,
          TraceEvent.invocationId?, MSQueue.HW.invocationIds,
          MSQueue.HW.HistoryEvent.invocationId?]
      all_goals exact inductionHypothesis

/-- The history response projection is exactly the source response projection. -/
theorem returnIds_sourceHistory
    (trace : List (TraceEvent Value)) :
    MSQueue.HW.returnIds (sourceHistory trace) = sourceReturnIds trace := by
  induction trace with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases event <;>
        simp [sourceHistory, sourceHistoryEvent?, sourceReturnIds,
          TraceEvent.returnId?, MSQueue.HW.returnIds,
          MSQueue.HW.HistoryEvent.returnId?]
      all_goals exact inductionHypothesis

namespace HistoryWellFormed

/-! Small list-order facts used to lift one-thread method runs globally. -/

theorem before_iff_pair_sublist
    {first second : β}
    {items : List β} :
    HerlihyWing.Before first second items ↔ [first, second] <+ items := by
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

theorem before_prepend
    (leading : List β)
    {first second : β}
    {items : List β}
    (before : HerlihyWing.Before first second items) :
    HerlihyWing.Before first second (leading ++ items) := by
  rw [before_iff_pair_sublist] at before ⊢
  exact before.trans
    ((List.nil_sublist leading).append (List.Sublist.refl items))

theorem head_before
    {first second : β}
    {rest : List β}
    (member : second ∈ rest) :
    HerlihyWing.Before first second (first :: rest) := by
  obtain ⟨between, later, restShape⟩ :=
    List.mem_iff_append.mp member
  subst rest
  exact ⟨[], between, later, rfl⟩

theorem before_of_cons
    {head first second : β}
    {rest : List β}
    (before : HerlihyWing.Before first second (head :: rest))
    (firstNe : first ≠ head) :
    HerlihyWing.Before first second rest := by
  rw [before_iff_pair_sublist] at before ⊢
  cases before with
  | cons _ ordered => exact ordered
  | cons_cons _ ordered => exact (firstNe rfl).elim

theorem before_filterMap
    {extract : β → Option γ}
    {first second : β}
    {firstValue secondValue : γ}
    {items : List β}
    (before : HerlihyWing.Before first second items)
    (firstExtracts : extract first = some firstValue)
    (secondExtracts : extract second = some secondValue) :
    HerlihyWing.Before firstValue secondValue
      (items.filterMap extract) := by
  rcases before with ⟨earlier, between, later, rfl⟩
  refine ⟨earlier.filterMap extract, between.filterMap extract,
    later.filterMap extract, ?_⟩
  simp [firstExtracts, secondExtracts]

theorem before_endpoints_ne
    {first second : β}
    {items : List β}
    (noDuplicates : items.Nodup)
    (before : HerlihyWing.Before first second items) :
    first ≠ second :=
  noDuplicates.forall_sublist (before_iff_pair_sublist.mp before)

theorem eventsForThread_append
    (thread : ThreadId)
    (first second : MSQueue.HW.History Value) :
    MSQueue.HW.eventsForThread thread (first ++ second) =
      MSQueue.HW.eventsForThread thread first ++
        MSQueue.HW.eventsForThread thread second := by
  induction first with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, MSQueue.HW.eventsForThread]
      split <;> simp [inductionHypothesis]

theorem eventsForThread_sublist
    (thread : ThreadId)
    (history : MSQueue.HW.History Value) :
    MSQueue.HW.eventsForThread thread history <+ history := by
  induction history with
  | nil => exact .slnil
  | cons event rest inductionHypothesis =>
      by_cases sameThread : event.thread = thread
      · simp only [MSQueue.HW.eventsForThread, sameThread, ↓reduceIte]
        exact inductionHypothesis.cons_cons event
      · simp only [MSQueue.HW.eventsForThread, sameThread, ↓reduceIte]
        exact inductionHypothesis.cons event

theorem before_eventsForThread
    {thread : ThreadId}
    {first second : MSQueue.HW.HistoryEvent Value}
    {history : MSQueue.HW.History Value}
    (before : HerlihyWing.Before first second history)
    (firstThread : first.thread = thread)
    (secondThread : second.thread = thread) :
    HerlihyWing.Before first second
      (MSQueue.HW.eventsForThread thread history) := by
  rcases before with ⟨earlier, between, later, rfl⟩
  refine ⟨MSQueue.HW.eventsForThread thread earlier,
    MSQueue.HW.eventsForThread thread between,
    MSQueue.HW.eventsForThread thread later, ?_⟩
  simp [eventsForThread_append, MSQueue.HW.eventsForThread,
    firstThread, secondThread]

theorem before_of_eventsForThread
    {thread : ThreadId}
    {first second : MSQueue.HW.HistoryEvent Value}
    {history : MSQueue.HW.History Value}
    (before : HerlihyWing.Before first second
      (MSQueue.HW.eventsForThread thread history)) :
    HerlihyWing.Before first second history := by
  rw [before_iff_pair_sublist] at before ⊢
  exact before.trans (eventsForThread_sublist thread history)

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
  | nil => simp at firstMember
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp firstMember with firstIsHead | firstInRest
      · subst first
        rcases List.mem_cons.mp secondMember with secondIsHead | secondInRest
        · exact secondIsHead.symm
        · have valueMember : value ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr ⟨second, secondInRest, secondExtracts⟩
          have shapedNodup :
              (value :: rest.filterMap extract).Nodup := by
            simpa [firstExtracts] using noDuplicates
          exact ((List.nodup_cons.mp shapedNodup).1 valueMember).elim
      · rcases List.mem_cons.mp secondMember with secondIsHead | secondInRest
        · subst second
          have valueMember : value ∈ rest.filterMap extract :=
            List.mem_filterMap.mpr ⟨first, firstInRest, firstExtracts⟩
          have shapedNodup :
              (value :: rest.filterMap extract).Nodup := by
            simpa [secondExtracts] using noDuplicates
          exact ((List.nodup_cons.mp shapedNodup).1 valueMember).elim
        · have restNodup : (rest.filterMap extract).Nodup :=
            ((List.sublist_cons_self head rest).filterMap extract).nodup
              noDuplicates
          exact inductionHypothesis restNodup firstInRest secondInRest
            firstExtracts secondExtracts

/-! The client-visible shape of one source thread. -/

inductive ClientForm : MSQueue.HW.History Value → Prop where
  | nil : ClientForm []
  | pending (invocation : MSQueue.HW.Invocation Value) :
      ClientForm [.invoke invocation]
  | complete
      (entry : MSQueue.HW.IdentifiedCompleted Value)
      {rest : MSQueue.HW.History Value} :
      ClientForm rest →
      ClientForm
        (.invoke entry.invocation :: .respond entry.returned :: rest)

/-- Erasing commits from a well-bracketed method trace gives client form. -/
theorem clientForm_of_threadForm
    : ∀ {events : List (MethodTrace.Event Value)},
      MethodTrace.ThreadForm events →
        ClientForm (MethodTrace.history events)
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
              simpa [MethodTrace.history,
                MethodTrace.Event.historyEvent?] using
                ClientForm.complete _
                  (clientForm_of_threadForm rest)

namespace ClientForm

theorem invocationIds_before
    {history : MSQueue.HW.History Value}
    {first second : MSQueue.HW.Invocation Value}
    (before : HerlihyWing.Before (.invoke first) (.invoke second) history) :
    HerlihyWing.Before first.id second.id
      (MSQueue.HW.invocationIds history) :=
  before_filterMap before rfl rfl

theorem invocationIds_ne
    {history : MSQueue.HW.History Value}
    {first second : MSQueue.HW.Invocation Value}
    (noDuplicates : (MSQueue.HW.invocationIds history).Nodup)
    (before : HerlihyWing.Before (.invoke first) (.invoke second) history) :
    first.id ≠ second.id :=
  before_endpoints_ne noDuplicates (invocationIds_before before)

theorem returnHasInvocation
    {history : MSQueue.HW.History Value}
    (form : ClientForm history)
    {returned : MSQueue.HW.Return Value}
    (member : MSQueue.HW.HistoryEvent.respond returned ∈ history) :
    ∃ invocation,
      MSQueue.HW.Matches invocation returned ∧
        HerlihyWing.Before (.invoke invocation) (.respond returned) history := by
  induction form with
  | nil => simp at member
  | pending invocation => simp at member
  | @complete entry rest restForm inductionHypothesis =>
      rcases List.mem_cons.mp member with atInvocation | afterInvocation
      · cases atInvocation
      · rcases List.mem_cons.mp afterInvocation with atResponse | inRest
        · cases atResponse
          exact ⟨entry.invocation, ⟨rfl, rfl⟩,
            ⟨[], [], rest, rfl⟩⟩
        · obtain ⟨invocation, matching, before⟩ :=
            inductionHypothesis inRest
          exact ⟨invocation, matching,
            by
              simpa using
                (before_prepend
                  ([.invoke entry.invocation, .respond entry.returned] :
                    MSQueue.HW.History Value) before)⟩

theorem threadSequential
    {history : MSQueue.HW.History Value}
    (form : ClientForm history)
    (noDuplicates : (MSQueue.HW.invocationIds history).Nodup)
    {first second : MSQueue.HW.Invocation Value}
    (firstMember : MSQueue.HW.HistoryEvent.invoke first ∈ history)
    (secondMember : MSQueue.HW.HistoryEvent.invoke second ∈ history)
    (sameThread : first.thread = second.thread)
    (before : HerlihyWing.Before (.invoke first) (.invoke second) history) :
    ∃ returned,
      MSQueue.HW.Matches first returned ∧
        HerlihyWing.Before (.invoke first) (.respond returned) history ∧
        HerlihyWing.Before (.respond returned) (.invoke second) history := by
  induction form with
  | nil => simp at firstMember
  | pending invocation =>
      have idsNe := invocationIds_ne noDuplicates before
      simp only [List.mem_singleton] at firstMember secondMember
      cases firstMember
      cases secondMember
      exact (idsNe rfl).elim
  | @complete entry rest restForm inductionHypothesis =>
      have splitNodup :
          entry.id ∉ MSQueue.HW.invocationIds rest ∧
            (MSQueue.HW.invocationIds rest).Nodup := by
        simpa [MSQueue.HW.invocationIds,
          MSQueue.HW.HistoryEvent.invocationId?,
          MSQueue.HW.IdentifiedCompleted.invocation] using noDuplicates
      by_cases firstIsHead : first = entry.invocation
      · subst first
        have idsNe := invocationIds_ne noDuplicates before
        have secondInRest :
            MSQueue.HW.HistoryEvent.invoke second ∈ rest := by
          rcases List.mem_cons.mp secondMember with atInvocation | afterInvocation
          · cases atInvocation
            exact (idsNe rfl).elim
          · rcases List.mem_cons.mp afterInvocation with atResponse | inRest
            · cases atResponse
            · exact inRest
        refine ⟨entry.returned, ⟨rfl, rfl⟩,
          ⟨[], [], rest, rfl⟩, ?_⟩
        exact before_prepend [.invoke entry.invocation]
          (head_before secondInRest)
      · have firstInRest :
            MSQueue.HW.HistoryEvent.invoke first ∈ rest := by
          rcases List.mem_cons.mp firstMember with atInvocation | afterInvocation
          · have : first = entry.invocation := by injection atInvocation
            exact (firstIsHead this).elim
          · rcases List.mem_cons.mp afterInvocation with atResponse | inRest
            · cases atResponse
            · exact inRest
        have afterInvocation :
            HerlihyWing.Before (.invoke first) (.invoke second)
              (.respond entry.returned :: rest) := by
          apply before_of_cons before
          intro same
          injection same with sameInvocation
          exact firstIsHead sameInvocation
        have inRest :
            HerlihyWing.Before (.invoke first) (.invoke second) rest := by
          apply before_of_cons afterInvocation
          intro same
          cases same
        have secondInRest : MSQueue.HW.HistoryEvent.invoke second ∈ rest :=
          inRest.second_mem
        obtain ⟨returned, matching, invocationBeforeReturn,
            returnBeforeInvocation⟩ :=
          inductionHypothesis splitNodup.2 firstInRest secondInRest inRest
        exact ⟨returned, matching,
          by
            simpa using
              (before_prepend
                ([.invoke entry.invocation, .respond entry.returned] :
                  MSQueue.HW.History Value) invocationBeforeReturn),
          by
            simpa using
              (before_prepend
                ([.invoke entry.invocation, .respond entry.returned] :
                  MSQueue.HW.History Value) returnBeforeInvocation)⟩

theorem returnIdsNodup
    {history : MSQueue.HW.History Value}
    (form : ClientForm history)
    (noDuplicates : (MSQueue.HW.invocationIds history).Nodup) :
    (MSQueue.HW.returnIds history).Nodup := by
  induction form with
  | nil => simp [MSQueue.HW.returnIds]
  | pending invocation =>
      simp [MSQueue.HW.returnIds, MSQueue.HW.HistoryEvent.returnId?]
  | @complete entry rest restForm inductionHypothesis =>
      have splitNodup :
          entry.id ∉ MSQueue.HW.invocationIds rest ∧
            (MSQueue.HW.invocationIds rest).Nodup := by
        simpa [MSQueue.HW.invocationIds,
          MSQueue.HW.HistoryEvent.invocationId?,
          MSQueue.HW.IdentifiedCompleted.invocation] using noDuplicates
      have headNotReturned : entry.id ∉ MSQueue.HW.returnIds rest := by
        intro member
        obtain ⟨event, eventMember, extracts⟩ :=
          List.mem_filterMap.mp member
        cases event with
        | invoke invocation =>
            simp [MSQueue.HW.HistoryEvent.returnId?] at extracts
        | respond returned =>
            have returnedId : returned.id = entry.id := by
              simpa [MSQueue.HW.HistoryEvent.returnId?] using
                Option.some.inj extracts
            obtain ⟨invocation, matching, before⟩ :=
              restForm.returnHasInvocation eventMember
            have invocationMember :
                invocation.id ∈ MSQueue.HW.invocationIds rest :=
              List.mem_filterMap.mpr
                ⟨.invoke invocation, before.first_mem, rfl⟩
            have sameId : invocation.id = entry.id :=
              matching.2.trans returnedId
            apply splitNodup.1
            simpa [sameId] using invocationMember
      simpa [MSQueue.HW.returnIds, MSQueue.HW.HistoryEvent.returnId?,
        MSQueue.HW.IdentifiedCompleted.returned] using
        List.nodup_cons.mpr
          ⟨headNotReturned, inductionHypothesis splitNodup.2⟩

theorem wellFormed
    {history : MSQueue.HW.History Value}
    (form : ClientForm history)
    (noDuplicates : (MSQueue.HW.invocationIds history).Nodup) :
    MSQueue.HW.WellFormed history where
  invocationIdsNodup := noDuplicates
  returnIdsNodup := form.returnIdsNodup noDuplicates
  returnHasInvocation := form.returnHasInvocation
  threadSequential firstMember secondMember sameThread before :=
    form.threadSequential noDuplicates firstMember secondMember
      sameThread before

end ClientForm

theorem threadProjectionWellFormed
    {history : MSQueue.HW.History Value}
    (forms : ∀ thread,
      ClientForm (MSQueue.HW.eventsForThread thread history))
    (globalNodup : (MSQueue.HW.invocationIds history).Nodup)
    (thread : ThreadId) :
    MSQueue.HW.WellFormed
      (MSQueue.HW.eventsForThread thread history) := by
  have localNodup :
      (MSQueue.HW.invocationIds
        (MSQueue.HW.eventsForThread thread history)).Nodup :=
    ((eventsForThread_sublist thread history).filterMap
      MSQueue.HW.HistoryEvent.invocationId?).nodup globalNodup
  exact (forms thread).wellFormed localNodup

theorem globalReturnHasInvocation
    {history : MSQueue.HW.History Value}
    (forms : ∀ thread,
      ClientForm (MSQueue.HW.eventsForThread thread history))
    (globalNodup : (MSQueue.HW.invocationIds history).Nodup)
    {returned : MSQueue.HW.Return Value}
    (member : MSQueue.HW.HistoryEvent.respond returned ∈ history) :
    ∃ invocation,
      MSQueue.HW.Matches invocation returned ∧
        HerlihyWing.Before (.invoke invocation) (.respond returned) history := by
  have projectedMember :
      MSQueue.HW.HistoryEvent.respond returned ∈
        MSQueue.HW.eventsForThread returned.thread history :=
    MSQueue.HW.mem_eventsForThread.mpr ⟨member, rfl⟩
  obtain ⟨invocation, matching, before⟩ :=
    (threadProjectionWellFormed forms globalNodup
      returned.thread).returnHasInvocation projectedMember
  exact ⟨invocation, matching, before_of_eventsForThread before⟩

theorem globalReturnIdsNodup
    {history : MSQueue.HW.History Value}
    (forms : ∀ thread,
      ClientForm (MSQueue.HW.eventsForThread thread history))
    (globalNodup : (MSQueue.HW.invocationIds history).Nodup) :
    (MSQueue.HW.returnIds history).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  change List.Pairwise (fun first second => first ≠ second)
    (history.filterMap MSQueue.HW.HistoryEvent.returnId?)
  rw [List.pairwise_filterMap]
  apply List.pairwise_of_forall_sublist
  intro firstEvent secondEvent ordered
  intro firstId firstExtracts secondId secondExtracts
  cases firstEvent with
  | invoke invocation =>
      simp [MSQueue.HW.HistoryEvent.returnId?] at firstExtracts
  | respond firstReturned =>
      cases secondEvent with
      | invoke invocation =>
          simp [MSQueue.HW.HistoryEvent.returnId?] at secondExtracts
      | respond secondReturned =>
          have firstIdShape : firstReturned.id = firstId := by
            simpa [MSQueue.HW.HistoryEvent.returnId?] using
              Option.some.inj firstExtracts
          have secondIdShape : secondReturned.id = secondId := by
            simpa [MSQueue.HW.HistoryEvent.returnId?] using
              Option.some.inj secondExtracts
          subst firstId
          subst secondId
          intro sameReturnId
          have responseBefore :
              HerlihyWing.Before (.respond firstReturned)
                (.respond secondReturned) history :=
            before_iff_pair_sublist.mpr ordered
          obtain ⟨firstInvocation, firstMatches,
              firstInvocationBefore⟩ :=
            globalReturnHasInvocation forms globalNodup
              responseBefore.first_mem
          obtain ⟨secondInvocation, secondMatches,
              secondInvocationBefore⟩ :=
            globalReturnHasInvocation forms globalNodup
              responseBefore.second_mem
          have invocationIdsSame :
              secondInvocation.id = firstInvocation.id :=
            secondMatches.2.trans
              (sameReturnId.symm.trans firstMatches.2.symm)
          have invocationEventsSame :
              (MSQueue.HW.HistoryEvent.invoke firstInvocation) =
                .invoke secondInvocation := by
            apply eq_of_filterMap_nodup globalNodup
              firstInvocationBefore.first_mem
              secondInvocationBefore.first_mem rfl
            simp [MSQueue.HW.HistoryEvent.invocationId?,
              invocationIdsSame]
          have invocationsSame : firstInvocation = secondInvocation := by
            injection invocationEventsSame
          have sameReturnedThread :
              firstReturned.thread = secondReturned.thread := by
            calc
              firstReturned.thread = firstInvocation.thread :=
                firstMatches.1.symm
              _ = secondInvocation.thread := by rw [invocationsSame]
              _ = secondReturned.thread := secondMatches.1
          have projectedBefore :
              HerlihyWing.Before (.respond firstReturned)
                (.respond secondReturned)
                (MSQueue.HW.eventsForThread
                  firstReturned.thread history) :=
            before_eventsForThread responseBefore rfl
              sameReturnedThread.symm
          have projectedIdBefore :
              HerlihyWing.Before firstReturned.id secondReturned.id
                (MSQueue.HW.returnIds
                  (MSQueue.HW.eventsForThread
                    firstReturned.thread history)) :=
            before_filterMap projectedBefore rfl rfl
          exact
            (before_endpoints_ne
              (threadProjectionWellFormed forms globalNodup
                firstReturned.thread).returnIdsNodup
              projectedIdBefore) sameReturnId

theorem ofThreadForms
    {history : MSQueue.HW.History Value}
    (forms : ∀ thread,
      ClientForm (MSQueue.HW.eventsForThread thread history))
    (globalNodup : (MSQueue.HW.invocationIds history).Nodup) :
    MSQueue.HW.WellFormed history where
  invocationIdsNodup := globalNodup
  returnIdsNodup := globalReturnIdsNodup forms globalNodup
  returnHasInvocation member :=
    globalReturnHasInvocation forms globalNodup member
  threadSequential
      {first} {second} firstMember secondMember sameThread before := by
    have firstProjected :
        MSQueue.HW.HistoryEvent.invoke first ∈
          MSQueue.HW.eventsForThread first.thread history :=
      MSQueue.HW.mem_eventsForThread.mpr ⟨firstMember, rfl⟩
    have secondProjected :
        MSQueue.HW.HistoryEvent.invoke second ∈
          MSQueue.HW.eventsForThread first.thread history :=
      MSQueue.HW.mem_eventsForThread.mpr
        ⟨secondMember, sameThread.symm⟩
    have projectedBefore :
        HerlihyWing.Before (.invoke first) (.invoke second)
          (MSQueue.HW.eventsForThread first.thread history) :=
      before_eventsForThread before rfl sameThread.symm
    obtain ⟨returned, matching, invocationBeforeReturn,
        returnBeforeInvocation⟩ :=
      (threadProjectionWellFormed forms globalNodup
        first.thread).threadSequential
          firstProjected secondProjected sameThread projectedBefore
    exact ⟨returned, matching,
      before_of_eventsForThread invocationBeforeReturn,
      before_of_eventsForThread returnBeforeInvocation⟩

end HistoryWellFormed

namespace SourceWellFormed

/-- Every thread projection of a checked source trace is well bracketed. -/
theorem threadClientForm
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace)
    (thread : ThreadId) :
    HistoryWellFormed.ClientForm
      (MSQueue.HW.eventsForThread thread (sourceHistory trace)) := by
  obtain ⟨_, sourceRun⟩ := wellFormed.threadRuns thread
  obtain ⟨methodFinal, methodExecution, _⟩ :=
    sourceRun.toIdleMethodExecution
  have projectedExecution :
      MethodTrace.Execution .idle
        (MethodTrace.eventsForThread thread
          (MethodTrace.eventsFrom trace)) methodFinal := by
    rw [MethodTrace.eventsForThread_eventsFrom]
    exact methodExecution
  have form := HistoryWellFormed.clientForm_of_threadForm
    projectedExecution.toThreadForm
  rw [MethodTrace.history_eventsForThread,
    MethodTrace.history_eventsFrom] at form
  exact form

/-- A checked source run produces a structurally well-formed HW history. -/
theorem historyWellFormed
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    (wellFormed : SourceWellFormed dummy trace) :
    MSQueue.HW.WellFormed (sourceHistory trace) := by
  apply HistoryWellFormed.ofThreadForms
  · exact wellFormed.threadClientForm
  · rw [invocationIds_sourceHistory]
    exact wellFormed.invocationIdsNodup

end SourceWellFormed

end WeakMemory.MSQueue.Source
