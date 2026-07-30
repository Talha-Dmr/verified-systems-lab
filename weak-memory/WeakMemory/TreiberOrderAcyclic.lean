import WeakMemory.TreiberSchedule

namespace WeakMemory.TreiberRC11

/-!
# Deriving schedule acyclicity from single-location coherence

For the current Treiber event universe, the explicit scheduling acyclicity
condition is a consequence of well-formedness and RC11 coherence.

Every event is assigned an anchor write:

* a write anchors itself;
* a read-only event anchors the unique write from which it reads.

Modification order compares the anchors. At a fixed anchor, the write is
strictly before its read-only observers. Extended coherence strictly increases
this rank, while coherence prevents happens-before from decreasing it.
-/

namespace SchedulingRank

/--
Choose the reads-from source of an event when one exists. The fallback branch
is used only outside well-formed graph carriers.
-/
noncomputable def readSource (graph : Graph α) (event : Event α) : Event α :=
  by
    classical
    exact if sources : ∃ source, graph.readsFrom source event then
      Classical.choose sources
    else
      event

/--
A write anchors itself; a read-only event anchors at its reads-from source.
-/
noncomputable def anchor (graph : Graph α) (event : Event α) : Event α :=
  by
    classical
    exact if event.IsWrite then event else readSource graph event

/--
Strict lexicographic order by anchor modification-order position and then by
the write-before-reader phase at one anchor.
-/
def Lt (graph : Graph α) (source target : Event α) : Prop :=
  graph.modificationOrder
      (anchor graph source) (anchor graph target) ∨
    (anchor graph source = anchor graph target ∧
      source.IsWrite ∧ ¬ target.IsWrite)

/-- Equal scheduling rank: equal anchors and equal write/read phases. -/
def Eqv (graph : Graph α) (source target : Event α) : Prop :=
  anchor graph source = anchor graph target ∧
    (source.IsWrite ↔ target.IsWrite)

/-- Nonstrict scheduling-rank order. -/
def Le (graph : Graph α) (source target : Event α) : Prop :=
  Lt graph source target ∨ Eqv graph source target

private theorem event_read_or_write (event : Event α) :
    event.IsRead ∨ event.IsWrite := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          exact Or.inr ⟨none, rfl⟩
      | algorithm action =>
          cases action <;> exact Or.inl ⟨_, rfl⟩

private theorem read_write_isRMW
    {event : Event α}
    (reads : event.IsRead)
    (writes : event.IsWrite) :
    event.IsRMW := by
  cases event with
  | mk id kind =>
      cases kind with
      | initial =>
          rcases reads with ⟨value, reads⟩
          simp [Event.readValue] at reads
      | algorithm action =>
          cases action <;>
            simp [Event.IsRMW, Event.IsWrite, Event.writtenValue]
              at writes ⊢

private theorem readsFrom_source_writes
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (readsFrom : graph.readsFrom source target) :
    source.IsWrite := by
  obtain ⟨value, sourceWrites, _⟩ :=
    wellFormed.readsFromValues readsFrom
  exact ⟨value, sourceWrites⟩

private theorem readsFrom_target_reads
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (readsFrom : graph.readsFrom source target) :
    target.IsRead := by
  obtain ⟨value, _, targetReads⟩ :=
    wellFormed.readsFromValues readsFrom
  exact ⟨value, targetReads⟩

private theorem readSource_readsFrom
    {graph : Graph α}
    {event : Event α}
    (hasSource : ∃ source, graph.readsFrom source event) :
    graph.readsFrom (readSource graph event) event := by
  classical
  simp only [readSource, dif_pos hasSource]
  exact Classical.choose_spec hasSource

private theorem anchor_eq_self
    {graph : Graph α}
    {event : Event α}
    (writes : event.IsWrite) :
    anchor graph event = event := by
  simp [anchor, writes]

private theorem anchor_readsFrom
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {event : Event α}
    (member : event ∈ graph.events)
    (doesNotWrite : ¬ event.IsWrite) :
    graph.readsFrom (anchor graph event) event := by
  have reads : event.IsRead :=
    (event_read_or_write event).resolve_right doesNotWrite
  obtain ⟨source, readsFrom⟩ :=
    wellFormed.everyReadHasSource member reads
  have hasSource : ∃ source, graph.readsFrom source event :=
    ⟨source, readsFrom⟩
  simpa [anchor, doesNotWrite] using
    readSource_readsFrom hasSource

private theorem anchor_writes
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {event : Event α}
    (member : event ∈ graph.events) :
    (anchor graph event).IsWrite := by
  by_cases writes : event.IsWrite
  · simpa [anchor_eq_self writes] using writes
  · exact readsFrom_source_writes wellFormed
      (anchor_readsFrom wellFormed member writes)

private theorem anchor_member
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {event : Event α}
    (member : event ∈ graph.events) :
    anchor graph event ∈ graph.events := by
  by_cases writes : event.IsWrite
  · simpa [anchor_eq_self writes] using member
  · exact (wellFormed.readsFromClosed
      (anchor_readsFrom wellFormed member writes)).1

private theorem anchor_eq_readsFrom_source
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (targetMember : target ∈ graph.events)
    (readsFrom : graph.readsFrom source target)
    (targetDoesNotWrite : ¬ target.IsWrite) :
    anchor graph target = source := by
  exact wellFormed.readsFromFunctional
    (anchor_readsFrom wellFormed targetMember targetDoesNotWrite)
    readsFrom

private theorem lt_irreflexive
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (event : Event α) :
    ¬ Lt graph event event := by
  intro beforeSelf
  rcases beforeSelf with modificationOrder | sameAnchor
  · exact wellFormed.modificationOrderIrreflexive
      (anchor graph event) modificationOrder
  · exact sameAnchor.2.2 sameAnchor.2.1

private theorem lt_transitive
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {first middle last : Event α}
    (firstBefore : Lt graph first middle)
    (secondBefore : Lt graph middle last) :
    Lt graph first last := by
  rcases firstBefore with firstMO | firstPhase
  · rcases secondBefore with secondMO | secondPhase
    · exact Or.inl
        (wellFormed.modificationOrderTransitive firstMO secondMO)
    · exact Or.inl (secondPhase.1 ▸ firstMO)
  · rcases secondBefore with secondMO | secondPhase
    · exact Or.inl (firstPhase.1 ▸ secondMO)
    · exact (secondPhase.2.1 |> firstPhase.2.2).elim

private theorem eqv_refl
    {graph : Graph α}
    (event : Event α) :
    Eqv graph event event :=
  ⟨rfl, Iff.rfl⟩

private theorem eqv_transitive
    {graph : Graph α}
    {first middle last : Event α}
    (firstSame : Eqv graph first middle)
    (secondSame : Eqv graph middle last) :
    Eqv graph first last :=
  ⟨firstSame.1.trans secondSame.1,
    firstSame.2.trans secondSame.2⟩

private theorem lt_eqv_trans
    {graph : Graph α}
    {first middle last : Event α}
    (firstBefore : Lt graph first middle)
    (secondSame : Eqv graph middle last) :
    Lt graph first last := by
  rcases firstBefore with firstMO | firstPhase
  · exact Or.inl (secondSame.1 ▸ firstMO)
  · refine Or.inr ⟨firstPhase.1.trans secondSame.1, firstPhase.2.1, ?_⟩
    intro lastWrites
    exact firstPhase.2.2 (secondSame.2.mpr lastWrites)

private theorem eqv_lt_trans
    {graph : Graph α}
    {first middle last : Event α}
    (firstSame : Eqv graph first middle)
    (secondBefore : Lt graph middle last) :
    Lt graph first last := by
  rcases secondBefore with secondMO | secondPhase
  · exact Or.inl (firstSame.1 ▸ secondMO)
  · refine Or.inr ⟨firstSame.1.trans secondPhase.1,
      firstSame.2.mpr secondPhase.2.1, secondPhase.2.2⟩

private theorem le_transitive
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {first middle last : Event α}
    (firstBefore : Le graph first middle)
    (secondBefore : Le graph middle last) :
    Le graph first last := by
  rcases firstBefore with firstLt | firstEqv
  · rcases secondBefore with secondLt | secondEqv
    · exact Or.inl (lt_transitive wellFormed firstLt secondLt)
    · exact Or.inl (lt_eqv_trans firstLt secondEqv)
  · rcases secondBefore with secondLt | secondEqv
    · exact Or.inl (eqv_lt_trans firstEqv secondLt)
    · exact Or.inr (eqv_transitive firstEqv secondEqv)

private theorem lt_le_trans
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {first middle last : Event α}
    (firstBefore : Lt graph first middle)
    (secondBefore : Le graph middle last) :
    Lt graph first last := by
  rcases secondBefore with secondLt | secondEqv
  · exact lt_transitive wellFormed firstBefore secondLt
  · exact lt_eqv_trans firstBefore secondEqv

private theorem le_lt_trans
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {first middle last : Event α}
    (firstBefore : Le graph first middle)
    (secondBefore : Lt graph middle last) :
    Lt graph first last := by
  rcases firstBefore with firstLt | firstEqv
  · exact lt_transitive wellFormed firstLt secondBefore
  · exact eqv_lt_trans firstEqv secondBefore

private theorem anchor_before_event
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {event : Event α}
    (member : event ∈ graph.events) :
    anchor graph event = event ∨
      graph.readsFrom (anchor graph event) event := by
  by_cases writes : event.IsWrite
  · exact Or.inl (anchor_eq_self writes)
  · exact Or.inr (anchor_readsFrom wellFormed member writes)

private theorem event_before_laterAnchor
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {event later : Event α}
    (eventMember : event ∈ graph.events)
    (laterWrites : later.IsWrite)
    (anchorBefore :
      graph.modificationOrder (anchor graph event) later) :
    graph.ExtendedCoherence event later := by
  by_cases eventWrites : event.IsWrite
  · have eventIsAnchor :=
      anchor_eq_self (graph := graph) eventWrites
    exact Graph.ExtendedCoherence.modificationOrder
      (eventIsAnchor ▸ anchorBefore)
  · apply Graph.ExtendedCoherence.readsBefore
    refine ⟨anchor graph event,
      anchor_readsFrom wellFormed eventMember eventWrites,
      anchorBefore, ?_⟩
    intro eventIsLater
    subst event
    exact eventWrites laterWrites

private theorem earlierAnchor_before_event
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {earlier event : Event α}
    (eventMember : event ∈ graph.events)
    (earlierBefore :
      graph.modificationOrder earlier (anchor graph event)) :
    graph.ExtendedCoherence earlier event := by
  rcases anchor_before_event wellFormed eventMember with
      anchorIsEvent | anchorReadsFrom
  · exact Graph.ExtendedCoherence.modificationOrder
      (anchorIsEvent ▸ earlierBefore)
  · exact Graph.ExtendedCoherence.transitive
      (Graph.ExtendedCoherence.modificationOrder earlierBefore)
      (Graph.ExtendedCoherence.readsFrom anchorReadsFrom)

private theorem lt_to_extendedCoherence
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (sourceMember : source ∈ graph.events)
    (targetMember : target ∈ graph.events)
    (before : Lt graph source target) :
    graph.ExtendedCoherence source target := by
  rcases before with anchorMO | sameAnchor
  · have sourceToAnchor :=
      event_before_laterAnchor wellFormed sourceMember
        (anchor_writes wellFormed targetMember) anchorMO
    rcases anchor_before_event wellFormed targetMember with
        anchorIsTarget | anchorReadsFrom
    · simpa [anchorIsTarget] using sourceToAnchor
    · exact Graph.ExtendedCoherence.transitive sourceToAnchor
        (Graph.ExtendedCoherence.readsFrom anchorReadsFrom)
  · have sourceIsAnchor :=
      anchor_eq_self (graph := graph) sameAnchor.2.1
    have anchorReadsFrom :=
      anchor_readsFrom wellFormed targetMember sameAnchor.2.2
    have targetAnchorIsSource :
        anchor graph target = source :=
      sameAnchor.1.symm.trans sourceIsAnchor
    exact Graph.ExtendedCoherence.readsFrom
      (targetAnchorIsSource ▸ anchorReadsFrom)

private theorem readsBefore_rankLt
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {read laterWrite : Event α}
    (readsBefore : graph.ReadsBefore read laterWrite) :
    Lt graph read laterWrite := by
  rcases readsBefore with
    ⟨source, readsFrom, sourceBeforeLater, readNotLater⟩
  have endpoints := wellFormed.readsFromClosed readsFrom
  have laterEndpoints :=
    wellFormed.modificationOrderClosed sourceBeforeLater
  have laterWrites :=
    (wellFormed.modificationOrderWrites sourceBeforeLater).2
  have laterIsAnchor :=
    anchor_eq_self (graph := graph) laterWrites
  by_cases readWrites : read.IsWrite
  · have readReads := readsFrom_target_reads wellFormed readsFrom
    have readRMW := read_write_isRMW readReads readWrites
    have readIsAnchor :=
      anchor_eq_self (graph := graph) readWrites
    have sourceBeforeRead :=
      wellFormed.rmw_source_precedes readsFrom readRMW
    have readBeforeLater :
        graph.modificationOrder read laterWrite := by
      rcases wellFormed.modificationOrderTotal
          endpoints.2 laterEndpoints.2 readWrites laterWrites readNotLater with
        readBefore | laterBefore
      · exact readBefore
      · exact (wellFormed.rmw_hasNoInterveningWrite
          readsFrom readRMW laterEndpoints.2 laterWrites
          ⟨sourceBeforeLater, laterBefore⟩).elim
    exact Or.inl (by
      simpa [readIsAnchor, laterIsAnchor] using readBeforeLater)
  · have readAnchor :=
      anchor_eq_readsFrom_source wellFormed endpoints.2
        readsFrom readWrites
    exact Or.inl (by
      simpa [readAnchor, laterIsAnchor] using sourceBeforeLater)

private theorem extendedCoherence_rankLt
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (edge : graph.ExtendedCoherence source target) :
    Lt graph source target := by
  induction edge with
  | @readsFrom source target readsFrom =>
      have endpoints := wellFormed.readsFromClosed readsFrom
      have sourceWrites :=
        readsFrom_source_writes wellFormed readsFrom
      have sourceIsAnchor :=
        anchor_eq_self (graph := graph) sourceWrites
      by_cases targetWrites : target.IsWrite
      · have targetReads :=
          readsFrom_target_reads wellFormed readsFrom
        have targetRMW :=
          read_write_isRMW targetReads targetWrites
        have targetIsAnchor :=
          anchor_eq_self (graph := graph) targetWrites
        exact Or.inl (by
          simpa [sourceIsAnchor, targetIsAnchor] using
            wellFormed.rmw_source_precedes readsFrom targetRMW)
      · have targetAnchor :=
          anchor_eq_readsFrom_source wellFormed endpoints.2
            readsFrom targetWrites
        exact Or.inr ⟨sourceIsAnchor.trans targetAnchor.symm,
          sourceWrites, targetWrites⟩
  | @modificationOrder source target modificationOrder =>
      have writes :=
        wellFormed.modificationOrderWrites modificationOrder
      exact Or.inl (by
        simpa [anchor_eq_self writes.1, anchor_eq_self writes.2] using
          modificationOrder)
  | @readsBefore read laterWrite readsBefore =>
      exact readsBefore_rankLt wellFormed readsBefore
  | transitive first second firstBefore secondBefore =>
      exact lt_transitive wellFormed firstBefore secondBefore

private theorem rank_trichotomy
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    {source target : Event α}
    (sourceMember : source ∈ graph.events)
    (targetMember : target ∈ graph.events) :
    Lt graph source target ∨
      Eqv graph source target ∨
      Lt graph target source := by
  classical
  by_cases sameAnchor :
      anchor graph source = anchor graph target
  · by_cases sourceWrites : source.IsWrite
    · by_cases targetWrites : target.IsWrite
      · exact Or.inr (Or.inl
          ⟨sameAnchor, by simp [sourceWrites, targetWrites]⟩)
      · exact Or.inl (Or.inr
          ⟨sameAnchor, sourceWrites, targetWrites⟩)
    · by_cases targetWrites : target.IsWrite
      · exact Or.inr (Or.inr (Or.inr
          ⟨sameAnchor.symm, targetWrites, sourceWrites⟩))
      · exact Or.inr (Or.inl
          ⟨sameAnchor, by simp [sourceWrites, targetWrites]⟩)
  · have sourceAnchorMember :=
      anchor_member wellFormed sourceMember
    have targetAnchorMember :=
      anchor_member wellFormed targetMember
    have sourceAnchorWrites :=
      anchor_writes wellFormed sourceMember
    have targetAnchorWrites :=
      anchor_writes wellFormed targetMember
    rcases wellFormed.modificationOrderTotal
        sourceAnchorMember targetAnchorMember
        sourceAnchorWrites targetAnchorWrites sameAnchor with
      sourceBefore | targetBefore
    · exact Or.inl (Or.inl sourceBefore)
    · exact Or.inr (Or.inr (Or.inl targetBefore))

private theorem happensBefore_rankLe
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (coherent : graph.Coherent)
    {source target : Event α}
    (happensBefore : graph.HappensBefore source target) :
    Le graph source target := by
  have endpoints : source ∈ graph.events ∧ target ∈ graph.events := by
    induction happensBefore with
    | programOrder programOrder =>
        exact wellFormed.programOrderClosed programOrder
    | synchronizesWith synchronizesWith =>
        rcases synchronizesWith with
          ⟨rfSource, sequence, readsFrom, _, _⟩
        exact ⟨sequence.headMember,
          (wellFormed.readsFromClosed readsFrom).2⟩
    | transitive first second firstClosed secondClosed =>
        exact ⟨firstClosed.1, secondClosed.2⟩
  rcases rank_trichotomy wellFormed endpoints.1 endpoints.2 with
      forward | sameOrBackward
  · exact Or.inl forward
  · rcases sameOrBackward with same | backward
    · exact Or.inr same
    · exact ((coherent happensBefore).2
        (lt_to_extendedCoherence wellFormed
          endpoints.2 endpoints.1 backward)).elim

private theorem orderPath_happensBefore_or_rankLt
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (coherent : graph.Coherent)
    {source target : Event α}
    (path : Relation.TransGen graph.OrderEdge source target) :
    graph.HappensBefore source target ∨
      Lt graph source target := by
  induction path with
  | single edge =>
      rcases edge with programOrder | extendedCoherence
      · exact Or.inl
          (Graph.HappensBefore.programOrder programOrder)
      · exact Or.inr
          (extendedCoherence_rankLt wellFormed extendedCoherence)
  | tail path edge inductionHypothesis =>
      rcases inductionHypothesis with happensBefore | rankBefore
      · rcases edge with programOrder | extendedCoherence
        · exact Or.inl (Graph.HappensBefore.transitive
            happensBefore
            (Graph.HappensBefore.programOrder programOrder))
        · exact Or.inr (le_lt_trans wellFormed
            (happensBefore_rankLe wellFormed coherent happensBefore)
            (extendedCoherence_rankLt wellFormed extendedCoherence))
      · rcases edge with programOrder | extendedCoherence
        · exact Or.inr (lt_le_trans wellFormed rankBefore
            (happensBefore_rankLe wellFormed coherent
              (Graph.HappensBefore.programOrder programOrder)))
        · exact Or.inr (lt_transitive wellFormed rankBefore
            (extendedCoherence_rankLt wellFormed extendedCoherence))

end SchedulingRank

/--
In the current single-location Treiber model, well-formedness and RC11
coherence imply acyclicity of the combined replay scheduling order.
-/
theorem orderAcyclic_of_wellFormed_coherent
    {graph : Graph α}
    (wellFormed : WellFormed graph)
    (coherent : graph.Coherent) :
    graph.OrderAcyclic := by
  intro event cycle
  rcases SchedulingRank.orderPath_happensBefore_or_rankLt
      wellFormed coherent cycle with
    happensBefore | rankBefore
  · exact (coherent happensBefore).1 rfl
  · exact SchedulingRank.lt_irreflexive wellFormed event rankBefore

namespace CoreConsistent

/--
Core consistency discharges the scheduling acyclicity premise used by the
finite topological-schedule construction.
-/
theorem orderAcyclic
    {graph : Graph α}
    (consistent : CoreConsistent graph) :
    graph.OrderAcyclic :=
  orderAcyclic_of_wellFormed_coherent
    consistent.toWellFormed
    consistent.coherence

end CoreConsistent

end WeakMemory.TreiberRC11
