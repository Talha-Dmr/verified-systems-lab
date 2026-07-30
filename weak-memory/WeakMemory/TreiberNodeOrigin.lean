import WeakMemory.TreiberNodeAccessSource

namespace WeakMemory.TreiberRC11

/-!
# Origin of non-null head values

Every non-null pointer written to the atomic head ultimately originates at the
unique successful push that allocated that node. A pop may re-expose an older
node, so the immediate writer need not be that publisher.

The proof follows decreasing common rank. If a pop writes `node`, its popped
node was published with `next = node`; that publishing push read `node` from a
strictly lower-ranked write. No-thin-air is therefore used constructively,
rather than assuming direct reads-from from the original publisher.
-/

namespace SourceAtomicExecution

/--
For two writes in the canonical graph, strict common-rank order determines
their modification-order orientation.
-/
theorem modificationOrder_of_rank_lt
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {first second : Event α}
    (firstMember :
      first ∈ execution.relations.graph.events)
    (secondMember :
      second ∈ execution.relations.graph.events)
    (firstWrites : first.IsWrite)
    (secondWrites : second.IsWrite)
    (rankLt :
      execution.order.rank first <
        execution.order.rank second) :
    execution.relations.graph.modificationOrder first second := by
  have different : first ≠ second := by
    intro same
    subst second
    exact (Nat.lt_irrefl _) rankLt
  rcases execution.relations.modificationOrderTotal
      firstMember secondMember firstWrites secondWrites different with
    forward | backward
  · exact forward
  · exact (Nat.lt_asymm rankLt
      (execution.order.modificationOrder_lt backward)).elim

/--
The allocator publisher of `node` is either a selected write of `node` or
precedes that write in modification order.
-/
theorem allocatorPublisher_eq_or_precedes_writer
    {initial : TreiberRA.State α}
    (execution : SourceAtomicExecution initial)
    {node : TreiberRA.NodeId}
    {publisher : Event α}
    {payload : α}
    {next : Option TreiberRA.NodeId}
    (allocatorRecord :
      execution.allocator node =
        some
          (publisher,
            { value := payload, next := next }))
    {writer : Event α}
    (writerMember :
      writer ∈ execution.relations.graph.events)
    (writesNode :
      writer.writtenValue = some (some node)) :
    publisher = writer ∨
      execution.relations.graph.modificationOrder
        publisher writer := by
  let typing := execution.toGraphTyping
  have publisherSound :=
    typing.allocatorSound allocatorRecord
  have publisherMember :
      publisher ∈ execution.relations.graph.events :=
    publisherSound.1
  have publisherAllocation :
      publisher.allocation? =
        some
          (node,
            { value := payload, next := next }) :=
    publisherSound.2
  have publisherWrites : publisher.IsWrite := by
    obtain ⟨written, writtenShape⟩ :
        ∃ written,
          publisher.writtenValue = some written := by
      cases publisher with
      | mk id kind =>
          cases kind with
          | initial =>
              simp [Event.allocation?] at publisherAllocation
          | algorithm action =>
              cases action <;>
                simp [Event.allocation?, Event.writtenValue]
                  at publisherAllocation ⊢
    exact ⟨written, writtenShape⟩
  generalize rankShape :
      execution.order.rank writer = writerRank
  induction writerRank using Nat.strongRecOn generalizing writer with
  | ind writerRank inductionHypothesis =>
      cases writer with
      | mk writerId writerKind =>
          cases writerKind with
          | initial =>
              simp [Event.writtenValue] at writesNode
          | algorithm action =>
              cases action with
              | pushLoad =>
                  simp [Event.writtenValue] at writesNode
              | popLoad =>
                  simp [Event.writtenValue] at writesNode
              | isEmptyLoad =>
                  simp [Event.writtenValue] at writesNode
              | pushSuccess thread allocated value expected =>
                  simp only [Event.writtenValue,
                    Option.some.injEq] at writesNode
                  subst allocated
                  have allocation :
                      (Event.mk writerId
                        (.algorithm
                          (.pushSuccess
                            thread node value expected)) :
                        Event α).allocation? =
                        some
                          (node,
                            { value := value, next := expected }) :=
                    rfl
                  have writerRecord :=
                    (typing.eventTyped _ writerMember
                      |>.allocationRecorded allocation).2
                  have recordsEqual :
                      (publisher,
                          ({ value := payload, next := next } :
                            TreiberRA.Node α)) =
                        (Event.mk writerId
                            (.algorithm
                              (.pushSuccess
                                thread node value expected)),
                          ({ value := value, next := expected } :
                            TreiberRA.Node α)) :=
                    Option.some.inj
                      (allocatorRecord.symm.trans writerRecord)
                  exact Or.inl
                    (congrArg Prod.fst recordsEqual)
              | pushFailure =>
                  simp [Event.writtenValue] at writesNode
              | popSuccess thread popped value poppedNext =>
                  simp only [Event.writtenValue,
                    Option.some.injEq] at writesNode
                  subst poppedNext
                  have typed :=
                    typing.eventTyped _ writerMember
                  simp only [Event.TypedBy] at typed
                  obtain ⟨poppedPublisher, poppedRecord,
                      poppedPublication⟩ := typed
                  have poppedPublisherSound :=
                    typing.allocatorSound poppedRecord
                  have poppedPublisherMember :
                      poppedPublisher ∈
                        execution.relations.graph.events :=
                    poppedPublisherSound.1
                  have poppedPublisherAllocation :
                      poppedPublisher.allocation? =
                        some
                          (popped,
                            { value := value,
                              next := some node }) :=
                    poppedPublisherSound.2
                  have poppedPublisherReadsNode :
                      poppedPublisher.readValue =
                        some (some node) := by
                    cases poppedPublisher with
                    | mk id kind =>
                        cases kind with
                        | initial =>
                            simp [Event.allocation?]
                              at poppedPublisherAllocation
                        | algorithm publisherAction =>
                            cases publisherAction <;>
                              simp [Event.allocation?]
                                at poppedPublisherAllocation
                            simp [Event.readValue,
                              poppedPublisherAllocation.2.2]
                  have poppedPublisherReads :
                      poppedPublisher.IsRead :=
                    ⟨some node, poppedPublisherReadsNode⟩
                  have wellFormed :
                      WellFormed execution.relations.graph :=
                    execution.toCoreConsistent.toWellFormed
                  obtain ⟨earlierWriter, earlierReadsFrom⟩ :=
                    wellFormed.everyReadHasSource
                      poppedPublisherMember
                      poppedPublisherReads
                  obtain ⟨readValue, earlierWrites,
                      publisherReadsValue⟩ :=
                    wellFormed.readsFromValues earlierReadsFrom
                  have readValueShape : readValue = some node :=
                    Option.some.inj
                      (publisherReadsValue.symm.trans
                        poppedPublisherReadsNode)
                  subst readValue
                  have earlierWriterMember :
                      earlierWriter ∈
                        execution.relations.graph.events :=
                    (wellFormed.readsFromClosed earlierReadsFrom).1
                  have earlierWriterRank :
                      execution.order.rank earlierWriter <
                        writerRank := by
                    rw [← rankShape]
                    exact Nat.lt_trans
                      (execution.order.readsFrom_lt
                        earlierReadsFrom)
                      (execution.order.extendedCoherence_lt
                        poppedPublication)
                  have earlierOrigin :=
                    inductionHypothesis
                      (execution.order.rank earlierWriter)
                      earlierWriterRank
                      (writer := earlierWriter)
                      earlierWriterMember
                      earlierWrites
                      rfl
                  have writerWrites :
                      (Event.mk writerId
                        (.algorithm
                          (.popSuccess
                            thread popped value (some node))) :
                        Event α).IsWrite :=
                    ⟨some node, rfl⟩
                  have earlierBeforeWriter :
                      execution.relations.graph.modificationOrder
                        earlierWriter
                        (Event.mk writerId
                          (.algorithm
                            (.popSuccess
                              thread popped value (some node)))) :=
                    execution.modificationOrder_of_rank_lt
                      earlierWriterMember writerMember
                      ⟨some node, earlierWrites⟩
                      writerWrites
                      (by
                        rw [rankShape]
                        exact earlierWriterRank)
                  rcases earlierOrigin with
                    publisherIsEarlier | publisherBeforeEarlier
                  · exact Or.inr <| by
                      rw [publisherIsEarlier]
                      exact earlierBeforeWriter
                  · exact Or.inr
                      (execution.relations.modificationOrderTransitive
                        publisherBeforeEarlier
                        earlierBeforeWriter)
              | popFailure =>
                  simp [Event.writtenValue] at writesNode
              | popEmpty =>
                  simp [Event.writtenValue] at writesNode

end SourceAtomicExecution

end WeakMemory.TreiberRC11
