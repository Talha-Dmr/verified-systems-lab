import WeakMemory.MSQueueSourceSchedule

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Scheduled RC11 visibility facts for the Michael--Scott refinement

These lemmas are the memory-order kernel needed by the future prefix
representation invariant.  In a schedule respecting extended coherence, a
read occurs after its RF source and before every distinct write that follows
that source in modification order.
-/

namespace AtomSchedule

/-- Every structural linearization point has an actual reads-from source in
the exact source-backed candidate. -/
theorem pointReadsFrom
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    ∃ source,
      MultiLocationRC11.RF execution.candidate source record.pointAtom :=
  execution.valid.toWellFormed.everyRead_hasSource
    (pointAtom_mem_candidate (execution := execution) member)
    (pointAtom_isRead_of_structuralRecord member)

theorem readsFrom_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source target : MultiLocationRC11.Atom Site Ptr}
    (readsFrom : MultiLocationRC11.RF execution.candidate source target) :
    MultiLocationRC11.IdBefore source.id target.id schedule.ids :=
  schedule.respectsExtendedCoherence
    (.readsFrom readsFrom)

theorem modificationOrder_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source target : MultiLocationRC11.Atom Site Ptr}
    (modificationOrder :
      MultiLocationRC11.MO execution.candidate source target) :
    MultiLocationRC11.IdBefore source.id target.id schedule.ids :=
  schedule.respectsExtendedCoherence
    (.modificationOrder modificationOrder)

theorem readsBefore_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source target : MultiLocationRC11.Atom Site Ptr}
    (readsBefore : MultiLocationRC11.RB execution.candidate source target) :
    MultiLocationRC11.IdBefore source.id target.id schedule.ids :=
  schedule.respectsExtendedCoherence
    (.readsBefore readsBefore)

/--
No write that is MO-later than an RF source can already occur before the read.
For a distinct write this is exactly the `rb` edge; for an RMW read considered
as its own later write, strict schedule order is irreflexive.
-/
theorem no_modificationOrderLater_before_read
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source read laterWrite : MultiLocationRC11.Atom Site Ptr}
    (readsFrom :
      MultiLocationRC11.RF execution.candidate source read)
    (modificationOrder :
      MultiLocationRC11.MO execution.candidate source laterWrite) :
    ¬ MultiLocationRC11.IdBefore laterWrite.id read.id schedule.ids := by
  intro laterBeforeRead
  by_cases same : read = laterWrite
  · subst laterWrite
    exact MultiLocationRC11.IdBefore.irreflexive laterBeforeRead
  · have readBeforeLater :
        MultiLocationRC11.IdBefore read.id laterWrite.id schedule.ids :=
      schedule.readsBefore_before
        ⟨source, readsFrom, modificationOrder, same⟩
    have cycle := MultiLocationRC11.IdBefore.transitive
      laterBeforeRead readBeforeLater
    exact MultiLocationRC11.IdBefore.irreflexive cycle

/-- A compact scheduled latest-source certificate for one RC11 read. -/
structure LatestSource
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    (source read : MultiLocationRC11.Atom Site Ptr) : Prop where
  readsFrom : MultiLocationRC11.RF execution.candidate source read
  sourceBefore :
    MultiLocationRC11.IdBefore source.id read.id schedule.ids
  noLaterBefore :
    ∀ {laterWrite},
      MultiLocationRC11.MO execution.candidate source laterWrite →
        ¬ MultiLocationRC11.IdBefore laterWrite.id read.id schedule.ids

theorem latestSource_of_readsFrom
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source read : MultiLocationRC11.Atom Site Ptr}
    (readsFrom : MultiLocationRC11.RF execution.candidate source read) :
    LatestSource schedule source read where
  readsFrom := readsFrom
  sourceBefore := schedule.readsFrom_before readsFrom
  noLaterBefore := fun modificationOrder =>
    schedule.no_modificationOrderLater_before_read
      readsFrom modificationOrder

/-- Every structural point therefore has a scheduled MO-latest RF source. -/
theorem pointLatestSource
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {record : Record Value}
    (member : record ∈ structuralRecords trace) :
    ∃ source, LatestSource schedule source record.pointAtom := by
  obtain ⟨source, readsFrom⟩ :=
    pointReadsFrom (execution := execution) member
  exact ⟨source, schedule.latestSource_of_readsFrom readsFrom⟩

/--
Among writes already scheduled before a read, its RF source is MO-latest.
Any other same-location write must be modification-order earlier.
-/
theorem rfSource_latest_before
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    (schedule : AtomSchedule execution)
    {source read write : MultiLocationRC11.Atom Site Ptr}
    (readsFrom : MultiLocationRC11.RF execution.candidate source read)
    (writeMember : write ∈ execution.candidate.atoms)
    (writeIsWrite : write.IsWrite)
    (sameLocation : write.location = read.location)
    (writeBeforeRead :
      MultiLocationRC11.IdBefore write.id read.id schedule.ids) :
    write = source ∨
      MultiLocationRC11.MO execution.candidate write source := by
  by_cases same : write = source
  · exact Or.inl same
  · right
    have writeSourceLocation : write.location = source.location :=
      sameLocation.trans readsFrom.sameLocation.symm
    rcases execution.valid.toWellFormed.modificationOrder_total
        writeMember readsFrom.closed.1 writeIsWrite
        readsFrom.2.2.1 writeSourceLocation with
      equal | writeBeforeSource | sourceBeforeWrite
    · exact (same equal).elim
    · exact writeBeforeSource
    · have readNeWrite : read ≠ write := by
        intro equal
        subst write
        exact MultiLocationRC11.IdBefore.irreflexive writeBeforeRead
      have readBeforeWrite :
          MultiLocationRC11.IdBefore read.id write.id schedule.ids :=
        schedule.readsBefore_before
          ⟨source, readsFrom, sourceBeforeWrite, readNeWrite⟩
      have cycle := MultiLocationRC11.IdBefore.transitive
        writeBeforeRead readBeforeWrite
      exact (MultiLocationRC11.IdBefore.irreflexive cycle).elim

/-- Successful source CAS reads come from their immediate MO predecessor. -/
theorem immediatePredecessor_of_readsFrom_rmw
    {Value : Type}
    {dummy : NodeId}
    {trace : List (TraceEvent Value)}
    {execution : SupportedExecution (Value := Value) dummy trace}
    {source rmw : MultiLocationRC11.Atom Site Ptr}
    (readsFrom : MultiLocationRC11.RF execution.candidate source rmw)
    (isRMW : rmw.IsRMW) :
    MultiLocationRC11.ImmediateMO execution.candidate source rmw :=
  execution.valid.rmwReadsImmediatePredecessor readsFrom isRMW

end AtomSchedule

end WeakMemory.MSQueue.Source.Structural
