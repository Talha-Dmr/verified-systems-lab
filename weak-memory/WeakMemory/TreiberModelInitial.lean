import WeakMemory.TreiberInterleavingCheck

namespace WeakMemory.TreiberRC11

/-!
# Canonical initialized model state

`treiber_init` stores null into the atomic head.  Unpublished client-owned
nodes are intentionally absent from the model heap; a successful release push
adds their immutable payload and `next` record.
-/

namespace ModelInitial

/-- No node has yet been published into the shared stack. -/
def emptyHeap : TreiberRA.Heap α :=
  fun _ => none

/-- State immediately after the modeled `treiber_init`. -/
def initialized : TreiberRA.State α where
  heap :=
    emptyHeap
  head :=
    none

@[simp] theorem initialized_head :
    (initialized : TreiberRA.State α).head = none :=
  rfl

@[simp] theorem initialized_heap
    (node : TreiberRA.NodeId) :
    (initialized : TreiberRA.State α).heap node = none :=
  rfl

/-- The initialized concrete state represents the empty abstract stack. -/
theorem represents_empty :
    TreiberRA.Represents
      (initialized : TreiberRA.State α).heap
      (initialized : TreiberRA.State α).head
      [] :=
  .empty

end ModelInitial

end WeakMemory.TreiberRC11
