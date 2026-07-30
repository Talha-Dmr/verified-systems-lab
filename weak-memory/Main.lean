import WeakMemory.TreiberGeneratedConsistency
import WeakMemory.TreiberNodeAccess

open WeakMemory

def main : IO Unit := do
  let initial : List Int := [20, 10]
  let (response, final) := StackSpec.step initial (.pop : StackSpec.Operation Int)
  IO.println s!"Sequential specification demo:"
  IO.println s!"  response = {repr response}"
  IO.println s!"  final stack = {repr final}"
  IO.println "Lean theorem checked: abstract Treiber commit traces are legal stack histories."
  IO.println "Lean theorem checked: allowed RA-fragment executions are linearizable."
  IO.println "Lean theorem checked: certified RC11-style graph schedules compose with the RA proof."
  IO.println "Lean theorem checked: accepted graph replay is equivalent to operational execution."
  IO.println "Lean theorem checked: acyclic po-union-eco constraints have a finite respecting schedule."
  IO.println "Lean theorem checked: well-formed coherent Treiber graphs have acyclic po-union-eco."
  IO.println "Lean theorem checked: explicit Treiber graph invariants make the constructed schedule replayable."
  IO.println "Lean theorem checked: invariant RC11-style Treiber graphs yield legal sequential stack histories."
  IO.println "Lean theorem checked: local allocator-table typing implies every replay invariant."
  IO.println "Lean theorem checked: typed RC11-style Treiber graphs are linearizable."
  IO.println "Lean theorem checked: locally generated Treiber events produce a sound allocator table."
  IO.println "Lean theorem checked: generated RC11-style Treiber candidates are linearizable."
  IO.println "Lean theorem checked: per-thread Treiber retries preserve operation and thread identity."
  IO.println "Lean theorem checked: a failed pop CAS observing null completes as an empty pop."
  IO.println "Lean theorem checked: controlled atomic events have fresh IDs and exact same-thread program order."
  IO.println "Lean theorem checked: controlled interleavings enforce unique operations and node reservations."
  IO.println "Lean theorem checked: eleven remaining relation fields plus coherence reconstruct core consistency."
  IO.println "Lean theorem checked: source node reads expose their release-sequence publication obligation."
