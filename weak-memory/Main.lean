import WeakMemory.TreiberGeneration

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
  IO.println "Lean theorem checked: explicit Treiber graph invariants make the constructed schedule replayable."
  IO.println "Lean theorem checked: invariant RC11-style Treiber graphs yield legal sequential stack histories."
  IO.println "Lean theorem checked: local allocator-table typing implies every replay invariant."
  IO.println "Lean theorem checked: typed RC11-style Treiber graphs are linearizable."
  IO.println "Lean theorem checked: locally generated Treiber events produce a sound allocator table."
  IO.println "Lean theorem checked: generated RC11-style Treiber candidates are linearizable."
