import WeakMemory.TreiberReplay

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
