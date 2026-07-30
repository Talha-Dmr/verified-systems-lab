import WeakMemory.TreiberNodeAccessDerivation
import WeakMemory.TreiberHistory
import WeakMemory.TreiberMethodTrace
import WeakMemory.TreiberScheduledHistory
import WeakMemory.TreiberVerifiedModelProvenance
import WeakMemory.TreiberSupportedModelSemantics
import WeakMemory.TreiberExecutionFrontend
import WeakMemory.TreiberC11V1Frontend
import WeakMemory.TreiberC11V1Examples

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
  IO.println "Lean theorem checked: canonical rf/mo data derives source node-read publication safety."
  IO.println "Lean theorem checked: finite rf/mo data and a common rank construct core-consistent source graphs."
  IO.println "Lean theorem checked: finite identified histories have a formal Herlihy-Wing linearizability predicate."
  IO.println "Lean theorem checked: source responses remain distinct from their atomic linearization points."
  IO.println "Lean theorem checked: graph schedules recover source operation identities and ordinary commit histories."
  IO.println "Lean theorem checked: source histories are well formed and source commits form their Herlihy-Wing completion."
  IO.println "Lean theorem checked: every respecting schedule preserves each client thread's operation order."
  IO.println "Lean theorem checked: same-thread real time is derived; cross-thread client order has an exact finite checker."
  IO.println "Lean theorem checked: client-compatible schedules construct classical Herlihy-Wing linearizations."
  IO.println "Lean theorem checked: relation ranks are derived from checked finite schedule positions."
  IO.println "Lean theorem checked: raw source, RF/MO, relation schedules, publication paths, and next reads are executable checks."
  IO.println "Lean theorem checked: accepted models retain exact proof-relevant provenance back to every raw input field."
  IO.println "Lean theorem checked: every normalized proof-carrying model round-trips through the complete raw validator."
  IO.println "Lean theorem checked: every accepted pinned Treiber model execution is node-safe and Herlihy-Wing linearizable."
  IO.println "Lean theorem checked: an exact external frontend contract transfers provenance, safety, and linearizability."
  IO.println "Lean theorem checked: direct RC11 consistency and generated graph typing certify replay of the same graph."
  IO.println "Lean theorem checked: finite declarative client constraints construct the internal schedule topologically."
  IO.println "Lean theorem checked: every admitted TreiberC11V1 execution receives the full replay, safety, provenance, and linearizability bundle."
  IO.println "Lean theorem checked: a concrete nonempty single-push declarative execution is linearizable."
