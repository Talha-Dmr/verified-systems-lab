import WeakMemory.TreiberC11V1Frontend
import WeakMemory.TreiberC11V1InfiniteRC11

namespace WeakMemory.TreiberC11V1

/-!
# Reusing finite safety for every infinite-execution prefix

The coherent infinite RC11 carrier stores an existing `DeclarativeExecution`
for every finite source prefix.  Consequently the full validator provenance,
RC11 consistency, replay, node-safety, and Herlihy--Wing linearizability
theorem applies without constructing a second safety semantics.
-/

namespace InfiniteRC11Execution

/-- Every finite prefix receives the repository's complete safety bundle. -/
theorem finitePrefix_fullyVerified
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    Nonempty
      (ExecutionFrontend.FullDeclarativeGuarantees
        (execution.declarativePrefix length)) :=
  ExecutionFrontend.everyDeclarativeExecution_fullyVerified
    (execution.declarativePrefix length)

/-- Direct Herlihy--Wing projection for every finite prefix. -/
theorem finitePrefix_linearizable
    [DecidableEq α]
    (execution : InfiniteRC11Execution α threadCount)
    (length : Nat) :
    HerlihyWing.Linearizable []
      (ExecutionFrontend.declarativeObservedHistory
        (execution.declarativePrefix length)) :=
  ExecutionFrontend.everyDeclarativeExecution_linearizable
    (execution.declarativePrefix length)

end InfiniteRC11Execution

end WeakMemory.TreiberC11V1
