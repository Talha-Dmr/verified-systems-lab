import WeakMemory.MSQueueChain

namespace WeakMemory.MSQueue.Chain.Example

def initial : State Nat := State.initial 0

def linked : State Nat := {
  initial with
  nodes := initial.nodes ++ [1]
  payloads := initial.payloads ++ [7]
}

def tailAdvanced : State Nat := { linked with tail := linked.tail + 1 }

def headAdvanced : State Nat := {
  tailAdvanced with head := tailAdvanced.head + 1
}

theorem replay :
    Replay initial
      [.enqueue 7, .dequeueValue 7, .dequeueEmpty]
      headAdvanced := by
  exact Replay.commit (.enqueue 7) _
    (Step.link initial 1 7 (by decide) (by decide)) <|
    Replay.silent
      (Step.advanceTail linked (by decide)) <|
    Replay.commit (.dequeueValue 7) _
      (Step.advanceHead tailAdvanced 7 (by decide) (by decide)) <|
    Replay.commit .dequeueEmpty []
      (Step.empty headAdvanced (by decide)) <|
    Replay.nil headAdvanced

theorem legal :
    QueueSpec.Legal []
      (completedHistory
        [.enqueue 7, .dequeueValue 7, .dequeueEmpty]) [] := by
  simpa [initial, headAdvanced, tailAdvanced, linked,
    State.initial, State.contents] using
    replay.linearizable (initial_wellFormed (Value := Nat) 0)

end WeakMemory.MSQueue.Chain.Example
