import WeakMemory.MSQueueSourceLinkGraph
import WeakMemory.MSQueueSourcePayload

namespace WeakMemory.MSQueue.Source.Structural

/-!
# Canonical structural-record prefix state

The universal replay proof needs a state determined by the already scheduled
records, rather than an independently chosen oracle state.  This module gives
that state and the minimal list invariant from which the ordinary
`Chain.WellFormed` facts follow.
-/

namespace Prefix

/-- One permanent link in the queue chain. -/
structure Edge (Value : Type) where
  owner : NodeId
  child : NodeId
  payload : Value
  deriving Repr, DecidableEq

namespace Record

def edge? : Structural.Record Value → Option (Edge Value)
  | ⟨_, _, _, .link owner child payload⟩ =>
      some ⟨owner, child, payload⟩
  | _ => none

def tailMove? : Structural.Record Value → Option (NodeId × NodeId)
  | ⟨_, _, _, .advanceTail expected desired⟩ =>
      some (expected, desired)
  | _ => none

def headMove? : Structural.Record Value → Option (Edge Value)
  | ⟨_, _, _, .advanceHead expected desired payload⟩ =>
      some ⟨expected, desired, payload⟩
  | _ => none

theorem projections_of_link
    {record : Structural.Record Value}
    {owner child : NodeId}
    {payload : Value}
    (actionShape : record.action = .link owner child payload) :
    edge? record = some ⟨owner, child, payload⟩ ∧
      tailMove? record = none ∧ headMove? record = none := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl, rfl⟩
  simp [edge?, tailMove?, headMove?]

theorem projections_of_advanceTail
    {record : Structural.Record Value}
    {expected desired : NodeId}
    (actionShape : record.action = .advanceTail expected desired) :
    edge? record = none ∧
      tailMove? record = some (expected, desired) ∧
      headMove? record = none := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl⟩
  simp [edge?, tailMove?, headMove?]

theorem projections_of_advanceHead
    {record : Structural.Record Value}
    {expected desired : NodeId}
    {payload : Value}
    (actionShape :
      record.action = .advanceHead expected desired payload) :
    edge? record = none ∧ tailMove? record = none ∧
      headMove? record = some ⟨expected, desired, payload⟩ := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl, rfl⟩
  simp [edge?, tailMove?, headMove?]

end Record

def links (records : List (Structural.Record Value)) : List (Edge Value) :=
  records.filterMap Record.edge?

def tailMoves
    (records : List (Structural.Record Value)) :
    List (NodeId × NodeId) :=
  records.filterMap Record.tailMove?

def headMoves
    (records : List (Structural.Record Value)) : List (Edge Value) :=
  records.filterMap Record.headMove?

@[simp] theorem links_nil : links ([] : List (Structural.Record Value)) = [] :=
  rfl

@[simp] theorem tailMoves_nil :
    tailMoves ([] : List (Structural.Record Value)) = [] :=
  rfl

@[simp] theorem headMoves_nil :
    headMoves ([] : List (Structural.Record Value)) = [] :=
  rfl

@[simp] theorem links_append
    (left right : List (Structural.Record Value)) :
    links (left ++ right) = links left ++ links right := by
  simp [links]

@[simp] theorem tailMoves_append
    (left right : List (Structural.Record Value)) :
    tailMoves (left ++ right) = tailMoves left ++ tailMoves right := by
  simp [tailMoves]

@[simp] theorem headMoves_append
    (left right : List (Structural.Record Value)) :
    headMoves (left ++ right) = headMoves left ++ headMoves right := by
  simp [headMoves]

theorem edge_mem_links_of_record
    {records : List (Structural.Record Value)}
    {record : Structural.Record Value}
    (member : record ∈ records)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : record.action = .link owner child payload) :
    (⟨owner, child, payload⟩ : Edge Value) ∈ links records := by
  apply List.mem_filterMap.mpr
  refine ⟨record, member, ?_⟩
  exact (Record.projections_of_link actionShape).1

theorem tailMove_mem_of_record
    {records : List (Structural.Record Value)}
    {record : Structural.Record Value}
    (member : record ∈ records)
    {expected desired : NodeId}
    (actionShape : record.action = .advanceTail expected desired) :
    (expected, desired) ∈ tailMoves records := by
  apply List.mem_filterMap.mpr
  refine ⟨record, member, ?_⟩
  exact (Record.projections_of_advanceTail actionShape).2.1

theorem record_of_edge_mem_links
    {records : List (Structural.Record Value)}
    {edge : Edge Value}
    (member : edge ∈ links records) :
    ∃ record ∈ records,
      record.action = .link edge.owner edge.child edge.payload := by
  rcases List.mem_filterMap.mp member with ⟨record, recordMember, selected⟩
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp [Record.edge?] at selected
  subst edge
  exact ⟨_, recordMember, rfl⟩

/-- The replay state is a canonical projection of its scheduled prefix. -/
def stateOf
    (dummy : NodeId)
    (records : List (Structural.Record Value)) : Chain.State Value where
  nodes := dummy :: (links records).map Edge.child
  payloads := (links records).map Edge.payload
  head := (headMoves records).length
  tail := (tailMoves records).length

@[simp] theorem stateOf_nil (dummy : NodeId) :
    stateOf (Value := Value) dummy [] = Chain.State.initial dummy :=
  rfl

/-- Appending one link record performs exactly the canonical chain append. -/
theorem stateOf_snoc_link
    (dummy : NodeId)
    (records : List (Structural.Record Value))
    (record : Structural.Record Value)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : record.action = .link owner child payload) :
    stateOf dummy (records ++ [record]) = {
      stateOf dummy records with
      nodes := (stateOf dummy records).nodes ++ [child]
      payloads := (stateOf dummy records).payloads ++ [payload]
    } := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl, rfl⟩
  simp [stateOf, links, tailMoves, headMoves, Record.edge?,
    Record.tailMove?, Record.headMove?]

/-- Appending one Tail swing increments exactly the canonical Tail index. -/
theorem stateOf_snoc_advanceTail
    (dummy : NodeId)
    (records : List (Structural.Record Value))
    (record : Structural.Record Value)
    {expected desired : NodeId}
    (actionShape : record.action = .advanceTail expected desired) :
    stateOf dummy (records ++ [record]) =
      { stateOf dummy records with
          tail := (stateOf dummy records).tail + 1 } := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl⟩
  simp [stateOf, links, tailMoves, headMoves, Record.edge?,
    Record.tailMove?, Record.headMove?]

/-- Appending one Head swing increments exactly the canonical Head index. -/
theorem stateOf_snoc_advanceHead
    (dummy : NodeId)
    (records : List (Structural.Record Value))
    (record : Structural.Record Value)
    {expected desired : NodeId}
    {payload : Value}
    (actionShape :
      record.action = .advanceHead expected desired payload) :
    stateOf dummy (records ++ [record]) =
      { stateOf dummy records with
          head := (stateOf dummy records).head + 1 } := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  rcases actionShape with ⟨rfl, rfl, rfl⟩
  simp [stateOf, links, tailMoves, headMoves, Record.edge?,
    Record.tailMove?, Record.headMove?]

/-- Appending an empty record leaves the canonical pointer state unchanged. -/
theorem stateOf_snoc_empty
    (dummy : NodeId)
    (records : List (Structural.Record Value))
    (record : Structural.Record Value)
    {head : NodeId}
    (actionShape : record.action = .empty head) :
    stateOf dummy (records ++ [record]) = stateOf dummy records := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  subst head
  simp [stateOf, links, tailMoves, headMoves, Record.edge?,
    Record.tailMove?, Record.headMove?]

/-- Minimal invariant over the three record projections. -/
structure Rep
    (dummy : NodeId)
    (records : List (Structural.Record Value)) : Prop where
  linkPath :
    (links records).map Edge.owner =
      (dummy :: (links records).map Edge.child).take
        (links records).length
  nodesNodup :
    (dummy :: (links records).map Edge.child).Nodup
  tailExact :
    tailMoves records =
      ((links records).take (tailMoves records).length).map
        fun edge => (edge.owner, edge.child)
  headExact :
    headMoves records =
      (links records).take (headMoves records).length
  headBeforeTail :
    (headMoves records).length ≤ (tailMoves records).length
  tailBound :
    (tailMoves records).length ≤ (links records).length
  tailLag :
    (links records).length ≤ (tailMoves records).length + 1

theorem Rep.nil (dummy : NodeId) :
    Rep (Value := Value) dummy [] := by
  exact {
    linkPath := by simp
    nodesNodup := by simp
    tailExact := by simp
    headExact := by simp
    headBeforeTail := by simp
    tailBound := by simp
    tailLag := by simp
  }

/-- An edge at index `i` names exactly state node `i`, state node `i + 1`,
and payload slot `i`. -/
theorem Rep.edgeAt_state
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    {index : Nat}
    {edge : Edge Value}
    (edgeAt : (links records)[index]? = some edge) :
    (stateOf dummy records).nodes[index]? = some edge.owner ∧
      (stateOf dummy records).nodes[index + 1]? = some edge.child ∧
      (stateOf dummy records).payloads[index]? = some edge.payload := by
  have indexBound : index < (links records).length :=
    (List.getElem?_eq_some_iff.mp edgeAt).1
  have ownerProjection :=
    congrArg (Option.map Edge.owner) edgeAt
  have childProjection :=
    congrArg (Option.map Edge.child) edgeAt
  have payloadProjection :=
    congrArg (Option.map Edge.payload) edgeAt
  rw [← List.getElem?_map] at ownerProjection
  rw [represented.linkPath] at ownerProjection
  rw [List.getElem?_take_of_lt indexBound] at ownerProjection
  rw [← List.getElem?_map] at childProjection payloadProjection
  exact ⟨by simpa [stateOf] using ownerProjection,
    by simpa [stateOf] using childProjection,
    by simpa [stateOf] using payloadProjection⟩

/-- In a represented path, a node that occurs in the chain but owns no edge
is exactly the final node. -/
theorem Rep.getLast?_eq_of_mem_of_not_owner
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    {node : NodeId}
    (nodeMember :
      node ∈ dummy :: (links records).map Edge.child)
    (notOwner : node ∉ (links records).map Edge.owner) :
    (dummy :: (links records).map Edge.child).getLast? = some node := by
  let nodes := dummy :: (links records).map Edge.child
  have notInPrefix :
      node ∉ nodes.take (nodes.length - 1) := by
    have notInOwners := notOwner
    rw [represented.linkPath] at notInOwners
    simpa [nodes] using notInOwners
  have expansion := List.take_append_getLast? nodes
  have memberInLast : node ∈ nodes.getLast?.toList := by
    have inNodes : node ∈ nodes := by simpa [nodes] using nodeMember
    rw [← expansion] at inNodes
    exact (List.mem_append.mp inNodes).resolve_left notInPrefix
  simpa using memberInLast

/-- If the represented Tail-move prefix already contains an edge ending at
the final chain node, Tail has reached the end of the link prefix. -/
theorem Rep.tailAtEnd_of_move_to_last
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    {previous node : NodeId}
    (moveMember : (previous, node) ∈ tailMoves records)
    (nodeAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some node) :
    (tailMoves records).length = (links records).length := by
  have moveInEdges := moveMember
  rw [represented.tailExact] at moveInEdges
  rcases List.mem_map.mp moveInEdges with
    ⟨edge, edgeInTake, edgeShape⟩
  have childShape : edge.child = node := by
    injection edgeShape with _ childEq
  rcases List.mem_take_iff_getElem.mp edgeInTake with
    ⟨index, indexBound, edgeAtIndex⟩
  have edgeAt : (links records)[index]? = some edge :=
    List.getElem?_eq_some_iff.mpr
      ⟨Nat.lt_of_lt_of_le indexBound (Nat.min_le_right _ _),
        edgeAtIndex⟩
  obtain ⟨_ownerAt, childAt, _payloadAt⟩ :=
    represented.edgeAt_state edgeAt
  rw [childShape] at childAt
  have lastAt := nodeAtEnd
  rw [List.getLast?_eq_getElem?] at lastAt
  have sameNode :
      (dummy :: (links records).map Edge.child)[index + 1]? =
        (dummy :: (links records).map Edge.child)[
          (links records).length]? := by
    exact childAt.trans (by simpa using lastAt.symm)
  have firstIndexBound :
      index + 1 <
        (dummy :: (links records).map Edge.child).length := by
    simp only [List.length_cons, List.length_map]
    have indexBeforeTail : index < (tailMoves records).length :=
      Nat.lt_of_lt_of_le indexBound (Nat.min_le_left _ _)
    have tailBound := represented.tailBound
    omega
  have indexAtLast : index + 1 = (links records).length :=
    (List.getElem?_inj firstIndexBound represented.nodesNodup).mp sameNode
  have indexBeforeTail : index < (tailMoves records).length :=
    Nat.lt_of_lt_of_le indexBound (Nat.min_le_left _ _)
  have tailBound := represented.tailBound
  omega

/-- If the permanent dummy is also the final represented node, no link has
yet been installed and Tail is at that end. -/
theorem Rep.tailAtEnd_of_dummy_at_last
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (dummyAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some dummy) :
    (tailMoves records).length = (links records).length := by
  have headAt :
      (dummy :: (links records).map Edge.child)[0]? = some dummy :=
    rfl
  have lastAt := dummyAtEnd
  rw [List.getLast?_eq_getElem?] at lastAt
  have sameNode :
      (dummy :: (links records).map Edge.child)[0]? =
        (dummy :: (links records).map Edge.child)[
          (links records).length]? := by
    exact headAt.trans (by simpa using lastAt.symm)
  have zeroBound :
      0 < (dummy :: (links records).map Edge.child).length := by
    simp
  have noLinks : (links records).length = 0 :=
    (List.getElem?_inj zeroBound represented.nodesNodup).mp sameNode |>.symm
  have tailBound := represented.tailBound
  omega

/-- Empty observations do not change any of the canonical projections. -/
theorem Rep.snocEmpty
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {head : NodeId}
    (actionShape : record.action = .empty head) :
    Rep dummy (records ++ [record]) := by
  rcases record with ⟨occurrence, point, validation, action⟩
  cases action <;> simp at actionShape
  subst head
  refine {
    linkPath := ?_
    nodesNodup := ?_
    tailExact := ?_
    headExact := ?_
    headBeforeTail := ?_
    tailBound := ?_
    tailLag := ?_
  }
  · simpa [links, Record.edge?] using represented.linkPath
  · simpa [links, Record.edge?] using represented.nodesNodup
  · simpa [links, tailMoves, Record.edge?, Record.tailMove?] using
      represented.tailExact
  · simpa [links, headMoves, Record.edge?, Record.headMove?] using
      represented.headExact
  · simpa [tailMoves, headMoves, Record.tailMove?, Record.headMove?] using
      represented.headBeforeTail
  · simpa [links, tailMoves, Record.edge?, Record.tailMove?] using
      represented.tailBound
  · simpa [links, tailMoves, Record.edge?, Record.tailMove?] using
      represented.tailLag

/-- Pure list step for appending a fresh link at the current Tail/end node. -/
theorem Rep.snocLink
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : record.action = .link owner child payload)
    (ownerAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some owner)
    (childFresh :
      child ∉ dummy :: (links records).map Edge.child)
    (tailAtEnd :
      (tailMoves records).length = (links records).length) :
    Rep dummy (records ++ [record]) := by
  obtain ⟨edgeProjection, tailProjection, headProjection⟩ :=
    Record.projections_of_link actionShape
  have linksShape :
      links (records ++ [record]) =
        links records ++ [⟨owner, child, payload⟩] := by
    simp [links, edgeProjection]
  have tailMovesShape :
      tailMoves (records ++ [record]) = tailMoves records := by
    simp [tailMoves, tailProjection]
  have headMovesShape :
      headMoves (records ++ [record]) = headMoves records := by
    simp [headMoves, headProjection]
  have ownerClosesPath :
      (links records).map Edge.owner ++ [owner] =
        dummy :: (links records).map Edge.child := by
    rw [represented.linkPath]
    have closes := List.take_append_getLast?
      (dummy :: (links records).map Edge.child)
    rw [ownerAtEnd] at closes
    simpa using closes
  have headBound :
      (headMoves records).length ≤ (links records).length :=
    Nat.le_trans represented.headBeforeTail represented.tailBound
  refine {
    linkPath := ?_
    nodesNodup := ?_
    tailExact := ?_
    headExact := ?_
    headBeforeTail := ?_
    tailBound := ?_
    tailLag := ?_
  }
  · rw [linksShape]
    simpa using ownerClosesPath
  · have appendedNodup :
        ((dummy :: (links records).map Edge.child) ++ [child]).Nodup := by
      rw [List.nodup_append]
      refine ⟨represented.nodesNodup, by simp, ?_⟩
      intro existing existingMember appended appendedMember
      simp at appendedMember
      subst appended
      intro same
      apply childFresh
      rwa [← same]
    rw [linksShape]
    simpa using appendedNodup
  · rw [tailMovesShape, linksShape]
    rw [List.take_append_of_le_length represented.tailBound]
    exact represented.tailExact
  · rw [headMovesShape, linksShape]
    rw [List.take_append_of_le_length headBound]
    exact represented.headExact
  · rw [headMovesShape, tailMovesShape]
    exact represented.headBeforeTail
  · rw [tailMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    exact Nat.le_succ_of_le represented.tailBound
  · rw [tailMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Pure list step for advancing Tail across the next represented edge. -/
theorem Rep.snocAdvanceTail
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {expected desired : NodeId}
    {payload : Value}
    (actionShape : record.action = .advanceTail expected desired)
    (nextEdge :
      (links records)[(tailMoves records).length]? =
        some ⟨expected, desired, payload⟩) :
    Rep dummy (records ++ [record]) := by
  obtain ⟨edgeProjection, tailProjection, headProjection⟩ :=
    Record.projections_of_advanceTail actionShape
  have linksShape :
      links (records ++ [record]) = links records := by
    simp [links, edgeProjection]
  have tailMovesShape :
      tailMoves (records ++ [record]) =
        tailMoves records ++ [(expected, desired)] := by
    simp [tailMoves, tailProjection]
  have headMovesShape :
      headMoves (records ++ [record]) = headMoves records := by
    simp [headMoves, headProjection]
  have nextIndex :
      (tailMoves records).length < (links records).length :=
    (List.getElem?_eq_some_iff.mp nextEdge).1
  have takeNext :
      (links records).take ((tailMoves records).length + 1) =
        (links records).take (tailMoves records).length ++
          [⟨expected, desired, payload⟩] := by
    rw [List.take_add_one, nextEdge]
    rfl
  refine {
    linkPath := ?_
    nodesNodup := ?_
    tailExact := ?_
    headExact := ?_
    headBeforeTail := ?_
    tailBound := ?_
    tailLag := ?_
  }
  · rw [linksShape]
    exact represented.linkPath
  · rw [linksShape]
    exact represented.nodesNodup
  · rw [tailMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    rw [takeNext, List.map_append]
    simpa using congrArg
      (fun moves => moves ++ [(expected, desired)])
      represented.tailExact
  · rw [headMovesShape, linksShape]
    exact represented.headExact
  · rw [headMovesShape, tailMovesShape]
    simp only [List.length_append, List.length_singleton]
    exact Nat.le_succ_of_le represented.headBeforeTail
  · rw [tailMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [tailMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    have tailLag := represented.tailLag
    omega

/-- Pure list step for advancing Head across the next represented edge. -/
theorem Rep.snocAdvanceHead
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {expected desired : NodeId}
    {payload : Value}
    (actionShape :
      record.action = .advanceHead expected desired payload)
    (nextEdge :
      (links records)[(headMoves records).length]? =
        some ⟨expected, desired, payload⟩)
    (headBeforeTail :
      (headMoves records).length < (tailMoves records).length) :
    Rep dummy (records ++ [record]) := by
  obtain ⟨edgeProjection, tailProjection, headProjection⟩ :=
    Record.projections_of_advanceHead actionShape
  have linksShape :
      links (records ++ [record]) = links records := by
    simp [links, edgeProjection]
  have tailMovesShape :
      tailMoves (records ++ [record]) = tailMoves records := by
    simp [tailMoves, tailProjection]
  have headMovesShape :
      headMoves (records ++ [record]) =
        headMoves records ++ [⟨expected, desired, payload⟩] := by
    simp [headMoves, headProjection]
  have nextIndex :
      (headMoves records).length < (links records).length :=
    (List.getElem?_eq_some_iff.mp nextEdge).1
  have takeNext :
      (links records).take ((headMoves records).length + 1) =
        (links records).take (headMoves records).length ++
          [⟨expected, desired, payload⟩] := by
    rw [List.take_add_one, nextEdge]
    rfl
  refine {
    linkPath := ?_
    nodesNodup := ?_
    tailExact := ?_
    headExact := ?_
    headBeforeTail := ?_
    tailBound := ?_
    tailLag := ?_
  }
  · rw [linksShape]
    exact represented.linkPath
  · rw [linksShape]
    exact represented.nodesNodup
  · rw [tailMovesShape, linksShape]
    exact represented.tailExact
  · rw [headMovesShape, linksShape]
    simp only [List.length_append, List.length_singleton]
    rw [takeNext]
    exact congrArg
      (fun moves => moves ++ [⟨expected, desired, payload⟩])
      represented.headExact
  · rw [headMovesShape, tailMovesShape]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [tailMovesShape, linksShape]
    exact represented.tailBound
  · rw [tailMovesShape, linksShape]
    exact represented.tailLag

/-! ## Readiness facts imply exact `Record.Applies` steps -/

theorem Rep.linkApplies
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (_represented : Rep dummy records)
    (record : Structural.Record Value)
    {owner child : NodeId}
    {payload : Value}
    (actionShape : record.action = .link owner child payload)
    (ownerAtEnd :
      (dummy :: (links records).map Edge.child).getLast? = some owner)
    (childFresh :
      child ∉ dummy :: (links records).map Edge.child)
    (tailAtEnd :
      (tailMoves records).length = (links records).length) :
    record.Applies (stateOf dummy records)
      (stateOf dummy (records ++ [record])) := by
  rw [Record.Applies, actionShape]
  have ownerAtTail := ownerAtEnd
  rw [List.getLast?_eq_getElem?] at ownerAtTail
  refine ⟨?_, ?_, ?_, stateOf_snoc_link dummy records record actionShape⟩
  · simpa [stateOf, tailAtEnd] using ownerAtTail
  · simpa [stateOf] using childFresh
  · simp only [stateOf, List.length_cons, List.length_map]
    omega

theorem Rep.advanceTailApplies
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {expected desired : NodeId}
    {payload : Value}
    (actionShape : record.action = .advanceTail expected desired)
    (nextEdge :
      (links records)[(tailMoves records).length]? =
        some ⟨expected, desired, payload⟩) :
    record.Applies (stateOf dummy records)
      (stateOf dummy (records ++ [record])) := by
  obtain ⟨expectedAt, desiredAt, _payloadAt⟩ :=
    represented.edgeAt_state nextEdge
  have nextIndex :
      (tailMoves records).length < (links records).length :=
    (List.getElem?_eq_some_iff.mp nextEdge).1
  rw [Record.Applies, actionShape]
  refine ⟨by simpa [stateOf] using expectedAt,
    by simpa [stateOf] using desiredAt, ?_,
    stateOf_snoc_advanceTail dummy records record actionShape⟩
  simp only [stateOf, List.length_cons, List.length_map]
  omega

theorem Rep.advanceHeadApplies
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records)
    (record : Structural.Record Value)
    {expected desired : NodeId}
    {payload : Value}
    (actionShape :
      record.action = .advanceHead expected desired payload)
    (nextEdge :
      (links records)[(headMoves records).length]? =
        some ⟨expected, desired, payload⟩)
    (headBeforeTail :
      (headMoves records).length < (tailMoves records).length) :
    record.Applies (stateOf dummy records)
      (stateOf dummy (records ++ [record])) := by
  obtain ⟨expectedAt, desiredAt, payloadAt⟩ :=
    represented.edgeAt_state nextEdge
  rw [Record.Applies, actionShape]
  exact ⟨by simpa [stateOf] using expectedAt,
    by simpa [stateOf] using desiredAt,
    by simpa [stateOf] using headBeforeTail,
    by simpa [stateOf] using payloadAt,
    stateOf_snoc_advanceHead dummy records record actionShape⟩

theorem Rep.emptyApplies
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (_represented : Rep dummy records)
    (record : Structural.Record Value)
    {head : NodeId}
    (actionShape : record.action = .empty head)
    (headNode :
      (stateOf dummy records).nodes[(headMoves records).length]? =
        some head)
    (headAtEnd :
      (headMoves records).length = (links records).length) :
    record.Applies (stateOf dummy records)
      (stateOf dummy (records ++ [record])) := by
  rw [Record.Applies, actionShape]
  refine ⟨by simpa [stateOf] using headNode, ?_, ?_⟩
  · simp only [stateOf, List.length_cons, List.length_map]
    omega
  · exact stateOf_snoc_empty dummy records record actionShape

/-- The canonical state of every represented prefix satisfies the existing
memory-model-independent chain invariant. -/
theorem Rep.stateWellFormed
    {dummy : NodeId}
    {records : List (Structural.Record Value)}
    (represented : Rep dummy records) :
    Chain.WellFormed (stateOf dummy records) := by
  refine {
    aligned := by simp [stateOf]
    nodesNodup := represented.nodesNodup
    headValid := ?_
    tailValid := ?_
    headBeforeTail := represented.headBeforeTail
    tailAtEnd := ?_
  }
  · simp only [stateOf, List.length_cons, List.length_map]
    have headBeforeTail := represented.headBeforeTail
    have tailBound := represented.tailBound
    omega
  · simp only [stateOf, List.length_cons, List.length_map]
    have tailBound := represented.tailBound
    omega
  · simp only [stateOf, List.length_cons, List.length_map]
    have tailLag := represented.tailLag
    omega

/-- The canonical state keeps the selected permanent dummy at its root. -/
theorem stateOf_rooted
    (dummy : NodeId)
    (records : List (Structural.Record Value)) :
    Chain.Rooted dummy (stateOf (Value := Value) dummy records) :=
  rfl

end Prefix

namespace Replay

/-- Extend an already checked structural replay by one record at its end. -/
theorem snoc
    {Value : Type}
    {initial before after : Chain.State Value}
    {records : List (Record Value)}
    {record : Record Value}
    (replayPrefix : Replay initial records before)
    (last : record.Applies before after) :
    Replay initial (records ++ [record]) after := by
  induction replayPrefix with
  | nil state =>
      exact Replay.cons last (Replay.nil after)
  | cons first later inductionHypothesis =>
      exact Replay.cons first (inductionHypothesis last)

end Replay

end WeakMemory.MSQueue.Source.Structural
