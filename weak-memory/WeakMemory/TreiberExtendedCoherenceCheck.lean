import WeakMemory.TreiberRelationScheduleCheck

namespace WeakMemory.TreiberRC11

/-!
# Executable extended-coherence path checking

Raw paths contain only event identifiers and primitive edge tags.  Every
identifier is resolved uniquely through the finite canonical carrier before
an edge is checked.  Missing and ambiguous identifiers are rejected.
-/

namespace ExtendedCoherenceCheck

/-- The three primitive generators of extended coherence. -/
inductive PrimitiveEdgeTag where
  | rf
  | mo
  | rb
  deriving Repr, DecidableEq

/-- One raw primitive step to a target event identifier. -/
structure RawStep where
  tag : PrimitiveEdgeTag
  target : EventId
  deriving Repr, DecidableEq

/--
A nonempty raw path.  Nonemptiness is structural because extended coherence
is transitive but not reflexive.
-/
structure RawPath where
  source : EventId
  first : RawStep
  rest : List RawStep
  deriving Repr, DecidableEq

namespace RawPath

/-- Encode one primitive logical edge as a nonempty raw path. -/
def singleton
    (tag : PrimitiveEdgeTag)
    (source target : EventId) :
    RawPath where
  source := source
  first := ⟨tag, target⟩
  rest := []

/--
Concatenate two nonempty raw paths.

The caller is responsible for ensuring that the first path's final target
identifier is the second path's source identifier.  The constructor itself
only joins their primitive-step lists.
-/
def append (first second : RawPath) : RawPath where
  source := first.source
  first := first.first
  rest := first.rest ++ second.first :: second.rest

@[simp]
theorem append_source
    (first second : RawPath) :
    (first.append second).source = first.source :=
  rfl

end RawPath

/--
Resolve an identifier only when exactly one carrier event has that identifier.
-/
def resolveUnique?
    (carrier : List (Event α))
    (eventId : EventId) :
    Option (Event α) :=
  match
    carrier.filter fun event =>
      decide (event.id = eventId)
  with
  | [event] =>
      some event
  | _ =>
      none

/--
Every canonical carrier event resolves to itself.  Fresh skeleton numbering
provides both duplicate freedom and identifier injectivity.
-/
theorem resolveUnique?_complete
    {skeleton : EventGraph.Skeleton α}
    {event : Event α}
    (member : event ∈ skeleton.events) :
    resolveUnique? skeleton.events event.id = some event := by
  let selectedEvents :=
    skeleton.events.filter fun candidate =>
      decide (candidate.id = event.id)
  have eventMatches : event ∈ selectedEvents := by
    exact List.mem_filter.mpr ⟨member, by simp⟩
  have matchesNodup : selectedEvents.Nodup := by
    exact skeleton.noDuplicateEvents.filter _
  have matchingEvent :
      ∀ candidate,
        candidate ∈ selectedEvents →
        candidate = event := by
    intro candidate candidateMember
    have description := List.mem_filter.mp candidateMember
    exact skeleton.uniqueIds description.1 member
      (by simpa using description.2)
  have matchesShape : selectedEvents = [event] := by
    cases shape : selectedEvents with
    | nil =>
        rw [shape] at eventMatches
        contradiction
    | cons first remaining =>
        have firstMember : first ∈ selectedEvents := by
          rw [shape]
          simp
        have firstShape := matchingEvent first firstMember
        subst first
        cases tailShape : remaining with
        | nil =>
            rfl
        | cons duplicate trailing =>
            have duplicateMember : duplicate ∈ selectedEvents := by
              rw [shape, tailShape]
              simp
            have duplicateShape :=
              matchingEvent duplicate duplicateMember
            subst duplicate
            rw [shape, tailShape] at matchesNodup
            simp at matchesNodup
  unfold resolveUnique?
  rw [show
    skeleton.events.filter (fun candidate =>
      decide (candidate.id = event.id)) =
        selectedEvents from rfl]
  rw [matchesShape]

/-- Successful finite lookup proves membership, identifier equality, and uniqueness. -/
theorem resolveUnique?_sound
    {carrier : List (Event α)}
    {eventId : EventId}
    {event : Event α}
    (resolved :
      resolveUnique? carrier eventId = some event) :
    event ∈ carrier ∧
      event.id = eventId ∧
      ∀ other,
        other ∈ carrier →
        other.id = eventId →
        other = event := by
  unfold resolveUnique? at resolved
  cases filteredShape :
      carrier.filter fun candidate =>
        decide (candidate.id = eventId) with
  | nil =>
      simp [filteredShape] at resolved
  | cons selected remaining =>
      cases remaining with
      | nil =>
          simp [filteredShape] at resolved
          subst event
          have selectedFiltered :
              selected ∈
                carrier.filter fun candidate =>
                  decide (candidate.id = eventId) := by
            rw [filteredShape]
            simp
          have selectedDescription :=
            List.mem_filter.mp selectedFiltered
          refine ⟨selectedDescription.1, ?_, ?_⟩
          · simpa using selectedDescription.2
          · intro other otherMember otherId
            have otherFiltered :
                other ∈
                  carrier.filter fun candidate =>
                    decide (candidate.id = eventId) :=
              List.mem_filter.mpr
                ⟨otherMember, by simp [otherId]⟩
            rw [filteredShape] at otherFiltered
            simpa using otherFiltered
      | cons duplicate trailing =>
          simp [filteredShape] at resolved

/-- A missing identifier is rejected by finite lookup. -/
theorem resolveUnique?_eq_none_of_missing
    {carrier : List (Event α)}
    {eventId : EventId}
    (missing :
      ∀ event,
        event ∈ carrier →
        event.id ≠ eventId) :
    resolveUnique? carrier eventId = none := by
  cases resolved : resolveUnique? carrier eventId with
  | none =>
      rfl
  | some event =>
      have description :=
        resolveUnique?_sound resolved
      exact False.elim
        (missing event description.1 description.2.1)

/-- Two distinct matching carrier events make lookup reject the identifier. -/
theorem resolveUnique?_eq_none_of_ambiguous
    {carrier : List (Event α)}
    {eventId : EventId}
    {first second : Event α}
    (firstMember : first ∈ carrier)
    (secondMember : second ∈ carrier)
    (firstId : first.id = eventId)
    (secondId : second.id = eventId)
    (different : first ≠ second) :
    resolveUnique? carrier eventId = none := by
  cases resolved : resolveUnique? carrier eventId with
  | none =>
      rfl
  | some event =>
      have description :=
        resolveUnique?_sound resolved
      have firstShape :=
        description.2.2 first firstMember firstId
      have secondShape :=
        description.2.2 second secondMember secondId
      exact False.elim
        (different (firstShape.trans secondShape.symm))

/-- The last raw identifier named by one nonempty path suffix. -/
def finalTargetId :
    RawStep → List RawStep → EventId
  | step, [] =>
      step.target
  | _, next :: rest =>
      finalTargetId next rest

/-- Appending a nonempty suffix makes its endpoint the combined endpoint. -/
@[simp]
theorem finalTargetId_append
    (firstStep : RawStep)
    (firstRest : List RawStep)
    (secondStep : RawStep)
    (secondRest : List RawStep) :
    finalTargetId firstStep
        (firstRest ++ secondStep :: secondRest) =
      finalTargetId secondStep secondRest := by
  induction firstRest generalizing firstStep with
  | nil =>
      rfl
  | cons next rest inductionHypothesis =>
      exact inductionHypothesis next

@[simp]
theorem RawPath.append_finalTargetId
    (first second : RawPath) :
    finalTargetId
        (first.append second).first
        (first.append second).rest =
      finalTargetId second.first second.rest :=
  finalTargetId_append
    first.first first.rest second.first second.rest

/-- Executably recognize one primitive edge between resolved carrier events. -/
def primitiveEdge
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (tag : PrimitiveEdgeTag)
    (source target : Event α) :
    Bool :=
  match tag with
  | .rf =>
      RelationScheduleCheck.readsFromEdge data source target
  | .mo =>
      RelationScheduleCheck.modificationOrderEdge
        data source target
  | .rb =>
      RelationScheduleCheck.readsBeforeEdge data source target

/-- A checked primitive edge constructs its logical extended-coherence edge. -/
theorem primitiveEdge_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {tag : PrimitiveEdgeTag}
    {source target : Event α}
    (sourceMember : source ∈ skeleton.events)
    (targetMember : target ∈ skeleton.events)
    (checked :
      primitiveEdge data tag source target = true) :
    data.graph.ExtendedCoherence source target := by
  cases tag with
  | rf =>
      apply Graph.ExtendedCoherence.readsFrom
      change data.readsFrom source target
      have sourceShape :
          data.sourceId target.id = some source.id := by
        simpa [primitiveEdge,
          RelationScheduleCheck.readsFromEdge] using checked
      exact ⟨sourceMember, targetMember, sourceShape⟩
  | mo =>
      apply Graph.ExtendedCoherence.modificationOrder
      change data.modificationOrder source target
      have idOrder :
          IdBefore source.id target.id data.writeOrder :=
        (RelationScheduleCheck.idBefore_eq_true_iff
          source.id target.id data.writeOrder).mp
            (by simpa [primitiveEdge,
              RelationScheduleCheck.modificationOrderEdge]
              using checked)
      exact ⟨sourceMember, targetMember, idOrder⟩
  | rb =>
      apply Graph.ExtendedCoherence.readsBefore
      exact
        (RelationScheduleCheck.readsBeforeEdge_eq_true_iff
          data sourceMember targetMember).mp
            (by simpa [primitiveEdge] using checked)

/-- A canonical reads-from edge passes its primitive Boolean check. -/
theorem primitiveEdge_readsFrom_complete
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.readsFrom source target) :
    primitiveEdge data .rf source target = true := by
  change data.readsFrom source target at edge
  simp [primitiveEdge,
    RelationScheduleCheck.readsFromEdge, edge.2.2]

/-- A canonical modification-order edge passes its primitive Boolean check. -/
theorem primitiveEdge_modificationOrder_complete
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.modificationOrder source target) :
    primitiveEdge data .mo source target = true := by
  change data.modificationOrder source target at edge
  exact
    (RelationScheduleCheck.idBefore_eq_true_iff
      source.id target.id data.writeOrder).mpr edge.2.2

/-- On carrier members, a logical reads-before edge passes its Boolean check. -/
theorem primitiveEdge_readsBefore_complete
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (sourceMember : source ∈ skeleton.events)
    (targetMember : target ∈ skeleton.events)
    (edge : data.graph.ReadsBefore source target) :
    primitiveEdge data .rb source target = true := by
  exact
    (RelationScheduleCheck.readsBeforeEdge_eq_true_iff
      data sourceMember targetMember).mpr edge

/-- Every extended-coherence derivation is closed over the canonical carrier. -/
theorem extendedCoherence_endpoints
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    source ∈ skeleton.events ∧
      target ∈ skeleton.events := by
  induction edge with
  | readsFrom primitive =>
      change data.readsFrom _ _ at primitive
      exact ⟨primitive.1, primitive.2.1⟩
  | modificationOrder primitive =>
      change data.modificationOrder _ _ at primitive
      exact ⟨primitive.1, primitive.2.1⟩
  | readsBefore primitive =>
      obtain ⟨write, readsFrom, modificationOrder,
        different⟩ := primitive
      change data.readsFrom write _ at readsFrom
      change data.modificationOrder write _ at modificationOrder
      exact ⟨readsFrom.2.1, modificationOrder.2.1⟩
  | transitive first second firstEndpoints secondEndpoints =>
      exact ⟨firstEndpoints.1, secondEndpoints.2⟩

/--
Check a nonempty suffix from one already resolved current event.
-/
def checkFrom
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (current : Event α)
    (step : RawStep) :
    List RawStep → Bool
  | [] =>
      match resolveUnique? skeleton.events step.target with
      | none =>
          false
      | some target =>
          primitiveEdge data step.tag current target
  | next :: rest =>
      match resolveUnique? skeleton.events step.target with
      | none =>
          false
      | some target =>
          primitiveEdge data step.tag current target &&
            checkFrom data target next rest

/--
Join two already checked nonempty suffixes at a shared canonical event.

This is the executable counterpart of transitive composition.  The final
identifier equality for the first suffix is enough to identify its resolved
endpoint with `middle`, because skeleton identifiers are injective.
-/
theorem checkFrom_append_true
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {current middle : Event α}
    (currentMember : current ∈ skeleton.events)
    (middleMember : middle ∈ skeleton.events)
    (firstStep : RawStep)
    (firstRest : List RawStep)
    (secondStep : RawStep)
    (secondRest : List RawStep)
    (firstChecked :
      checkFrom data current firstStep firstRest = true)
    (firstTarget :
      finalTargetId firstStep firstRest = middle.id)
    (secondChecked :
      checkFrom data middle secondStep secondRest = true) :
    checkFrom data current firstStep
        (firstRest ++ secondStep :: secondRest) = true := by
  induction firstRest generalizing current firstStep with
  | nil =>
      unfold checkFrom at firstChecked ⊢
      cases resolved :
          resolveUnique? skeleton.events firstStep.target with
      | none =>
          simp [resolved] at firstChecked
      | some endpoint =>
          simp only [resolved] at firstChecked ⊢
          have endpointDescription :=
            resolveUnique?_sound resolved
          have endpointShape : endpoint = middle :=
            skeleton.uniqueIds endpointDescription.1 middleMember
              (endpointDescription.2.1.trans firstTarget)
          subst endpoint
          exact Bool.and_eq_true_iff.mpr
            ⟨firstChecked, secondChecked⟩
  | cons next rest inductionHypothesis =>
      unfold checkFrom at firstChecked ⊢
      cases resolved :
          resolveUnique? skeleton.events firstStep.target with
      | none =>
          simp [resolved] at firstChecked
      | some nextEvent =>
          simp only [resolved, Bool.and_eq_true] at firstChecked
          apply Bool.and_eq_true_iff.mpr
          have nextDescription :=
            resolveUnique?_sound resolved
          exact ⟨firstChecked.1,
            inductionHypothesis nextDescription.1 next
              firstChecked.2 firstTarget⟩

/-- Check one raw path by first resolving its source uniquely. -/
def check
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (path : RawPath) :
    Bool :=
  match resolveUnique? skeleton.events path.source with
  | none =>
      false
  | some source =>
      checkFrom data source path.first path.rest

/-- Soundness of the recursive nonempty path checker. -/
theorem checkFrom_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {current : Event α}
    (currentMember : current ∈ skeleton.events)
    (step : RawStep)
    (rest : List RawStep)
    (checked :
      checkFrom data current step rest = true) :
    ∃ target,
      target ∈ skeleton.events ∧
        target.id = finalTargetId step rest ∧
        data.graph.ExtendedCoherence current target := by
  induction rest generalizing current step with
  | nil =>
      unfold checkFrom at checked
      cases resolved :
          resolveUnique? skeleton.events step.target with
      | none =>
          simp [resolved] at checked
      | some target =>
          simp only [resolved] at checked
          have targetDescription :=
            resolveUnique?_sound resolved
          exact ⟨target, targetDescription.1,
            targetDescription.2.1,
            primitiveEdge_sound data currentMember
              targetDescription.1 checked⟩
  | cons next rest inductionHypothesis =>
      unfold checkFrom at checked
      cases resolved :
          resolveUnique? skeleton.events step.target with
      | none =>
          simp [resolved] at checked
      | some middle =>
          simp only [resolved, Bool.and_eq_true] at checked
          have middleDescription :=
            resolveUnique?_sound resolved
          have firstEdge :
              data.graph.ExtendedCoherence current middle :=
            primitiveEdge_sound data currentMember
              middleDescription.1 checked.1
          obtain ⟨target, targetMember, targetId,
              laterPath⟩ :=
            inductionHypothesis middleDescription.1 next
              checked.2
          exact ⟨target, targetMember, targetId,
            Graph.ExtendedCoherence.transitive
              firstEdge laterPath⟩

/--
A passing raw path resolves both endpoints in the canonical carrier and
constructs the claimed extended-coherence path between them.
-/
theorem check_sound
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    (path : RawPath)
    (checked : check data path = true) :
    ∃ source target,
      source ∈ skeleton.events ∧
        target ∈ skeleton.events ∧
        source.id = path.source ∧
        target.id =
          finalTargetId path.first path.rest ∧
        data.graph.ExtendedCoherence source target := by
  unfold check at checked
  cases resolved :
      resolveUnique? skeleton.events path.source with
  | none =>
      simp [resolved] at checked
  | some source =>
      simp only [resolved] at checked
      have sourceDescription :=
        resolveUnique?_sound resolved
      obtain ⟨target, targetMember, targetId, pathEdge⟩ :=
        checkFrom_sound data sourceDescription.1
          path.first path.rest checked
      exact ⟨source, target, sourceDescription.1,
        targetMember, sourceDescription.2.1,
        targetId, pathEdge⟩

/--
Completeness of the finite path language.

Every logical extended-coherence derivation has a raw identifier-and-tag path
that names the same endpoints and is accepted by the executable checker.
The proof is constructive at the existential level: primitive constructors
become singleton paths and transitive constructors become `RawPath.append`.
-/
theorem exists_checked_path
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    ∃ path : RawPath,
      path.source = source.id ∧
        finalTargetId path.first path.rest = target.id ∧
        check data path = true := by
  induction edge with
  | @readsFrom source target primitive =>
      change data.readsFrom source target at primitive
      refine ⟨RawPath.singleton .rf source.id target.id,
        rfl, rfl, ?_⟩
      unfold check RawPath.singleton
      rw [resolveUnique?_complete primitive.1]
      unfold checkFrom
      rw [resolveUnique?_complete primitive.2.1]
      exact
        primitiveEdge_readsFrom_complete data
          (by
            change data.graph.readsFrom source target
            exact primitive)
  | @modificationOrder source target primitive =>
      change data.modificationOrder source target at primitive
      refine ⟨RawPath.singleton .mo source.id target.id,
        rfl, rfl, ?_⟩
      unfold check RawPath.singleton
      rw [resolveUnique?_complete primitive.1]
      unfold checkFrom
      rw [resolveUnique?_complete primitive.2.1]
      exact
        primitiveEdge_modificationOrder_complete data
          (by
            change data.graph.modificationOrder source target
            exact primitive)
  | @readsBefore source target primitive =>
      have endpoints :
          source ∈ skeleton.events ∧
            target ∈ skeleton.events :=
        extendedCoherence_endpoints data
          (.readsBefore primitive)
      refine ⟨RawPath.singleton .rb source.id target.id,
        rfl, rfl, ?_⟩
      unfold check RawPath.singleton
      rw [resolveUnique?_complete endpoints.1]
      unfold checkFrom
      rw [resolveUnique?_complete endpoints.2]
      exact
        primitiveEdge_readsBefore_complete data
          endpoints.1 endpoints.2 primitive
  | @transitive source middle target first second
      firstPath secondPath =>
      obtain ⟨left, leftSource, leftTarget,
        leftChecked⟩ := firstPath
      obtain ⟨right, rightSource, rightTarget,
        rightChecked⟩ := secondPath
      have firstEndpoints :=
        extendedCoherence_endpoints data first
      have secondEndpoints :=
        extendedCoherence_endpoints data second
      have leftSuffix :
          checkFrom data source left.first left.rest = true := by
        unfold check at leftChecked
        rw [leftSource,
          resolveUnique?_complete firstEndpoints.1]
          at leftChecked
        exact leftChecked
      have rightSuffix :
          checkFrom data middle right.first right.rest = true := by
        unfold check at rightChecked
        rw [rightSource,
          resolveUnique?_complete secondEndpoints.1]
          at rightChecked
        exact rightChecked
      refine ⟨left.append right, ?_, ?_, ?_⟩
      · exact leftSource
      · simpa using rightTarget
      · unfold check
        rw [RawPath.append_source, leftSource,
          resolveUnique?_complete firstEndpoints.1]
        exact
          checkFrom_append_true data
            firstEndpoints.1 firstEndpoints.2
            left.first left.rest right.first right.rest
            leftSuffix leftTarget rightSuffix

/--
A selected complete raw serialization of one logical path.

`ExtendedCoherence` lives in `Prop`, so Lean intentionally prevents direct
proof recursion into the data type `RawPath`.  This wrapper uses ordinary
classical choice over the constructive existential theorem above; clients
that want an axiom-free theorem can use `exists_checked_path` directly.
-/
noncomputable def serialize
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    RawPath :=
  Classical.choose (exists_checked_path data edge)

/-- The selected serialization names the logical source identifier. -/
theorem serialize_source
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    (serialize data edge).source = source.id :=
  (Classical.choose_spec
    (exists_checked_path data edge)).1

/-- The selected serialization names the logical target identifier. -/
theorem serialize_finalTargetId
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    finalTargetId
        (serialize data edge).first
        (serialize data edge).rest =
      target.id :=
  (Classical.choose_spec
    (exists_checked_path data edge)).2.1

/-- The executable checker accepts the selected serialization. -/
theorem check_serialize
    [DecidableEq α]
    {skeleton : EventGraph.Skeleton α}
    (data : AtomicRelationData skeleton)
    {source target : Event α}
    (edge : data.graph.ExtendedCoherence source target) :
    check data (serialize data edge) = true :=
  (Classical.choose_spec
    (exists_checked_path data edge)).2.2

end ExtendedCoherenceCheck

end WeakMemory.TreiberRC11
