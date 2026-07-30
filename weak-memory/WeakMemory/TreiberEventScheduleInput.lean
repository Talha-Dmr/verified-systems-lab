import WeakMemory.TreiberExtendedCoherenceCheck

namespace WeakMemory.TreiberRC11

/-!
# Resolving raw event-identifier schedules

External execution data names canonical events by identifier.  This module
resolves such a list through the finite source carrier and rejects missing or
ambiguous identifiers before the relation-schedule checker sees it.
-/

namespace EventScheduleInput

/-- Resolve every submitted identifier, preserving submitted order. -/
def resolve?
    (carrier : List (Event α)) :
    List EventId → Option (List (Event α))
  | [] =>
      some []
  | eventId :: rest =>
      match
        ExtendedCoherenceCheck.resolveUnique? carrier eventId,
        resolve? carrier rest
      with
      | some event, some events =>
          some (event :: events)
      | _, _ =>
          none

/-- Successful resolution preserves IDs and keeps every event in the carrier. -/
theorem resolve?_sound
    {carrier : List (Event α)}
    {eventIds : List EventId}
    {schedule : List (Event α)}
    (accepted :
      resolve? carrier eventIds = some schedule) :
    schedule.map Event.id = eventIds ∧
      ∀ event,
        event ∈ schedule →
          event ∈ carrier := by
  induction eventIds generalizing schedule with
  | nil =>
      simp [resolve?] at accepted
      subst schedule
      simp
  | cons eventId rest inductionHypothesis =>
      unfold resolve? at accepted
      cases headResolved :
          ExtendedCoherenceCheck.resolveUnique? carrier eventId with
      | none =>
          simp [headResolved] at accepted
      | some event =>
          cases restResolved : resolve? carrier rest with
          | none =>
              simp [headResolved, restResolved] at accepted
          | some events =>
              simp only [headResolved, restResolved,
                Option.some.injEq] at accepted
              subst schedule
              have headDescription :=
                ExtendedCoherenceCheck.resolveUnique?_sound
                  headResolved
              have restDescription :=
                inductionHypothesis restResolved
              constructor
              · simp [headDescription.2.1,
                  restDescription.1]
              · intro candidate member
                rcases List.mem_cons.mp member with
                  isHead | inRest
                · subst candidate
                  exact headDescription.1
                · exact restDescription.2 candidate inRest

/--
Serializing a carrier-closed event schedule by canonical identifier and
resolving it again returns the original schedule.

The generated skeleton's identifier injectivity is used by
`resolveUnique?_complete` at each finite list position.
-/
theorem resolve?_complete
    {skeleton : EventGraph.Skeleton α}
    {schedule : List (Event α)}
    (closed :
      ∀ event,
        event ∈ schedule →
          event ∈ skeleton.events) :
    resolve? skeleton.events (schedule.map Event.id) =
      some schedule := by
  induction schedule with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      have eventMember :
          event ∈ skeleton.events :=
        closed event (by simp)
      have restClosed :
          ∀ candidate,
            candidate ∈ rest →
              candidate ∈ skeleton.events := by
        intro candidate member
        exact closed candidate (by simp [member])
      have headResolved :
          ExtendedCoherenceCheck.resolveUnique?
              skeleton.events event.id =
            some event :=
        ExtendedCoherenceCheck.resolveUnique?_complete
          eventMember
      have restResolved :
          resolve? skeleton.events
              (rest.map Event.id) =
            some rest :=
        inductionHypothesis restClosed
      simp [resolve?, headResolved, restResolved]

/--
For a generated skeleton carrier, successful raw-ID resolution is equivalent
to exact identifier preservation and carrier closure.
-/
theorem resolve?_eq_some_iff
    {skeleton : EventGraph.Skeleton α}
    {eventIds : List EventId}
    {schedule : List (Event α)} :
    resolve? skeleton.events eventIds = some schedule ↔
      schedule.map Event.id = eventIds ∧
        ∀ event,
          event ∈ schedule →
            event ∈ skeleton.events := by
  constructor
  · exact resolve?_sound
  · rintro ⟨idsShape, closed⟩
    rw [← idsShape]
    exact resolve?_complete closed

end EventScheduleInput

end WeakMemory.TreiberRC11
