import WeakMemory.TreiberC11V1

namespace WeakMemory.TreiberC11V1

/-!
# Finite local control between Treiber liveness boundaries

This source-only module identifies the events relevant to system progress and
proves that local computation cannot wander forever between them.  It does not
assume an RC11 graph, scheduling fairness, or primitive CAS progress.
-/

namespace TraceEvent

/-- A client starts a push or pop call on the long-lived stack. -/
def IsPushPopInvocation : TraceEvent α → Prop
  | .invokePush _ _ _ _
  | .invokePop _ _ =>
      True
  | _ =>
      False

/-- A dynamic weak compare-and-exchange attempt, successful or failed. -/
def IsCASAttempt : TraceEvent α → Prop
  | .atomic
      ⟨_, .pushCas _ _ _ _ _ _ _⟩ =>
      True
  | .atomic
      ⟨_, .popCas _ _ _ _ _ _ _⟩ =>
      True
  | _ =>
      False

/-- A successful compare-and-exchange commit. -/
def IsSuccessfulCAS : TraceEvent α → Prop
  | .atomic
      ⟨_, .pushCas _ _ _ _ _ _ true⟩ =>
      True
  | .atomic
      ⟨_, .popCas _ _ _ _ _ _ true⟩ =>
      True
  | _ =>
      False

/-- The local expected pointer supplied to a CAS event, if it is a CAS. -/
def casExpected? : TraceEvent α → Option Ptr
  | .atomic
      ⟨_, .pushCas _ _ _ _ expected _ _⟩ =>
      some expected
  | .atomic
      ⟨_, .popCas _ _ expected _ _ _ _⟩ =>
      some (.node expected)
  | _ =>
      none

/-- The pointer actually observed by a CAS event, if it is a CAS. -/
def casObserved? : TraceEvent α → Option Ptr
  | .atomic
      ⟨_, .pushCas _ _ _ _ _ observed _⟩ =>
      some observed
  | .atomic
      ⟨_, .popCas _ _ _ _ _ observed _⟩ =>
      some observed
  | _ =>
      none

/-- The expected and observed pointers of one genuine CAS attempt agree. -/
def CASComparesEqual (event : TraceEvent α) : Prop :=
  ∃ value,
    event.casExpected? = some value ∧
      event.casObserved? = some value

/--
A load that decides an operation without needing a subsequent CAS attempt.

An empty pop linearizes at its null load.  Every `isEmpty` call linearizes at
its load.  A non-null pop load merely starts the `next`-field/CAS path.
-/
def IsDecisiveLoad : TraceEvent α → Prop
  | .atomic
      ⟨_, .popLoad _ _ .null⟩ =>
      True
  | .atomic
      ⟨_, .isEmptyLoad _ _ _⟩ =>
      True
  | _ =>
      False

/--
An atomic source event that commits one abstract stack operation.

The failed pop CAS that observes null commits an empty pop even though the RMW
itself did not succeed.
-/
def IsOperationCommit : TraceEvent α → Prop
  | .atomic
      ⟨_, .pushCas _ _ _ _ _ _ true⟩ =>
      True
  | .atomic
      ⟨_, .popLoad _ _ .null⟩ =>
      True
  | .atomic
      ⟨_, .popCas _ _ _ _ _ _ true⟩ =>
      True
  | .atomic
      ⟨_, .popCas _ _ _ _ _ .null false⟩ =>
      True
  | .atomic
      ⟨_, .isEmptyLoad _ _ _⟩ =>
      True
  | _ =>
      False

/-- A source-level method response. -/
def IsResponse : TraceEvent α → Prop
  | .respondPush _ _
  | .respondPop _ _ _
  | .respondIsEmpty _ _ _ =>
      True
  | _ =>
      False

/--
An event at which the local liveness proof must consult either primitive
progress, memory behavior, or method completion.
-/
def IsLivenessBoundary (event : TraceEvent α) : Prop :=
  event.IsCASAttempt ∨
    event.IsDecisiveLoad ∨
    event.IsResponse

theorem successfulCAS_is_attempt
    {event : TraceEvent α}
    (successful : event.IsSuccessfulCAS) :
    event.IsCASAttempt := by
  cases event with
  | atomic occurrence =>
      cases occurrence with
      | mk id action =>
          cases action <;>
            simp [IsSuccessfulCAS] at successful
          case pushCas succeeded =>
            cases succeeded
            · simp at successful
            · simp [IsCASAttempt]
          case popCas succeeded =>
            cases succeeded
            · simp at successful
            · simp [IsCASAttempt]
  | _ =>
      simp [IsSuccessfulCAS] at successful

/-- A compare-equal event is necessarily a genuine CAS attempt. -/
theorem comparesEqual_is_attempt
    {event : TraceEvent α}
    (matching : event.CASComparesEqual) :
    event.IsCASAttempt := by
  obtain ⟨value, expected, observed⟩ := matching
  cases event with
  | atomic occurrence =>
      cases occurrence with
      | mk id action =>
          cases action <;>
            simp [casExpected?] at expected
          all_goals simp [IsCASAttempt]
  | _ =>
      simp [casExpected?] at expected

/-- Every successful CAS is an abstract operation commit. -/
theorem successfulCAS_is_commit
    {event : TraceEvent α}
    (successful : event.IsSuccessfulCAS) :
    event.IsOperationCommit := by
  cases event with
  | atomic occurrence =>
      cases occurrence with
      | mk id action =>
          cases action <;>
            simp [IsSuccessfulCAS] at successful
          case pushCas succeeded =>
            cases succeeded
            · simp at successful
            · simp [IsOperationCommit]
          case popCas succeeded =>
            cases succeeded
            · simp at successful
            · simp [IsOperationCommit]
  | _ =>
      simp [IsSuccessfulCAS] at successful

/-- Every decisive load is an abstract operation commit. -/
theorem decisiveLoad_is_commit
    {event : TraceEvent α}
    (decisive : event.IsDecisiveLoad) :
    event.IsOperationCommit := by
  cases event with
  | atomic occurrence =>
      cases occurrence with
      | mk id action =>
          cases action with
          | popLoad thread operation observed =>
              cases observed <;>
                simp [IsDecisiveLoad,
                  IsOperationCommit] at decisive ⊢
          | isEmptyLoad =>
              simp [IsOperationCommit]
          | _ =>
              simp [IsDecisiveLoad] at decisive
  | _ =>
      simp [IsDecisiveLoad] at decisive

end TraceEvent

/-- A thread has an invoked operation that has not yet returned. -/
def Active : LocalState α → Prop
  | .idle =>
      False
  | _ =>
      True

/--
A thread has a pending push or pop call.

Unlike a predicate on fresh invocation events, this remains true for one
operation that is stuck forever, so it is suitable for stating non-vacuous
long-run client demand.
-/
def PushPopActive : LocalState α → Prop
  | .pushLoading ..
  | .pushWriting ..
  | .pushing ..
  | .popLoading ..
  | .popReading ..
  | .popping ..
  | .returningPush ..
  | .returningPop .. =>
      True
  | .idle
  | .checkingEmpty ..
  | .returningIsEmpty .. =>
      False

/-- Every pending push or pop call is an active operation. -/
theorem PushPopActive.active
    {state : LocalState α}
    (pending : PushPopActive state) :
    Active state := by
  cases state <;>
    simp [PushPopActive, Active] at pending ⊢

/-- A committed operation is waiting to emit its source-level response. -/
def Returning : LocalState α → Prop
  | .returningPush ..
  | .returningPop ..
  | .returningIsEmpty .. =>
      True
  | _ =>
      False

/-- Every returning state still belongs to its pending invocation. -/
theorem Returning.active
    {state : LocalState α}
    (returning : Returning state) :
    Active state := by
  cases state <;> simp [Returning, Active] at returning ⊢

/--
Number of purely local scheduled steps remaining before the next liveness
boundary on the current straight-line control path.
-/
def controlRank : LocalState α → Nat
  | .idle =>
      0
  | .pushLoading .. =>
      2
  | .pushWriting .. =>
      1
  | .pushing .. =>
      0
  | .popLoading .. =>
      2
  | .popReading .. =>
      1
  | .popping .. =>
      0
  | .checkingEmpty .. =>
      0
  | .returningPush .. =>
      0
  | .returningPop .. =>
      0
  | .returningIsEmpty .. =>
      0

/-- The local distance to a liveness boundary is uniformly bounded. -/
theorem controlRank_le_two
    (state : LocalState α) :
    controlRank state ≤ 2 := by
  cases state <;> simp [controlRank]

namespace LocalStep

/-- A push/pop invocation leaves its owner in an active local state. -/
theorem active_after_of_pushPopInvocation
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (invocation : event.IsPushPopInvocation) :
    Active after := by
  cases step <;>
    simp [TraceEvent.IsPushPopInvocation, Active] at invocation ⊢

/-- Every source-valid successful CAS compares equal. -/
theorem successfulCAS_comparesEqual
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (successful : event.IsSuccessfulCAS) :
    event.CASComparesEqual := by
  cases step <;>
    simp [TraceEvent.IsSuccessfulCAS,
      TraceEvent.CASComparesEqual,
      TraceEvent.casExpected?,
      TraceEvent.casObserved?] at successful ⊢

/-- A non-response source step preserves activity. -/
theorem active_after_of_not_response
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (active : Active before)
    (notResponse : ¬ event.IsResponse) :
    Active after := by
  cases step <;>
    simp [Active, TraceEvent.IsResponse] at active notResponse ⊢

/-- The only step available from a returning state emits a response. -/
theorem response_of_returning
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (returning : Returning before) :
    event.IsResponse := by
  cases step <;>
    simp [Returning, TraceEvent.IsResponse] at returning ⊢

/-- Every source-valid abstract commit enters a returning state. -/
theorem returning_after_of_operationCommit
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (commit : event.IsOperationCommit) :
    Returning after := by
  cases step <;>
    simp [TraceEvent.IsOperationCommit, Returning] at commit ⊢

/--
Every scheduled step of an active operation either emits a liveness boundary
or strictly decreases a rank bounded by two.

In particular, spurious and mismatching weak-CAS failures are boundaries;
they cannot be hidden as unbounded "local computation."
-/
theorem livenessBoundary_or_controlRank_decreases
    {thread : ThreadId}
    {before after : LocalState α}
    {event : TraceEvent α}
    (step : LocalStep thread before event after)
    (active : Active before) :
    event.IsLivenessBoundary ∨
      controlRank after < controlRank before := by
  cases step <;>
    simp [Active, TraceEvent.IsLivenessBoundary,
      TraceEvent.IsCASAttempt, TraceEvent.IsDecisiveLoad,
      TraceEvent.IsResponse, controlRank] at active ⊢

end LocalStep

end WeakMemory.TreiberC11V1
