import WeakMemory.MSQueueSpec
import WeakMemory.MultiLocationRC11

namespace WeakMemory.MSQueue

/-!
# Source-shaped reclamation-free Michael--Scott queue

This module defines the local control flow and exact atomic labels of the
Michael--Scott algorithm.  It does not yet choose reads-from or modification
order and therefore makes no RC11-validity or linearizability claim by itself.

Nodes are never reclaimed or reused.  A later global execution layer will
enforce freshness and immutable payloads; this local layer retains the node
and operation identities needed for that proof.
-/

inductive Ptr where
  | null
  | node (id : NodeId)
  deriving Repr, DecidableEq

namespace Source

abbrev ThreadId := Nat
abbrev OperationId := Nat
abbrev EventId := Nat

/-!
Atomic labels are stage-specific so the empty-dequeue linearization point can
be recovered from an event without consulting a later state.  Every CAS label
records the value actually observed and whether it succeeded.  Local-step
rules force equality on success but deliberately allow equality on failure.
-/
inductive AtomicAction (Value : Type) where
  | initializeNext
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
  | enqueueTailLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | enqueueNextLoad
      (thread : ThreadId)
      (operation : OperationId)
      (tail : NodeId)
      (observed : Ptr)
  | enqueueTailValidate
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | enqueueLinkCAS
      (thread : ThreadId)
      (operation : OperationId)
      (tail node : NodeId)
      (value : Value)
      (observed : Ptr)
      (succeeded : Bool)
  | enqueueHelpTailCAS
      (thread : ThreadId)
      (operation : OperationId)
      (expected desired : NodeId)
      (observed : Ptr)
      (succeeded : Bool)
  | enqueueFinishTailCAS
      (thread : ThreadId)
      (operation : OperationId)
      (expected desired : NodeId)
      (observed : Ptr)
      (succeeded : Bool)
  | dequeueHeadLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | dequeueTailLoad
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | dequeueNextLoad
      (thread : ThreadId)
      (operation : OperationId)
      (head : NodeId)
      (observed : Ptr)
  | dequeueHeadValidate
      (thread : ThreadId)
      (operation : OperationId)
      (observed : Ptr)
  | dequeueHeadValidateEmpty
      (thread : ThreadId)
      (operation : OperationId)
      (head : NodeId)
      (nextRead : EventId)
  | dequeueHelpTailCAS
      (thread : ThreadId)
      (operation : OperationId)
      (expected desired : NodeId)
      (observed : Ptr)
      (succeeded : Bool)
  | dequeueHeadCAS
      (thread : ThreadId)
      (operation : OperationId)
      (expected desired : NodeId)
      (value : Value)
      (observed : Ptr)
      (succeeded : Bool)
  deriving Repr, DecidableEq

namespace AtomicAction

def thread : AtomicAction Value → ThreadId
  | .initializeNext thread ..
  | .enqueueTailLoad thread ..
  | .enqueueNextLoad thread ..
  | .enqueueTailValidate thread ..
  | .enqueueLinkCAS thread ..
  | .enqueueHelpTailCAS thread ..
  | .enqueueFinishTailCAS thread ..
  | .dequeueHeadLoad thread ..
  | .dequeueTailLoad thread ..
  | .dequeueNextLoad thread ..
  | .dequeueHeadValidate thread ..
  | .dequeueHeadValidateEmpty thread ..
  | .dequeueHelpTailCAS thread ..
  | .dequeueHeadCAS thread .. => thread

def operation : AtomicAction Value → OperationId
  | .initializeNext _ operation ..
  | .enqueueTailLoad _ operation ..
  | .enqueueNextLoad _ operation ..
  | .enqueueTailValidate _ operation ..
  | .enqueueLinkCAS _ operation ..
  | .enqueueHelpTailCAS _ operation ..
  | .enqueueFinishTailCAS _ operation ..
  | .dequeueHeadLoad _ operation ..
  | .dequeueTailLoad _ operation ..
  | .dequeueNextLoad _ operation ..
  | .dequeueHeadValidate _ operation ..
  | .dequeueHeadValidateEmpty _ operation ..
  | .dequeueHelpTailCAS _ operation ..
  | .dequeueHeadCAS _ operation .. => operation

def site : AtomicAction Value → Site
  | .initializeNext _ _ node => .next node
  | .enqueueNextLoad _ _ tail _ => .next tail
  | .enqueueLinkCAS _ _ tail _ _ _ _ => .next tail
  | .dequeueNextLoad _ _ head _ => .next head
  | .enqueueTailLoad ..
  | .enqueueTailValidate ..
  | .enqueueHelpTailCAS ..
  | .enqueueFinishTailCAS ..
  | .dequeueTailLoad ..
  | .dequeueHelpTailCAS .. => .tail
  | .dequeueHeadLoad ..
  | .dequeueHeadValidate ..
  | .dequeueHeadValidateEmpty ..
  | .dequeueHeadCAS .. => .head

/-- Atomic projection into the reusable multi-location core. -/
def access : AtomicAction Value → MultiLocationRC11.Access Ptr
  | .initializeNext _ _ _ => .initial .null
  | .enqueueTailLoad _ _ observed
  | .enqueueNextLoad _ _ _ observed
  | .enqueueTailValidate _ _ observed
  | .dequeueHeadLoad _ _ observed
  | .dequeueTailLoad _ _ observed
  | .dequeueNextLoad _ _ _ observed
  | .dequeueHeadValidate _ _ observed => .load observed
  | .dequeueHeadValidateEmpty _ _ head _ => .load (.node head)
  | .enqueueLinkCAS _ _ _ node _ observed true =>
      .rmw observed (.node node)
  | .enqueueLinkCAS _ _ _ _ _ observed false => .load observed
  | .enqueueHelpTailCAS _ _ _ desired observed true
  | .enqueueFinishTailCAS _ _ _ desired observed true
  | .dequeueHelpTailCAS _ _ _ desired observed true =>
      .rmw observed (.node desired)
  | .enqueueHelpTailCAS _ _ _ _ observed false
  | .enqueueFinishTailCAS _ _ _ _ observed false
  | .dequeueHelpTailCAS _ _ _ _ observed false => .load observed
  | .dequeueHeadCAS _ _ _ desired _ observed true =>
      .rmw observed (.node desired)
  | .dequeueHeadCAS _ _ _ _ _ observed false => .load observed

/-- Sufficient, intentionally non-minimal RA orders. -/
def order : AtomicAction Value → MemoryOrder
  | .initializeNext .. => .relaxed
  | .enqueueTailLoad ..
  | .enqueueNextLoad ..
  | .enqueueTailValidate ..
  | .dequeueHeadLoad ..
  | .dequeueTailLoad ..
  | .dequeueNextLoad ..
  | .dequeueHeadValidate ..
  | .dequeueHeadValidateEmpty .. => .acquire
  | .enqueueLinkCAS _ _ _ _ _ _ true
  | .enqueueHelpTailCAS _ _ _ _ _ true
  | .enqueueFinishTailCAS _ _ _ _ _ true
  | .dequeueHelpTailCAS _ _ _ _ _ true
  | .dequeueHeadCAS _ _ _ _ _ _ true => .acqRel
  | .enqueueLinkCAS _ _ _ _ _ _ false
  | .enqueueHelpTailCAS _ _ _ _ _ false
  | .enqueueFinishTailCAS _ _ _ _ _ false
  | .dequeueHelpTailCAS _ _ _ _ _ false
  | .dequeueHeadCAS _ _ _ _ _ _ false => .acquire

def succeededCAS : AtomicAction Value → Bool
  | .enqueueLinkCAS _ _ _ _ _ _ succeeded
  | .enqueueHelpTailCAS _ _ _ _ _ succeeded
  | .enqueueFinishTailCAS _ _ _ _ _ succeeded
  | .dequeueHelpTailCAS _ _ _ _ _ succeeded
  | .dequeueHeadCAS _ _ _ _ _ _ succeeded => succeeded
  | _ => false

/-- The compare operands retained by every source-level CAS label. -/
structure CASView where
  expected : Ptr
  observed : Ptr
  succeeded : Bool
  deriving Repr, DecidableEq

def casView? : AtomicAction Value → Option CASView
  | .enqueueLinkCAS _ _ _ _ _ observed succeeded =>
      some ⟨.null, observed, succeeded⟩
  | .enqueueHelpTailCAS _ _ expected _ observed succeeded
  | .enqueueFinishTailCAS _ _ expected _ observed succeeded
  | .dequeueHelpTailCAS _ _ expected _ observed succeeded =>
      some ⟨.node expected, observed, succeeded⟩
  | .dequeueHeadCAS _ _ expected _ _ observed succeeded =>
      some ⟨.node expected, observed, succeeded⟩
  | _ => none

def IsMatchingCAS (action : AtomicAction Value) : Prop :=
  ∃ view,
    action.casView? = some view ∧ view.observed = view.expected

def IsSpuriousFailure (action : AtomicAction Value) : Prop :=
  ∃ view,
    action.casView? = some view ∧
      view.observed = view.expected ∧ view.succeeded = false

def IsMismatchFailure (action : AtomicAction Value) : Prop :=
  ∃ view,
    action.casView? = some view ∧
      view.observed ≠ view.expected ∧ view.succeeded = false

def IsMalformedSuccess (action : AtomicAction Value) : Prop :=
  ∃ view,
    action.casView? = some view ∧
      view.observed ≠ view.expected ∧ view.succeeded = true

/-- Every source label stays inside the advertised non-SC RA fragment. -/
theorem access_allows_order
    (action : AtomicAction Value) :
    action.access.Allows action.order := by
  cases action with
  | initializeNext => trivial
  | enqueueTailLoad => trivial
  | enqueueNextLoad => trivial
  | enqueueTailValidate => trivial
  | enqueueLinkCAS _ _ _ _ _ _ succeeded =>
      cases succeeded <;> trivial
  | enqueueHelpTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;> trivial
  | enqueueFinishTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;> trivial
  | dequeueHeadLoad => trivial
  | dequeueTailLoad => trivial
  | dequeueNextLoad => trivial
  | dequeueHeadValidate => trivial
  | dequeueHeadValidateEmpty => trivial
  | dequeueHelpTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;> trivial
  | dequeueHeadCAS _ _ _ _ _ _ succeeded =>
      cases succeeded <;> trivial

/-- Exactly successful CAS labels project to RC11 RMW accesses. -/
theorem access_isRMW_iff_succeededCAS
    (action : AtomicAction Value) :
    action.access.IsRMW ↔ action.succeededCAS = true := by
  cases action with
  | initializeNext =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueTailLoad =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueNextLoad =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueTailValidate =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueLinkCAS _ _ _ _ _ _ succeeded =>
      cases succeeded <;>
        simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueHelpTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;>
        simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | enqueueFinishTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;>
        simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueHeadLoad =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueTailLoad =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueNextLoad =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueHeadValidate =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueHeadValidateEmpty =>
      simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueHelpTailCAS _ _ _ _ _ succeeded =>
      cases succeeded <;>
        simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]
  | dequeueHeadCAS _ _ _ _ _ _ succeeded =>
      cases succeeded <;>
        simp [access, succeededCAS, MultiLocationRC11.Access.IsRMW]

theorem spuriousFailure_isMatching
    {action : AtomicAction Value}
    (spurious : action.IsSpuriousFailure) :
    action.IsMatchingCAS := by
  rcases spurious with ⟨view, selected, matching, _⟩
  exact ⟨view, selected, matching⟩

end AtomicAction

structure AtomicOccurrence (Value : Type) where
  id : EventId
  action : AtomicAction Value
  deriving Repr, DecidableEq

namespace AtomicOccurrence

/-!
A commit may be validated after its actual linearization point.  This matters
for empty dequeue: the null `head.next` load is the point, while a later Head
reload validates that the observation belongs to a stable snapshot.
-/
structure CommitRecord (Value : Type) where
  thread : ThreadId
  operation : OperationId
  point : EventId
  validation : EventId
  commit : Commit Value
  deriving Repr, DecidableEq

def toRC11Atom
    (occurrence : AtomicOccurrence Value) :
    MultiLocationRC11.Atom Site Ptr where
  id := occurrence.id
  thread? := some occurrence.action.thread
  location := occurrence.action.site
  access := occurrence.action.access
  order := occurrence.action.order

theorem toRC11Atom_orderSupported
    (occurrence : AtomicOccurrence Value) :
    occurrence.toRC11Atom.access.Allows
      occurrence.toRC11Atom.order :=
  occurrence.action.access_allows_order

def commitRecord?
    (occurrence : AtomicOccurrence Value) :
    Option (CommitRecord Value) :=
  match occurrence.action with
  | .enqueueLinkCAS thread operation _ _ value _ true =>
      some {
        thread := thread
        operation := operation
        point := occurrence.id
        validation := occurrence.id
        commit := .enqueue value
      }
  | .dequeueHeadCAS thread operation _ _ value _ true =>
      some {
        thread := thread
        operation := operation
        point := occurrence.id
        validation := occurrence.id
        commit := .dequeueValue value
      }
  | .dequeueHeadValidateEmpty thread operation _ nextRead =>
      some {
        thread := thread
        operation := operation
        point := nextRead
        validation := occurrence.id
        commit := .dequeueEmpty
      }
  | _ => none

end AtomicOccurrence

inductive TraceEvent (Value : Type) where
  | invokeEnqueue
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (value : Value)
  | initializePayload
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (value : Value)
  | invokeDequeue
      (thread : ThreadId)
      (operation : OperationId)
  | atomic (occurrence : AtomicOccurrence Value)
  | readPayload
      (thread : ThreadId)
      (operation : OperationId)
      (node : NodeId)
      (value : Value)
  | respondEnqueue
      (thread : ThreadId)
      (operation : OperationId)
  | respondDequeue
      (thread : ThreadId)
      (operation : OperationId)
      (result : Option Value)
  deriving Repr, DecidableEq

namespace TraceEvent

def thread : TraceEvent Value → ThreadId
  | .invokeEnqueue thread ..
  | .initializePayload thread ..
  | .invokeDequeue thread ..
  | .readPayload thread ..
  | .respondEnqueue thread ..
  | .respondDequeue thread .. => thread
  | .atomic occurrence => occurrence.action.thread

def operation : TraceEvent Value → OperationId
  | .invokeEnqueue _ operation ..
  | .initializePayload _ operation ..
  | .invokeDequeue _ operation
  | .readPayload _ operation ..
  | .respondEnqueue _ operation
  | .respondDequeue _ operation .. => operation
  | .atomic occurrence => occurrence.action.operation

def commitRecord? : TraceEvent Value → Option (AtomicOccurrence.CommitRecord Value)
  | .atomic occurrence => occurrence.commitRecord?
  | _ => none

end TraceEvent

/-!
One thread's local variables and source program counter.  Calls and responses
remain explicit and distinct from commits.
-/
inductive LocalState (Value : Type) where
  | idle
  | enqueueWritingPayload
      (operation : OperationId) (node : NodeId) (value : Value)
  | enqueueInitializingNext
      (operation : OperationId) (node : NodeId) (value : Value)
  | enqueueLoadingTail
      (operation : OperationId) (node : NodeId) (value : Value)
  | enqueueLoadingNext
      (operation : OperationId) (node : NodeId) (value : Value)
      (tail : NodeId)
  | enqueueValidatingTail
      (operation : OperationId) (node : NodeId) (value : Value)
      (tail : NodeId) (next : Ptr)
  | enqueueLinking
      (operation : OperationId) (node : NodeId) (value : Value)
      (tail : NodeId)
  | enqueueHelpingTail
      (operation : OperationId) (node : NodeId) (value : Value)
      (expected desired : NodeId)
  | enqueueFinishingTail
      (operation : OperationId) (node : NodeId) (value : Value)
      (expected : NodeId)
  | enqueueReturning (operation : OperationId)
  | dequeueLoadingHead (operation : OperationId)
  | dequeueLoadingTail (operation : OperationId) (head : NodeId)
  | dequeueLoadingNext
      (operation : OperationId) (head tail : NodeId)
  | dequeueValidatingHead
      (operation : OperationId) (head tail : NodeId)
      (nextRead : EventId) (next : Ptr)
  | dequeueHelpingTail
      (operation : OperationId) (expected desired : NodeId)
  | dequeueReadingPayload
      (operation : OperationId) (head next : NodeId)
  | dequeueSwingingHead
      (operation : OperationId) (head next : NodeId) (value : Value)
  | dequeueReturning
      (operation : OperationId) (result : Option Value)
  deriving Repr, DecidableEq

/-- Exact one-thread source-control transition. -/
inductive LocalStep (thread : ThreadId) :
    LocalState Value → TraceEvent Value → LocalState Value → Prop where
  | beginEnqueue (operation node) (value : Value) :
      LocalStep thread .idle
        (.invokeEnqueue thread operation node value)
        (.enqueueWritingPayload operation node value)
  | initializePayload (operation node) (value : Value) :
      LocalStep thread
        (.enqueueWritingPayload operation node value)
        (.initializePayload thread operation node value)
        (.enqueueInitializingNext operation node value)
  | initializeNext (id operation node) (value : Value) :
      LocalStep thread
        (.enqueueInitializingNext operation node value)
        (.atomic ⟨id, .initializeNext thread operation node⟩)
        (.enqueueLoadingTail operation node value)
  | enqueueTailLoad (id operation node) (value : Value) (tail : NodeId) :
      LocalStep thread
        (.enqueueLoadingTail operation node value)
        (.atomic ⟨id,
          .enqueueTailLoad thread operation (.node tail)⟩)
        (.enqueueLoadingNext operation node value tail)
  | enqueueNextLoad
      (id operation node) (value : Value) (tail : NodeId) (next : Ptr) :
      LocalStep thread
        (.enqueueLoadingNext operation node value tail)
        (.atomic ⟨id,
          .enqueueNextLoad thread operation tail next⟩)
        (.enqueueValidatingTail operation node value tail next)
  | enqueueTailChanged
      (id operation node) (value : Value)
      (tail actual : NodeId)
      (next : Ptr)
      (changed : actual ≠ tail) :
      LocalStep thread
        (.enqueueValidatingTail operation node value tail next)
        (.atomic ⟨id,
          .enqueueTailValidate thread operation (.node actual)⟩)
        (.enqueueLoadingTail operation node value)
  | enqueueTailStableNull
      (id operation node) (value : Value) (tail : NodeId) :
      LocalStep thread
        (.enqueueValidatingTail operation node value tail .null)
        (.atomic ⟨id,
          .enqueueTailValidate thread operation (.node tail)⟩)
        (.enqueueLinking operation node value tail)
  | enqueueTailStableNode
      (id operation node) (value : Value) (tail next : NodeId) :
      LocalStep thread
        (.enqueueValidatingTail operation node value tail (.node next))
        (.atomic ⟨id,
          .enqueueTailValidate thread operation (.node tail)⟩)
        (.enqueueHelpingTail operation node value tail next)
  | enqueueLinkSuccess
      (id operation node) (value : Value) (tail : NodeId) :
      LocalStep thread
        (.enqueueLinking operation node value tail)
        (.atomic ⟨id,
          .enqueueLinkCAS thread operation tail node value .null true⟩)
        (.enqueueFinishingTail operation node value tail)
  | enqueueLinkFailure
      (id operation node) (value : Value) (tail : NodeId)
      (observed : Ptr) :
      LocalStep thread
        (.enqueueLinking operation node value tail)
        (.atomic ⟨id,
          .enqueueLinkCAS thread operation tail node value observed false⟩)
        (.enqueueLoadingTail operation node value)
  | enqueueHelpTailSuccess
      (id operation node) (value : Value) (expected desired : NodeId) :
      LocalStep thread
        (.enqueueHelpingTail operation node value expected desired)
        (.atomic ⟨id,
          .enqueueHelpTailCAS thread operation expected desired
            (.node expected) true⟩)
        (.enqueueLoadingTail operation node value)
  | enqueueHelpTailFailure
      (id operation node) (value : Value) (expected desired : NodeId)
      (observed : Ptr) :
      LocalStep thread
        (.enqueueHelpingTail operation node value expected desired)
        (.atomic ⟨id,
          .enqueueHelpTailCAS thread operation expected desired
            observed false⟩)
        (.enqueueLoadingTail operation node value)
  | enqueueFinishTailSuccess
      (id operation node) (value : Value) (expected : NodeId) :
      LocalStep thread
        (.enqueueFinishingTail operation node value expected)
        (.atomic ⟨id,
          .enqueueFinishTailCAS thread operation expected node
            (.node expected) true⟩)
        (.enqueueReturning operation)
  | enqueueFinishTailFailure
      (id operation node) (value : Value) (expected : NodeId)
      (observed : Ptr) :
      LocalStep thread
        (.enqueueFinishingTail operation node value expected)
        (.atomic ⟨id,
          .enqueueFinishTailCAS thread operation expected node
            observed false⟩)
        (.enqueueReturning operation)
  | finishEnqueue (operation : OperationId) :
      LocalStep thread
        (.enqueueReturning operation)
        (.respondEnqueue thread operation)
        .idle
  | beginDequeue (operation : OperationId) :
      LocalStep thread .idle
        (.invokeDequeue thread operation)
        (.dequeueLoadingHead operation)
  | dequeueHeadLoad (id operation head : Nat) :
      LocalStep thread
        (.dequeueLoadingHead operation)
        (.atomic ⟨id,
          .dequeueHeadLoad thread operation (.node head)⟩)
        (.dequeueLoadingTail operation head)
  | dequeueTailLoad (id operation head tail : Nat) :
      LocalStep thread
        (.dequeueLoadingTail operation head)
        (.atomic ⟨id,
          .dequeueTailLoad thread operation (.node tail)⟩)
        (.dequeueLoadingNext operation head tail)
  | dequeueNextLoad
      (id operation head tail : Nat) (next : Ptr) :
      LocalStep thread
        (.dequeueLoadingNext operation head tail)
        (.atomic ⟨id,
          .dequeueNextLoad thread operation head next⟩)
        (.dequeueValidatingHead operation head tail id next)
  | dequeueHeadChanged
      (id operation head tail actual : Nat)
      (nextRead : EventId)
      (next : Ptr)
      (changed : actual ≠ head) :
      LocalStep thread
        (.dequeueValidatingHead operation head tail nextRead next)
        (.atomic ⟨id,
          .dequeueHeadValidate thread operation (.node actual)⟩)
        (.dequeueLoadingHead operation)
  | dequeueEmpty
      (id operation head : Nat) (nextRead : EventId) :
      LocalStep thread
        (.dequeueValidatingHead operation head head nextRead .null)
        (.atomic ⟨id,
          .dequeueHeadValidateEmpty thread operation head nextRead⟩)
        (.dequeueReturning operation none)
  | dequeueNeedsHelp
      (id operation head next : Nat) (nextRead : EventId) :
      LocalStep thread
        (.dequeueValidatingHead operation head head nextRead (.node next))
        (.atomic ⟨id,
          .dequeueHeadValidate thread operation (.node head)⟩)
        (.dequeueHelpingTail operation head next)
  | dequeueNonempty
      (id operation head tail next : Nat)
      (nextRead : EventId)
      (different : head ≠ tail) :
      LocalStep thread
        (.dequeueValidatingHead operation head tail nextRead (.node next))
        (.atomic ⟨id,
          .dequeueHeadValidate thread operation (.node head)⟩)
        (.dequeueReadingPayload operation head next)
  | dequeueHelpTailSuccess
      (id operation expected desired : Nat) :
      LocalStep thread
        (.dequeueHelpingTail operation expected desired)
        (.atomic ⟨id,
          .dequeueHelpTailCAS thread operation expected desired
            (.node expected) true⟩)
        (.dequeueLoadingHead operation)
  | dequeueHelpTailFailure
      (id operation expected desired : Nat) (observed : Ptr) :
      LocalStep thread
        (.dequeueHelpingTail operation expected desired)
        (.atomic ⟨id,
          .dequeueHelpTailCAS thread operation expected desired
            observed false⟩)
        (.dequeueLoadingHead operation)
  | readPayload
      (operation head next : Nat) (value : Value) :
      LocalStep thread
        (.dequeueReadingPayload operation head next)
        (.readPayload thread operation next value)
        (.dequeueSwingingHead operation head next value)
  | dequeueHeadSuccess
      (id operation head next : Nat) (value : Value) :
      LocalStep thread
        (.dequeueSwingingHead operation head next value)
        (.atomic ⟨id,
          .dequeueHeadCAS thread operation head next value
            (.node head) true⟩)
        (.dequeueReturning operation (some value))
  | dequeueHeadFailure
      (id operation head next : Nat) (value : Value) (observed : Ptr) :
      LocalStep thread
        (.dequeueSwingingHead operation head next value)
        (.atomic ⟨id,
          .dequeueHeadCAS thread operation head next value
            observed false⟩)
        (.dequeueLoadingHead operation)
  | finishDequeue (operation : OperationId) (result : Option Value) :
      LocalStep thread
        (.dequeueReturning operation result)
        (.respondDequeue thread operation result)
        .idle

/-- Compare-equal weak failure is admitted at the enqueue link site. -/
theorem enqueueLink_spuriousFailure
    (thread id operation node tail : Nat)
    (value : Value) :
    LocalStep thread
      (.enqueueLinking operation node value tail)
      (.atomic ⟨id,
        .enqueueLinkCAS thread operation tail node value .null false⟩)
      (.enqueueLoadingTail operation node value) :=
  .enqueueLinkFailure id operation node value tail .null

/-- Compare-equal weak failure is admitted at the dequeue head site. -/
theorem dequeueHead_spuriousFailure
    (thread id operation head next : Nat)
    (value : Value) :
    LocalStep thread
      (.dequeueSwingingHead operation head next value)
      (.atomic ⟨id,
        .dequeueHeadCAS thread operation head next value
          (.node head) false⟩)
      (.dequeueLoadingHead operation) :=
  .dequeueHeadFailure id operation head next value (.node head)

/-- A finite per-thread source prefix; its final call may remain pending. -/
inductive Run (thread : ThreadId) :
    LocalState Value → List (TraceEvent Value) → LocalState Value → Prop where
  | nil (state : LocalState Value) :
      Run thread state [] state
  | cons
      {initial middle final : LocalState Value}
      (event : TraceEvent Value)
      (rest : List (TraceEvent Value))
      (first : LocalStep thread initial event middle)
      (later : Run thread middle rest final) :
      Run thread initial (event :: rest) final

namespace Run

theorem localStep_of_mem
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    {event : TraceEvent Value}
    (member : event ∈ events) :
    ∃ before after,
      LocalStep thread before event after := by
  induction run with
  | nil state => simp at member
  | cons current rest first later inductionHypothesis =>
      simp at member
      rcases member with rfl | member
      · exact ⟨_, _, first⟩
      · exact inductionHypothesis member

/--
Factor a local run at an arbitrary represented event.  Unlike
`localStep_of_mem`, this retains the prefix and suffix runs, allowing later
refinement proofs to recover the control-flow provenance of a CAS or a
validation from the surrounding method attempt.
-/
theorem factor_of_mem
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    {event : TraceEvent Value}
    (member : event ∈ events) :
    ∃ beforeEvents beforeState afterState afterEvents,
      events = beforeEvents ++ event :: afterEvents ∧
        Run thread initial beforeEvents beforeState ∧
        LocalStep thread beforeState event afterState ∧
        Run thread afterState afterEvents final := by
  induction run with
  | nil state => simp at member
  | @cons initial middle final current rest first later
      inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with currentIsEvent | memberInRest
      · subst current
        exact ⟨[], initial, middle, rest, rfl, .nil initial,
          first, later⟩
      · obtain ⟨beforeEvents, beforeState, afterState, afterEvents,
          restShape, beforeRun, eventStep, afterRun⟩ :=
          inductionHypothesis memberInRest
        refine ⟨current :: beforeEvents, beforeState, afterState,
          afterEvents, ?_, ?_, eventStep, afterRun⟩
        · simp [restShape]
        · exact .cons current beforeEvents first beforeRun

/-- Recover the final transition of a nonempty local run. -/
theorem lastStep_of_ne_nil
    {thread : ThreadId}
    {initial final : LocalState Value}
    {events : List (TraceEvent Value)}
    (run : Run thread initial events final)
    (nonempty : events ≠ []) :
    ∃ beforeEvents beforeState lastEvent,
      events = beforeEvents ++ [lastEvent] ∧
        Run thread initial beforeEvents beforeState ∧
        LocalStep thread beforeState lastEvent final := by
  induction run with
  | nil state => exact (nonempty rfl).elim
  | @cons initial middle final current rest first later
      inductionHypothesis =>
      cases rest with
      | nil =>
          cases later
          exact ⟨[], initial, current, rfl, .nil initial, first⟩
      | cons next remaining =>
          obtain ⟨beforeEvents, beforeState, lastEvent, restShape,
              beforeRun, lastStep⟩ :=
            inductionHypothesis (by simp)
          refine ⟨current :: beforeEvents, beforeState, lastEvent,
            ?_, ?_, lastStep⟩
          · simp [restShape]
          · exact .cons current beforeEvents first beforeRun

end Run

/-- Source-generated successful labels cannot use mismatched compare values. -/
theorem LocalStep.successfulCAS_isMatching
    {thread : ThreadId}
    {initial final : LocalState Value}
    {occurrence : AtomicOccurrence Value}
    (step :
      LocalStep thread initial (.atomic occurrence) final)
    (successful : occurrence.action.succeededCAS = true) :
    occurrence.action.IsMatchingCAS := by
  cases step <;>
    simp_all [AtomicAction.succeededCAS, AtomicAction.IsMatchingCAS,
      AtomicAction.casView?]

/-- Consequently the malformed-success shape is absent from every local run. -/
theorem LocalStep.not_malformedSuccess
    {thread : ThreadId}
    {initial final : LocalState Value}
    {occurrence : AtomicOccurrence Value}
    (step :
      LocalStep thread initial (.atomic occurrence) final) :
    ¬ occurrence.action.IsMalformedSuccess := by
  cases step <;>
    simp_all [AtomicAction.IsMalformedSuccess,
      AtomicAction.casView?]

end Source

end WeakMemory.MSQueue
