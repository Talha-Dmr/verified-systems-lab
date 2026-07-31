import WeakMemory.InfiniteExecution

namespace WeakMemory.WeakCAS

/-!
# Site-indexed weak-CAS progress rule

This module gives the multi-location form of the reusable weak-CAS progress
argument.  Attempts and successes carry an explicit logical CAS site.  The
site chosen on a response-free suffix must eventually have no later
modification and receive compare-equal attempts arbitrarily late.  Primitive
justice is then applied at that same stable site.

The shared site index prevents an unrelated modification or success at another
location from discharging the justice obligation of the active retry loop.
Sites are logical identities rather than raw addresses, so clients may include
an allocation generation when address reuse matters.
-/

namespace SiteProgressRule

/-- Observable predicates needed by the site-indexed system-progress rule. -/
structure Interface (Thread Site : Type) where
  active : Nat → Thread → Prop
  response : Nat → Prop
  succeededAt : Site → Nat → Prop
  /--
  Every event that changes the site's supplying-write generation.  Clients
  must include same-valued writes and both legs of any ABA-shaped change, not
  merely events that change the currently stored value.
  -/
  modifiedAt : Site → Nat → Prop
  /-- Every successful weak CAS is recorded as a site modification. -/
  success_is_modification :
    ∀ site time, succeededAt site time → modifiedAt site time
  matchingAttemptAt : Thread → Site → Nat → Prop

/-- No method response occurs at or after `start`. -/
def NoResponseFrom
    (system : Interface Thread Site)
    (start : Nat) : Prop :=
  ∀ time,
    start ≤ time →
      ¬ system.response time

/-- No primitive success at `site` occurs at or after `start`. -/
def NoSuccessAtFrom
    (system : Interface Thread Site)
    (site : Site)
    (start : Nat) : Prop :=
  ∀ time,
    start ≤ time →
      ¬ system.succeededAt site time

/-- No write or successful RMW modifies `site` at or after `start`. -/
def NoModificationAtFrom
    (system : Interface Thread Site)
    (site : Site)
    (start : Nat) : Prop :=
  ∀ time,
    start ≤ time →
      ¬ system.modifiedAt site time

/-- A modification-free suffix is in particular success-free. -/
theorem noSuccessAtFrom_of_noModificationAtFrom
    (system : Interface Thread Site)
    (site : Site)
    (start : Nat)
    (stable : NoModificationAtFrom system site start) :
    NoSuccessAtFrom system site start := by
  intro time afterStart succeeded
  exact
    stable time afterStart
      (system.success_is_modification site time succeeded)

/--
Primitive weak-CAS justice at one logical site.

When a thread makes compare-equal attempts at `site` arbitrarily late while
the site's supplying-write generation remains stable, one of those conditions
must be broken by a later success at `site`.  Stability is expressed by the
absence of every modification, not merely the absence of successful weak CAS,
so same-valued writes and ABA-shaped changes cannot be hidden.  The definition
deliberately contains no method-response or abstract algorithmic progress
predicate.  Its conclusion is a success at the same site, but not necessarily
a success by the repeatedly attempting thread; the rule targets system
lock-freedom rather than per-thread starvation-freedom.
-/
def PrimitiveJusticeAt
    (system : Interface Thread Site)
    (site : Site) : Prop :=
  ∀ thread start,
    NoModificationAtFrom system site start →
    Liveness.InfinitelyOften
      (system.matchingAttemptAt thread site) →
    ∃ time,
      start ≤ time ∧
        system.succeededAt site time

/-- Primitive weak-CAS justice holds independently at every logical site. -/
def PrimitiveJustice
    (system : Interface Thread Site) : Prop :=
  ∀ site, PrimitiveJusticeAt system site

/--
An owner has a stable pure-spurious suffix at `site`: after one cutoff the site
is never modified, yet compare-equal attempts by that owner occur arbitrarily
late.
-/
def StablePureSpuriousSuffixAt
    (system : Interface Thread Site)
    (site : Site)
    (thread : Thread) : Prop :=
  ∃ cutoff,
    NoModificationAtFrom system site cutoff ∧
      Liveness.InfinitelyOften
        (system.matchingAttemptAt thread site)

/-- No owner has a stable pure-spurious suffix at the selected site. -/
def NoStablePureSpuriousSuffixAt
    (system : Interface Thread Site)
    (site : Site) : Prop :=
  ∀ thread,
    ¬ StablePureSpuriousSuffixAt system site thread

/--
Site justice is exactly the exclusion of stable all-spurious suffixes at that
site.  This equivalence is algorithm-independent.
-/
theorem primitiveJusticeAt_iff_noStablePureSpuriousSuffixAt
    (system : Interface Thread Site)
    (site : Site) :
    PrimitiveJusticeAt system site ↔
      NoStablePureSpuriousSuffixAt system site := by
  constructor
  · intro justice thread stable
    obtain ⟨cutoff, noModification, matching⟩ := stable
    obtain ⟨time, afterCutoff, succeeded⟩ :=
      justice thread cutoff noModification matching
    exact
      noModification time afterCutoff
        (system.success_is_modification site time succeeded)
  · intro noStable thread cutoff noModification matching
    exact False.elim
      (noStable thread ⟨cutoff, noModification, matching⟩)

/--
If every compare-equal attempt at a site succeeds, as for a strong CAS
primitive, primitive justice at that site follows without an extra fairness
assumption.
-/
theorem primitiveJusticeAt_of_matchingAttemptsSucceed
    (system : Interface Thread Site)
    (site : Site)
    (strong :
      ∀ thread time,
        system.matchingAttemptAt thread site time →
          system.succeededAt site time) :
    PrimitiveJusticeAt system site := by
  intro thread start _ matching
  obtain ⟨time, afterStart, attempt⟩ := matching start
  exact ⟨time, afterStart, strong thread time attempt⟩

/-- Strong compare-equal behavior at every site discharges global justice. -/
theorem primitiveJustice_of_matchingAttemptsSucceed
    (system : Interface Thread Site)
    (strong :
      ∀ site thread time,
        system.matchingAttemptAt thread site time →
          system.succeededAt site time) :
    PrimitiveJustice system := by
  intro site
  exact
    primitiveJusticeAt_of_matchingAttemptsSucceed
      system site (strong site)

/-- From every state with an active owner, some later method responds. -/
def SystemResponseProgress
    (system : Interface Thread Site) : Prop :=
  ∀ start,
    (∃ thread, system.active start thread) →
    ∃ time,
      start ≤ time ∧
        system.response time

/--
Algorithm-, scheduler-, and memory-specific obligations consumed by the
site-indexed primitive-justice rule.

The existential packages an eventual cutoff and one progress-relevant site
with both facts needed for the contradiction.  Keeping those facts coupled is
essential: a modification or success at an unrelated site must not discharge
justice for the selected retry site.  The later cutoff admits finitely many
helping modifications before the relevant site stabilizes.  The witness
thread need not own the operation active at `start`, so clients may discharge
system progress through helping.
-/
structure Obligations
    (system : Interface Thread Site) : Prop where
  progressSite_on_responseFreeSuffix :
    ∀ start,
      (∃ owner, system.active start owner) →
      NoResponseFrom system start →
      ∃ witnessThread,
        ∃ cutoff,
          start ≤ cutoff ∧
            ∃ site,
              NoModificationAtFrom system site cutoff ∧
                Liveness.InfinitelyOften
                  (system.matchingAttemptAt witnessThread site)

/--
Generic multi-location weak-CAS system-progress theorem.

A hypothetical response-free active suffix selects a later cutoff and one
logical site.  The site is not modified after that cutoff but has arbitrarily
late matching attempts.  Site-wise primitive justice yields a success, hence
a modification, at the same site, a contradiction.
-/
theorem systemResponseProgress_of_siteJustice
    (system : Interface Thread Site)
    (obligations : Obligations system)
    (justice : PrimitiveJustice system) :
    SystemResponseProgress system := by
  intro start active
  by_cases responds :
      ∃ time,
        start ≤ time ∧
          system.response time
  · exact responds
  · have noResponse :
        NoResponseFrom system start := by
      intro time afterStart response
      exact responds ⟨time, afterStart, response⟩
    obtain ⟨thread, cutoff, _, site, noModification, matching⟩ :=
      obligations.progressSite_on_responseFreeSuffix
        start active noResponse
    obtain ⟨time, afterStart, succeeded⟩ :=
      justice site thread cutoff noModification matching
    exact False.elim
      (noModification time afterStart
        (system.success_is_modification site time succeeded))

end SiteProgressRule

end WeakMemory.WeakCAS
