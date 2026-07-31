import WeakMemory.WeakCASTwoSite

namespace WeakMemory.WeakCASSiteResult

/-!
# Public theorem surface for site-indexed weak-CAS progress

This module collects the generic multi-location rule, its strong-CAS
specialization, the conservative single-site embedding, and the two-site
positive and negative validation results.
-/

/-- Generic system progress from coupled site obligations and per-site justice. -/
theorem siteIndexedSystemResponseProgress
    (system :
      WeakCAS.SiteProgressRule.Interface Thread Site)
    (obligations :
      WeakCAS.SiteProgressRule.Obligations system)
    (justice :
      WeakCAS.SiteProgressRule.PrimitiveJustice system) :
    WeakCAS.SiteProgressRule.SystemResponseProgress system :=
  WeakCAS.SiteProgressRule.systemResponseProgress_of_siteJustice
    system obligations justice

/-- Strong compare-equal CAS behavior discharges the primitive justice layer. -/
theorem strongCASSystemResponseProgress
    (system :
      WeakCAS.SiteProgressRule.Interface Thread Site)
    (obligations :
      WeakCAS.SiteProgressRule.Obligations system)
    (strong :
      ∀ site thread time,
        system.matchingAttemptAt thread site time →
          system.succeededAt site time) :
    WeakCAS.SiteProgressRule.SystemResponseProgress system :=
  siteIndexedSystemResponseProgress
    system obligations
    (WeakCAS.SiteProgressRule.primitiveJustice_of_matchingAttemptsSucceed
      system strong)

/-- Per-site justice is exactly exclusion of a stable pure-spurious suffix. -/
theorem siteJusticeExact
    (system :
      WeakCAS.SiteProgressRule.Interface Thread Site)
    (site : Site) :
    WeakCAS.SiteProgressRule.PrimitiveJusticeAt system site ↔
      WeakCAS.SiteProgressRule.NoStablePureSpuriousSuffixAt
        system site :=
  WeakCAS.SiteProgressRule.primitiveJusticeAt_iff_noStablePureSpuriousSuffixAt
    system site

/-- The old primitive-justice contract agrees with the `Unit` site embedding. -/
theorem singleSiteJusticeConservative
    (system : WeakCAS.ProgressRule.Interface Thread) :
    WeakCAS.ProgressRule.PrimitiveJustice system ↔
      WeakCAS.SiteProgressRule.PrimitiveJustice
        system.toSiteIndexed :=
  WeakCAS.ProgressRule.primitiveJustice_iff_siteIndexed system

/-- The old response-progress conclusion is unchanged by site embedding. -/
theorem singleSiteProgressConservative
    (system : WeakCAS.ProgressRule.Interface Thread) :
    WeakCAS.ProgressRule.SystemResponseProgress system ↔
      WeakCAS.SiteProgressRule.SystemResponseProgress
        system.toSiteIndexed :=
  WeakCAS.ProgressRule.systemResponseProgress_iff_siteIndexed
    system

/-- Conditional progress for the operational two-site validation client. -/
theorem twoSiteSystemResponseProgress
    (run : WeakCASTwoSite.Run)
    (threadFair : WeakCASTwoSite.WeakThreadFair run)
    (justice :
      WeakCAS.SiteProgressRule.PrimitiveJustice
        (WeakCASTwoSite.interface run)) :
    WeakCAS.SiteProgressRule.SystemResponseProgress
      (WeakCASTwoSite.interface run) :=
  WeakCASTwoSite.systemResponseProgress_of_siteJustice
    run threadFair justice

/-- The positive assumptions coexist with recurring successes at both sites. -/
theorem twoSitePositiveAssumptionsJointlySatisfiable :
    ∃ candidate : WeakCASTwoSite.Run,
      WeakCASTwoSite.WeakThreadFair candidate ∧
        WeakCAS.SiteProgressRule.PrimitiveJustice
          (WeakCASTwoSite.interface candidate) ∧
        Liveness.InfinitelyOften
          ((WeakCASTwoSite.interface candidate).succeededAt
            .left) ∧
        Liveness.InfinitelyOften
          ((WeakCASTwoSite.interface candidate).succeededAt
            .right) ∧
        WeakCAS.SiteProgressRule.SystemResponseProgress
          (WeakCASTwoSite.interface candidate) :=
  ⟨WeakCASTwoSite.SuccessRich.run,
    WeakCASTwoSite.SuccessRich.threadFair,
    WeakCASTwoSite.SuccessRich.primitiveJustice,
    WeakCASTwoSite.SuccessRich.leftSuccesses,
    WeakCASTwoSite.SuccessRich.rightSuccesses,
    WeakCASTwoSite.SuccessRich.responseProgress⟩

/-- Both sites can be fairly scheduled yet fail justice by spurious failure. -/
theorem twoSiteAllSpuriousSeparation :
    ∃ candidate : WeakCASTwoSite.Run,
      WeakCASTwoSite.WeakThreadFair candidate ∧
        WeakCAS.SiteProgressRule.Obligations
          (WeakCASTwoSite.interface candidate) ∧
        ¬ WeakCAS.SiteProgressRule.PrimitiveJustice
          (WeakCASTwoSite.interface candidate) ∧
        ¬ WeakCAS.SiteProgressRule.SystemResponseProgress
          (WeakCASTwoSite.interface candidate) :=
  WeakCASTwoSite.AllSpurious.obligations_do_not_imply_justice_or_progress

/--
Unrelated right-site successes do not discharge left-site justice.  Erasing
sites makes the old global justice predicate true, but the old theorem remains
sound because its global suffix obligation rejects the execution.
-/
theorem wrongSiteErasureSeparation :
    WeakCASTwoSite.WeakThreadFair
        WeakCASTwoSite.WrongSite.run ∧
      WeakCAS.SiteProgressRule.Obligations
        (WeakCASTwoSite.interface WeakCASTwoSite.WrongSite.run) ∧
      WeakCAS.SiteProgressRule.PrimitiveJusticeAt
        (WeakCASTwoSite.interface WeakCASTwoSite.WrongSite.run)
        .right ∧
      (¬ WeakCAS.SiteProgressRule.PrimitiveJusticeAt
        (WeakCASTwoSite.interface WeakCASTwoSite.WrongSite.run)
        .left) ∧
      WeakCAS.ProgressRule.PrimitiveJustice
        WeakCASTwoSite.WrongSite.erasedInterface ∧
      (¬ WeakCAS.ProgressRule.Obligations
        WeakCASTwoSite.WrongSite.erasedInterface) ∧
      (¬ WeakCAS.SiteProgressRule.SystemResponseProgress
        (WeakCASTwoSite.interface
          WeakCASTwoSite.WrongSite.run)) :=
  ⟨WeakCASTwoSite.WrongSite.threadFair,
    WeakCASTwoSite.WrongSite.obligations,
    WeakCASTwoSite.WrongSite.primitiveJusticeAt_right,
    WeakCASTwoSite.WrongSite.notPrimitiveJusticeAt_left,
    WeakCASTwoSite.WrongSite.erasedPrimitiveJustice,
    WeakCASTwoSite.WrongSite.notErasedObligations,
    WeakCASTwoSite.WrongSite.notSystemResponseProgress⟩

end WeakMemory.WeakCASSiteResult
