# Public Formal-Artifact Search Report

Last updated: 2026-07-31

Publication cutoff: 2026-07-31

Status: one broad reproducible public-index pass, one exact RSan metadata
follow-up, and an eleven-artifact source audit complete; coverage limitations
remain

## Question and interpretation

This search tests whether a public source or artifact already contains the
full conjunction in `claim-card.md`, including an RC11 Treiber model, genuine
equal-value spurious CAS failure, a separate primitive-justice premise, an
all-spurious independence execution, unbounded system response progress, and
machine-checked finite-prefix safety.

A zero result below means only that the named interface returned no public hit
for the exact recorded query at the recorded time. It is not evidence that no
matching source exists on an unindexed branch, in an unarchived repository, or
under different terminology.

## Reproducible Zenodo and GitHub run

Run directory:
`data/artifact-runs/20260730T233156Z/`

- Script version: 1
- Script SHA-256:
  `37a55eee411357b0b93e42c6744a92fe5a7c31932467743c58a4579e02e5c2f4`
- Query-catalogue SHA-256:
  `7fd2ec8343458e03726e2475e5fd359e33cedc1dda557a42225bb07af9757385`
- Queries: 20 total; ten Zenodo metadata queries and ten GitHub code
  queries
- Outcome: 20 successful, zero failed
- Preserved public result rows: six, representing four repository or Zenodo
  resources before version/fork collapsing

The earlier 18-query run at `data/artifact-runs/20260730T232113Z/` is
preserved as an immutable baseline. The later run adds focused
persistent-memory/Spirea queries without reinterpreting the earlier result.

The run can be reproduced from this directory with:

```bash
python3 scripts/search_artifact_indexes.py --validate-only
python3 scripts/search_artifact_indexes.py
```

Zenodo responses are preserved verbatim in the ignored local `raw/` cache and
identified by a checksum in `manifest.csv`. GitHub code search uses an
authenticated `gh` client. It filters the response in memory and preserves
only hits whose repository reports `isPrivate == false`; the unfiltered
response is never written.

### Zenodo result disposition

| Resource | Why retrieved | Full-text disposition |
|---|---|---|
| Barbazo and Rival, *Shape Abstraction of Thread Interferences*, Zenodo 21258346 | Formal analysis evaluated on Treiber clients | S25, adjacent. The sound MemCAD analysis checks data-race freedom and linked-list shape preservation. It has no liveness, RC11, weak-CAS, or fairness-separation theorem. |
| Cho et al., *Memento*, Zenodo 7811928; paper DOI 10.1145/3591232 | Formal persistent-memory framework with a Treiber implementation | S26/PA21, adjacent but claim-narrowing. Theorems 3.1 and 3.4 establish detectability and erasure refinement; the implementation uses an exact-match helping CAS on Intel x86. No target weak-CAS or response-progress theorem was located. |

Memento's Zenodo record contains one 7,069,433,008-byte ZIP
(`md5:9eb2203ce292cc89fdc1792b4aa2fa7a`). It was not downloaded into the local
corpus; its paper, artifact metadata, and public description were screened, so
no source-level absence claim is made for that 7 GB image. Likewise, the
3.9 GB Shape Abstraction virtual-machine image was not downloaded; its
standalone public README was retrieved and screened as S25.

In the broad 2026-07-30 pass, the remaining Zenodo queries returned zero
records. Those queries cover weak
CAS with fairness/liveness, formal spurious-CAS terminology, all-spurious or
primitive-justice terminology, memory fairness with RMWs, and prefix-finite
from-read terminology. The added `Z10` query for mechanized persistent-memory
Treiber work also returned zero. Exact query strings and URLs are in
`artifact-index-queries.csv` and the run manifest.

### Exact RSan metadata follow-up

The citation screen promoted Margalit et al.'s RSan paper as S59/PA47 because
§4.1, footnote 3 explicitly supports weak CAS that may fail after reading the
expected value under RC20. Query Z11 was therefore added for the exact artifact
title, `"Robustness Sanitizer"`, and all eleven Zenodo queries were rerun in
`data/artifact-runs/20260731T035000Z-rsan-followup/`.

- All eleven requests succeeded; Z11 returned exactly one untruncated record,
  Zenodo 15002568, version DOI `10.5281/zenodo.15002568`.
- The preserved Z11 response is 4,868 bytes with SHA-256
  `9851df4a45b728543dd3cb3aa81f70205980b2863db41c54187639bbc5c9b65d`.
- The record contains one `rsan.image.docker.tar.zst` payload of
  12,331,288,562 bytes with provider MD5
  `dd9a2d2778747b6d2f4cd04aee22c6da`.
- The run's query snapshot has SHA-256
  `6f7b4a026bc7b746f850545bdaa0975bc503f5a6aa0c02c6aae2eea96596f3e9`;
  `run.json` has SHA-256
  `60360742626ccc27248e3bbbbb5b27ecf93ebac2ccd488450d0c3b3e1a12e542`.

The 12.3 GB compressed Docker image was not downloaded into the fixed local
artifact corpus. The primary paper and exact artifact metadata support the
claim that the tool handles genuine weak CAS, but the audit makes no
source-level absence claim about that image. On the inspected paper-level
evidence, RSan's published dynamic robustness/safety result does not defeat
the candidate: §4.3's blocking `BCAS` annotations omit failed retry events
rather than proving their liveness. The uninspected image remains a coverage
gap.

### Independently recovered Spirea artifact

The independent proof-archive and author-page sweep promoted Vindum and
Birkedal's *Spirea* paper and
[Zenodo artifact 8314888](https://doi.org/10.5281/zenodo.8314888), even though
the focused `Z10` Zenodo metadata query returned zero. This is a concrete
demonstration of the metadata-indexing limitation rather than a reason to
discard the work.

The paper DOI was already present as an unscreened Crossref result for Q12 in
the noisy version-1 pilot. Its promotion therefore also demonstrates why the
remaining open-index candidate tables require record-level decisions.

Spirea is recorded as S27/PA22/A04. Its Coq source verifies a durable Treiber
case under a view-based release/acquire weak-persistent-memory semantics. The
CAS failure head step requires the observed value to differ from the expected
value, and the paper explicitly says the verified stack specification implies
neither linearizability nor LIFO. The case study establishes thread and crash
safety, not liveness or fairness-separated progress.

The active, unprotected
[`high-nextgen-logic`](https://github.com/logsem/spirea/tree/925a8d7a7c69c0c83163fe78d0d93f668e0558ca)
branch was also checked at commit
`925a8d7a7c69c0c83163fe78d0d93f668e0558ca`, dated 2026-07-04. It
substantially expands the durable Treiber history evaluator and paired-pop
reasoning and retains `wp_push`, `wp_pop`, and `wp_sync`; the case-study file
is present in `config/source-list`. The branch still has mismatch-only CAS,
uses ordinary partial-correctness weakest-precondition loop proofs, and
contains no Treiber fairness, termination, lock-freedom, or wait-freedom
result. The Treiber file has no `Admitted` or project `Axiom`, but the branch
has no pull request, commit status, or check run. This is current unreviewed
source evidence, not a publication or a reproduced branch build.

### Independent theorem, author-page, and artifact follow-ups

The exact Zenodo/GitHub queries were supplemented by theorem-level citation
snowballing, author pages, theses, and public project archives. These routes
promoted the following records that repository-name and metadata queries alone
did not reliably expose:

- **A29/PA29, Colvin and Dongol 2007.** The ICTAC paper reports a direct
  PVS-checked Treiber lock-freedom proof based on a global well-founded order.
  Its conclusion is system-wide/existential rather than per-thread progress.
  The publisher abstract and primary-author thesis corroborate the result, but
  the full paper is access-controlled and exact theorem wording remains queued
  for human confirmation.
- **A30/PA30/A05, Colvin and Dongol 2009.** The superseding generic method has
  completed PVS proof families for the Michael–Scott and bounded-array queues.
  Its author-hosted bundle also contains `treiber.pvs`, but no `treiber.prf`,
  and lines 401–412 mark two well-foundedness lemmas “Will not prove.” It is
  not a second completed 2009 Treiber artifact. The fixed archive has MD5
  `d94e3786323df65a194f5279dbcd9cc3` and SHA-256
  `ef949e62e988a57750a9765d44e41b68e988997309cbd4369292d803b3971710`.
- **S28/PA23, Tofan, Schellhorn, and Reif 2011.** The paper and live KIV
  project give machine-checked memory safety, ABA prevention, linearizability,
  and system lock-freedom for a Treiber stack with hazard-pointer reclamation.
  The semantics is interleaving and CAS is exact-match.
- **S33/PA27, Relinche.** The GenMC-backed checker establishes contextual
  refinement for Treiber variants under RC11 for every client within a fixed
  method-invocation bound. This is bounded finite-execution safety, not an
  infinite-execution liveness theorem.
- **S29/PA24, *Will It Fit?*.** Its Coq/IrisFit development places functional
  and heap-space specifications for strong-CAS Treiber beside bounded-time
  allocation-enablement theorems. Those theorems concern garbage collection
  and allocation requests, not push/pop response or lock-freedom.
- **S35/PA28, *Parcas*.** Its public Rocq/Iris development proves Treiber
  linearizability and work/span bounds for fixed participants and a finite
  operation budget. The paper explicitly says this is not a formal proof of
  lock-freedom.
- **S32, *Zoo*, and S34, modular safe memory reclamation.** These current
  Rocq/Coq-Iris developments verify Treiber functional or reclamation safety
  under sequential consistency. Zoo covers three OCaml Treiber variants;
  S34 covers garbage collection, hazard pointers, and RCU. Neither proves
  stack progress, and Zoo lists relaxed memory as future work.
- **S30/PA25, Miri–GenMC.** The thesis's RC11 Treiber benchmark uses strong
  Rust `compare_exchange` and bounded safety/performance exploration. It
  explicitly says GenMC omits compare-equal spurious weak-CAS failures and
  demonstrates a bug the integration misses. The cutoff-pinned GenMC source
  retains the omission and strong-CAS Treiber tests.
- **S31/PA26, *Mirror is Not Strong*.** KIV revealed a genuine durable
  `compare_exchange_weak`: failure may occur even when current and expected
  values agree. The 73-obligation lower Mirror-to-IMirror refinement is
  mechanized; the upper IMirror-to-PLib refinement is explicitly unfinished.
  There is no Treiber client, fairness/justice premise, or progress theorem.
- **S36, Dongol's thesis.** This primary-author source corroborates the
  2007/2009 well-founded-order lineage and its global existential progress
  quantifier, while warning that the 2009 paper's proofs are not reproduced in
  the thesis.
- **S55/PA45/A06, *RoboCop*.** The archived executable artifact contains a
  direct Treiber benchmark under RC20 and the audit reproduced the benchmark's
  structural counts. Both stack operations use
  `atomic_compare_exchange_strong_explicit`. The checked property is
  relaxed-memory-to-SC robustness, a safety boundary; the CAS-to-BCAS
  preprocessing discards independent failed read-only loop iterations and
  cannot be used as evidence for weak-CAS retry-loop liveness.
- **S56/PA46/A07, general-purpose RCU.** The paper uses an
  RCU-protected Treiber stack to illustrate an iRC11 safety argument. The
  archived Rocq source instead identifies mechanized RCU, mutex,
  Michael--Scott queue, and Harris-list developments. Its 156 extracted files
  have no `stack` or `treiber` pathname, and its CAS-failure rule requires
  inequality. The artifact therefore does not establish a machine-checked
  Treiber theorem, genuine weak CAS, or Treiber liveness.
- **S226/PA118/A11, *Promising-ARM/RISC-V*.** The Coq model gives an
  independently enabled store-exclusive failure step: failure has no
  value-mismatch or interference premise. The same supplement contains finite
  C++ and Rust Treiber exploration inputs, but those source programs use
  strong compare-exchange and are not Coq client proofs. The checked results
  establish model equivalence, certification, promise computation, and a
  RISC-V no-outstanding-promises/deadlock-freedom theorem—not Treiber
  linearizability, operation response, primitive justice, or lock-freedom.

These follow-ups defeat broad novelty wording for mechanized Treiber progress,
automated RC11 Treiber safety, Treiber-plus-resource-liveness developments,
mechanized discovery of genuine weak CAS, independent hardware
store-exclusive failure, and direct relaxed-memory Treiber
robustness/safety. None supplies the full
RC11/weak-CAS/primitive-justice/all-spurious/unbounded-response conjunction.

### GitHub result disposition

The exact `cas_weak_fun` query returned:

1. `snu-sf/fairness/src/example/SCM.v`; and
2. `SB1491/fairness-spec/src/example/SCM.v`, with the same blob SHA-1.

The first is the already-screened FOS source and the second is a public fork.
The source-level result is recorded in `artifact-audit.md`: FOS defines and
registers the fair weak-CAS primitive but contains no Treiber use or client
theorem.

The other nine queries returned zero public rows:

- `WeakCASJustice`;
- `"all-spurious"`;
- `compare_exchange_weak Treiber`;
- `"weak CAS" Treiber`;
- `"spurious failure" Treiber`;
- `"memory fairness" CAS`;
- `"prefix-finite" "from-read"`; and
- `Treiber cas_weak`; and
- `Spirea Treiber`.

GitHub's result count is not exposed by the `gh search code --json` interface,
so the manifest deliberately leaves `total_results` blank. A zero row is
therefore a query result, not a completeness certificate for GitHub.

### Targeted Dartagnan follow-up

A citation and repository follow-up from S05 found a relevant implementation
that the exact public-code queries did not retrieve. The audit pins the
following observations to public Dat3M commit
[`a7e3e4843359dde3a0e29500a821030e2433e316`](https://github.com/hernanponcedeleon/Dat3M/tree/a7e3e4843359dde3a0e29500a821030e2433e316),
committed on 2026-06-28 and inspected before the publication cutoff:

1. The nontermination encoder says that events capable of spurious failure
   must succeed in a repeating suffix and enforces this for every potentially
   recurring `RMWStoreExclusive`
   ([source lines 681–686](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/dartagnan/src/main/java/com/dat3m/dartagnan/encoding/NonTerminationEncoder.java#L681-L686)).
2. The current C11 compiler passes the LLVM `strong` flag into the exclusive
   store and updates the success result for a weak operation
   ([source lines 208–228](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/dartagnan/src/main/java/com/dat3m/dartagnan/program/processing/compilation/VisitorC11.java#L208-L228)).
3. The bundled Treiber benchmark calls
   `atomic_compare_exchange_strong_explicit`
   ([source lines 4–8](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/benchmarks/lfds/treiber.h#L4-L8)).
   Its C11 and RC11 regression suites both expect `UNKNOWN`
   ([C11 lines 59–68](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/dartagnan/src/test/java/com/dat3m/dartagnan/llvm/C11LFDSTest.java#L59-L68);
   [RC11 lines 46–55](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/dartagnan/src/test/java/com/dat3m/dartagnan/llvm/RC11LFDSTest.java#L46-L55)).
4. The liveness-enabled VMM regression also expects `UNKNOWN` for the same
   strong-CAS Treiber input
   ([source lines 43–45 and 63–72](https://github.com/hernanponcedeleon/Dat3M/blob/a7e3e4843359dde3a0e29500a821030e2433e316/dartagnan/src/test/java/com/dat3m/dartagnan/llvm/VMMLFDSTest.java#L43-L72)).

The chronology matters. The suffix-fairness constraint entered the project in
[PR 772](https://github.com/hernanponcedeleon/Dat3M/pull/772), merged on
2025-03-10. The public paper-artifact branch at commit
[`445539172ba3af3c2020409249053e3c5f356bc2`](https://github.com/hernanponcedeleon/Dat3M/tree/445539172ba3af3c2020409249053e3c5f356bc2),
dated 2025-11-28, contains the suffix rule but compiles LLVM compare-exchange
to a hard-coded strong exclusive store
([source lines 208–229](https://github.com/hernanponcedeleon/Dat3M/blob/445539172ba3af3c2020409249053e3c5f356bc2/dartagnan/src/main/java/com/dat3m/dartagnan/program/processing/compilation/VisitorC11.java#L208-L229)).
Proper weak-flag lowering was added only in
[PR 976](https://github.com/hernanponcedeleon/Dat3M/pull/976), merged on
2026-03-05, after the paper's January 2026 publication. The paper's statement
that its developed theory ignores platform fairness is therefore retained;
the current tool has a later implementation-level composition that narrows
any claim about first implementation.

The paper artifact at
[Zenodo 17770530](https://doi.org/10.5281/zenodo.17770530) is a
1,605,322,240-byte Docker-image tar plus small README and license files. Its
public README, metadata, and artifact-branch source were checked, but the image
was not downloaded, so the audit does not assert that the Docker image is
byte-for-byte represented by the public branch. The commit-pinned sources
establish the implementation findings above. They do not provide a weak-CAS
Treiber progress theorem or defeat the exact candidate conjunction.

## Known-artifact source audit

The eleven fixed archives A01--A11 in `artifact-sources.csv` were downloaded
and matched against their declared checksums: MD5 for A01--A10 and SHA-256 for
A11. A01--A08 and A10--A11 were safely extracted and searched at source level.
A09 contains one unsafe absolute symbolic link, so the generic extractor
rejected it; its 4,254 regular files were enumerated and searched directly
from the tar stream. The canonical successful retrieval records for A01--A07
are split across four immutable manifests:

- `data/artifacts/manifest-20260730T224632Z.csv` for A01--A03;
- `data/artifacts/manifest-20260730T233105Z.csv` for A04;
- `data/artifacts/manifest-20260731T002021Z.csv` for A05; and
- `data/artifacts/manifest-20260731T033506Z.csv` for A06--A07.

The A08 safe extraction and A09 policy rejection are recorded in
`data/artifacts/manifest-20260731T051403Z.csv`; A11's retrieval and safe
extraction are recorded in
`data/artifacts/manifest-20260731T090424Z.csv`. The current consolidated
no-extraction integrity revalidation is
`data/artifacts/manifest-20260731T091909Z.csv`, SHA-256
`8d8c700790081215f3784dc6db8a953218ddfeaa6b6a6221405d7811064d3613`;
it records all eleven archives with zero integrity failures. A01--A08 and
A10--A11 account for 23,999 safely extracted files. The A06
archive is 7,516,951 bytes with 20,427 files; the A07 archive is 785,699 bytes
with 156 files. Their SHA-256 values are, respectively,
`b13daecf7f4a83a93175a4634be0b45ef1fd5e583d33f798938b1ae972d0de06`
and
`e3c6379299ab1227479ed789822c450044ff15ac59b69b83761a680376297f08`.
Exact hashes, paths, declarations, line references, and negative scans for all
eleven artifacts are in `artifact-audit.md`.

The current `fetch_artifacts.py` accepts both ZIP and compressed-tar inputs,
validates each extraction target, and rejects symbolic links and special tar
members. Its SHA-256 at this audit revision is
`40f31ca2f4c91ca8b65ae73498620cdd6295e11d3f9864cc55051eb06da1fef8`;
the eleven-row `artifact-sources.csv` catalogue has SHA-256
`7b4236830d9df5db7dc27c26ad14ef4770c8702a6fa97db0662c581b5a484be2`.
From the audit directory, cached archives can be reverified and a new
timestamped manifest produced with:

```bash
python3 scripts/fetch_artifacts.py --no-extract
```

This command verifies archive integrity and source presence without following
A09's unsafe link; it is not a substitute for rebuilding the proof
developments with their pinned toolchains. The audit did not perform fresh
full Coq/Rocq/PVS/Agda builds of A01--A05, A07, A08, A10, or A11.
It did rerun A06's Treiber benchmark in an isolated Python 3.12 environment
with `pycparser==3.0` and `z3-solver==5.0.0.0`; the reproduced structural
counts were `3,4,2`, while wall-clock time differed from the reference run.

The source audit establishes:

- FOS already defines a fair, address-indexed weak CAS and excludes an
  infinite same-address all-spurious behavior through its fairness machinery,
  but does not use the primitive in Treiber;
- Lilo already machine-checks strong-CAS Treiber termination and carries the
  unused FOS weak-CAS definition in the same source tree, but does not connect
  them;
- Lawyer machine-checks strong-CAS liveness examples in an interleaving
  language, but has no Treiber or spurious weak-CAS definition;
- Spirea machine-checks durable Treiber thread/crash safety under weak
  persistent memory, but its CAS is exact-match and the verified specification
  explicitly omits linearizability/LIFO and all liveness guarantees;
- The Colvin–Dongol bundle has completed 2009 queue proof families, while its
  legacy `treiber.pvs` has no proof file and retains two explicitly unproved
  well-foundedness obligations. The separately published 2007 direct PVS
  Treiber result remains valid prior art and is not conflated with this
  incomplete file;
- RoboCop reproducibly checks RC20 robustness for a Treiber input whose push
  and pop operations both use strong compare-exchange. Robustness is a safety
  result: the artifact does not test operation termination, genuine
  compare-equal spurious failure, primitive justice, or an all-spurious
  execution; and
- the general-purpose RCU paper gives a Treiber-with-RCU iRC11 safety
  illustration, but its archived Rocq development contains no identified
  Treiber or stack proof file. The archive mechanizes RCU and selected
  queue/list clients, and its CAS failure rule is mismatch-only;
- CQS's pinned public branch contains 33 Coq files for synchronization
  components and exact-CAS safety proofs, but no exact liveness/fairness term
  and none of the blocking-pool or modified-outer-stack files referenced in
  the paper. The paper-level fair/Treiber construction is prior art, while
  mechanized progress is not established by this branch; and
- GenMC v0.6 already includes strong-CAS Treiber regressions in a
  C11/RC11-family model checker. Its public API exposes weak compare-exchange,
  but the audited execution visitor ignores the weak flag and succeeds on
  equality; the artifact proves no positive progress property.
- Burrow's cutoff-eligible public archive contains 20 Agda modules for
  axiomatic weak-memory executions, well-formedness, and mapping proofs. Its
  x86-to-Arm result is graph robustness; the pinned repository contains no
  identified Treiber, fairness, liveness, termination, or weak-CAS justice
  development; and
- Promising-ARM/RISC-V mechanizes an independently enabled store-exclusive
  failure step and machine-model certification results. Its finite Treiber
  example sources use strong compare-exchange, are separate from the Coq
  development, and provide no checked Treiber safety, primitive-justice, or
  response-progress theorem.

A separate commit-pinned Dartagnan implementation follow-up establishes that:

- Dartagnan implements a lasso-level constraint against infinite spurious
  exclusive-store failure, but its current Treiber benchmark is strong-CAS
  and has no positive C11/RC11 termination verdict.

These are stronger findings than repository-name or README searches because
they inspect the fixed artifact versions themselves.

## Proof-assistant archive checks

### Isabelle Archive of Formal Proofs

The stable AFP archive was downloaded from
`https://isa-afp.org/release/afp-current.tar.gz`.

- Archive version directory: `afp-2026-07-21`
- Tarball SHA-256:
  `544de82b35d1bb6aaa1923f11cdd50d702824a6e0601cd72ee7e43e5eca85d6f`
- Literal target searches over the extracted source:
  `Treiber`, `compare_exchange_weak`, `cas_weak`, `weak CAS`,
  `spurious failure`, `WeakCASJustice`, and `all-spurious`
- Relevant target hits: zero

The two literal `RC11` occurrences are an unrelated European Commission report
identifier in a bibliography. AFP does contain a generic strong
`compareAndSwap` operation in JinjaThreads (473 occurrences across 27 files),
but no Treiber or weak/spurious-CAS instance was found.

### Rocq package archive

The official `rocq-prover/opam` repository was shallow-cloned and searched at
commit:

```text
e871a8727041d9b28041842e4452cce69acb880b
```

Package metadata contained no occurrence of `Treiber`,
`compare_exchange_weak`, `WeakCASJustice`, `all-spurious`, `cas_weak`, `RC11`,
`weak CAS`, or `spurious failure`. This checks the official package catalogue,
not every source file of every package. The fixed FOS, Lilo, Lawyer, Trillium,
and Nola sources are handled separately in the primary-source and artifact
audits.

### Lean search surfaces

Four exact Loogle declaration-name searches returned zero Mathlib/Lean
declarations:

- `"Treiber"`;
- `"compare_exchange_weak"`;
- `"WeakCASJustice"`; and
- `"all-spurious"`.

LeanSearch returned 20 semantic results for each of `Treiber stack`,
`weak compare exchange spurious failure`, `WeakCASJustice`, and
`RC11 weak CAS fairness`; none of the returned declarations contained a target
token. These are semantic top-20 checks, not exhaustive negative searches.

The Reservoir package-metadata bundle served on 2026-07-31 had SHA-256
`6edb1858f3ee6da8e4eeaaaa07a559c33b5351d9843ca30e4f89be36b61c9f1e`.
It contained no occurrence of `Treiber`, `compare_exchange_weak`,
`WeakCASJustice`, `all-spurious`, `cas_weak`, or `RC11`. This checks package
metadata, not all package source revisions.

## Current conclusion

The public-index run, independent proof-archive checks, eleven-artifact source
audit, and targeted author/thesis follow-ups found no proof of the full target
conjunction. The strongest artifact-level wording threats now include FOS,
Lilo, the classical PVS/KIV Treiber lineage, Spirea, Mirror, Relinche,
RoboCop, RSan, general-purpose RCU, Promising-ARM/RISC-V, and current
Dartagnan:

- FOS defeats any claim to the first formal fair weak-CAS primitive;
- Lilo defeats any claim to the first machine-checked Treiber termination
  result;
- the 2007 PVS and 2011 KIV results defeat first mechanized Treiber
  lock-freedom and safety-plus-progress wording;
- Spirea and Relinche defeat broad first mechanized weak/persistent-memory or
  automated RC11 Treiber safety wording;
- Mirror defeats first mechanized discovery/modeling of genuinely weak durable
  CAS, although its end-to-end upper refinement is unfinished;
- RoboCop defeats broad wording about first automated relaxed-memory Treiber
  robustness, but its benchmark uses strong CAS and its result is safety, not
  progress;
- RSan defeats broad wording about the first weak-memory model or tool
  supporting genuine weak CAS, while its inspected published result is
  robustness rather than Treiber liveness; and
- the general-purpose RCU paper narrows broad iRC11 Treiber-with-reclamation
  safety wording, while its archived Rocq artifact supplies no identified
  Treiber proof;
- CQS narrows broad fair-synchronization and Treiber-derived-construction
  wording, while its pinned public Coq branch supplies no identified
  mechanized progress or outer-stack proof; and
- GenMC defeats broad wording about first weak-memory model checking of a
  Treiber benchmark, while the audited version uses exact CAS semantics and
  supplies no liveness theorem; and
- Burrow narrows broad machine-checked weak-memory-framework wording, while
  its Agda result concerns model mappings and graph robustness rather than
  concurrent-object progress; and
- Promising-ARM/RISC-V defeats broad wording about first combining a
  mechanized weak-memory model, independent exclusive-store failure, and
  Treiber test inputs, while its bounded strong-CAS examples and model
  metatheory do not establish Treiber safety or response progress.

Memento additionally defeats broad wording about the first formal persistent
Treiber or detectable helping-CAS framework. Current Dartagnan defeats wording
that the platform-fairness extension has never been implemented. *Will It
Fit?*, *Parcas*, *Zoo*, and the modular reclamation work further constrain
claims about combining Treiber with liveness-adjacent, cost, or mechanized
safety results. Miri–GenMC documents that a major RC11 exploration path still
omits genuine spurious weak-CAS behavior.

The candidate contribution must remain the exact six-part conjunction, not
any component in isolation. That conjunction survives this bounded audit, but
the result remains N0–N1 rather than a priority certificate.

## Coverage limits and next actions

- GitHub indexing, branch selection, forks, and legacy query semantics can
  omit source files; its JSON interface supplies no exhaustive total.
- Software Heritage exposes origin lookup but no suitable global
  content-search interface in this audit. It was not counted as a completed
  code-content search.
- Rocq and Reservoir checks cover package metadata, not the complete source of
  every package revision.
- Loogle and LeanSearch principally cover Lean/Mathlib declarations rather
  than arbitrary external repositories.
- Author pages and unpublished branches have not all been searched
  systematically.
- Human screening confirmation and external expert review are still pending.
- The eleven archives passed checksum and source-inventory checks, but
  A01--A05, A07, A08, A10, and A11 were not freshly rebuilt with their
  proof-assistant
  toolchains.
  A09 was audited from its tar stream because its one unsafe absolute symbolic
  link was rejected rather than extracted. The
  successful A06 rerun reproduced its robustness benchmark, not a
  proof-kernel certificate or liveness result.
- The large Memento and Shape Abstraction VM images were not source-scanned;
  their papers/public README and artifact metadata were screened instead.
- The 1.6 GB POPL 2026 Dartagnan artifact image was not downloaded; its public
  README and metadata were checked, and the related current public source was
  inspected at an immutable commit.
- The 12.3 GB RSan Docker image was metadata-audited but not downloaded or
  source-scanned. Paper-level evidence establishes the genuine-weak-CAS tool
  boundary, but the image remains an explicit source-level coverage gap.

The public artifact sweep narrows the remaining uncertainty but does not by
itself raise the audit beyond N0–N1. Because A11/PA118 was newly promoted as a
closest work, its forward/backward citation expansion and every resulting
candidate must be screened before counting a no-new-closest wave. The protocol
then requires two consecutive complete no-new-closest waves after the last
promotion. Keyed production coverage, human screening confirmation, and
independent expert review also remain required.
