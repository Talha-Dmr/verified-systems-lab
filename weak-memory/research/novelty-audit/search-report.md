# Novelty-Audit Search Report

Last updated: 2026-07-31

Publication cutoff used throughout this audit: 2026-07-31

Audit status: active; between N0 and N1

## Question being tested

The audit asks whether prior work already proves the full conjunction below:

1. an explicit finite-thread, reclamation-free Treiber stack under C11/RC11;
2. genuinely weak compare-and-exchange with unbounded equal-value spurious
   failure;
3. primitive weak-CAS justice kept distinct from scheduler and memory
   fairness;
4. an integrated all-spurious execution showing that scheduler and memory
   fairness alone do not imply progress;
5. unbounded system-wide response progress; and
6. machine-checked composition with finite-prefix linearizability.

The conjunction has survived the primary-source and limited citation screening
recorded here. This is a current negative search result, not a proof of
priority, and it does not justify an unqualified “first” claim.

## Evidence inventory

- `primary-sources.csv` identifies S01–S230. The catalogue currently has 179
  locally retained PDFs and text extractions across immutable manifests.
  Missing or access-restricted files remain explicit. The latest incremental
  manifest, `data/papers/manifest-20260731T095210Z.csv`, downloaded S228–S230
  and records the subscription-blocked S227 journal PDF as a failure; the
  accessible precursor and official metadata are used only with a partial
  full-text qualification. Historical manifests preserve failures, fallbacks,
  and earlier corpus states rather than being rewritten.
- `standards-history-sources.csv` identifies five primary WG21/LWG pages
  delimiting the weak-CAS progress lineage from N2427 through N3927.
  `data/standards/manifest-20260731T021452Z.csv` records exact local HTML and
  deterministic text copies with zero failures; its SHA-256 is
  `dc14ea4202e8d8dd8d0856c6cf45c32a836c290f34f2380d818425d5c9151a75`.
- `artifact-sources.csv` identifies eleven fixed archives, including FOS,
  Lilo, Lawyer, Spirea, the Colvin–Dongol PVS sources, RoboCop,
  General-Purpose RCU, CQS, GenMC, the RSan source snapshot, and
  Promising-ARM/RISC-V. `data/artifacts/manifest-20260731T091909Z.csv`
  revalidates all eleven with zero integrity failures; its SHA-256 is
  `8d8c700790081215f3784dc6db8a953218ddfeaa6b6a6221405d7811064d3613`.
  A09's unsafe absolute symlink was rejected by the generic extractor and its
  regular files were audited directly from the tar stream.
- `prior-art-matrix.csv` contains 122 theorem-level comparisons. Every row
  has `subsumes_candidate=no`; that is an audited judgment, not a proof of
  nonexistence.
- `closest-work-map.csv` maps all 110 current `include-closest` records to
  exactly one matrix row, and `citation-seeds.csv` contains the corresponding
  110 seeds.
- `screening.csv` contains 240 decisions: 110 `include-closest`, 84
  `include-adjacent`, 34 `include-context`, 11
  `include-version-audit`, and one `exclude-secondary`. All remain
  Codex-assisted decisions awaiting the human confirmation required by
  `protocol.md`.
- Ten checksum-bound decision overlays contain 4,267 Codex-assisted decisions
  across overlapping immutable queues. The 179-work closing queue is fully
  classified, with zero new `include-closest` records. Queue overlap is
  preserved rather than silently collapsed, so this total is a decision-row
  count rather than a distinct-work count. Every decision still awaits the
  human confirmation required by `protocol.md`.
- `data/artifact-runs/20260730T233156Z/` records the broad ten-Zenodo/ten-public-
  GitHub pass. `data/artifact-runs/20260731T035000Z-rsan-followup/` records the
  exact RSan metadata query. Its 12,331,288,562-byte Docker image was not
  downloaded, so no source-level absence claim is made about that payload.
- `artifact-search-report.md` records the public-index runs, Isabelle AFP,
  Rocq and Lean search surfaces, source-level artifact findings, exact hashes,
  and coverage limits.

The checksum-bound citation queues described below have record-level decision
overlays, including exhaustive overlays for the 1,167-work, 1,978-work, and
179-work unions. Broad open-index retrieval tables are not thereby equivalent
to screened citation queues. All retrieval counts below are records returned,
not counts of relevant papers.

## Open-index run ledger

### Version-1 pilot

Run directory: `data/runs/20260730T220459Z/`

- Script version: 1
- UTC interval: 2026-07-30 22:04:59–22:09:34
- Query catalogue: 15 queries, SHA-256
  `0bd6f634d1c806e154062ebe4b7916b1d27523b0a5024f61dbaacff331f50a19`
- Providers: DBLP, OpenAlex, Crossref, Semantic Scholar, and arXiv
- Requests: 75 total; 56 successful; 19 failed
- Records: 2,505 normalized; 2,031 deduplicated

| Provider | Requests | Successful | Failed | Returned records |
|---|---:|---:|---:|---:|
| arXiv | 15 | 15 | 0 | 0 |
| Crossref | 15 | 15 | 0 | 1,500 |
| DBLP | 15 | 4 | 11 | 0 |
| OpenAlex | 15 | 15 | 0 | 711 |
| Semantic Scholar | 15 | 7 | 8 | 294 |

This run is retained as a pilot only. The same high-dimensional natural query
text was sent through interfaces with incompatible query semantics. The arXiv
queries were over-conjunctive, Crossref’s fuzzy search produced a large noisy
set, DBLP repeatedly disconnected, and Semantic Scholar rate-limited eight
requests. Its `run.json`, `manifest.csv`, `records.csv`, and
`deduplicated.csv` are retained, but the run is not final coverage evidence.

### Interrupted version-2 OpenAlex discovery run

Run directory: `data/runs/20260730T223354Z/`

- UTC interval: 2026-07-30 22:33:54–22:40:15
- Provider: OpenAlex
- Publication cutoff: 2026-07-31
- Raw pages retained: 28
- Partial returned records: 2,216
- Terminal marker: `run-interrupted.json`
- Reusable as completed evidence: no

| Query | Raw pages | Partial returned records |
|---|---:|---:|
| OA01 | 1 | 81 |
| OA02 | 1 | 60 |
| OA03 | 1 | 8 |
| OA04 | 1 | 25 |
| OA05 | 2 | 126 |
| OA06A | 1 | 18 |
| OA06B | 19 | 1,889 |
| OA07 | 1 | 8 |
| OA08 | 1 | 1 |

The unauthenticated API began returning HTTP 429 with a long `Retry-After`
delay after OA01–OA07 and the first OA08 page. The run was deliberately stopped
without normalization or deduplication and must not be counted as a completed
OpenAlex search.

### Current terminal runs

| Run directory | Scope | Requests | Outcome | Records |
|---|---|---:|---|---:|
| `20260730T224855Z-core` | arXiv, exact-title Crossref, Semantic Scholar | 35 | 19 successful, 16 Semantic Scholar requests skipped, 0 failed | 333 normalized / 305 deduplicated |
| `20260730T224954Z-dblp` | DBLP D01–D22 | 22 | 16 successful, 6 disconnected | 36 / 36 |
| `20260730T225800Z-dblp-retry` | DBLP retry D17–D22 plus D23–D28 | 12 | 12 successful, 0 failed | 21 / 21 |
| `20260730T225200Z-oa-seed` | OpenAlex no-key probe | 1 | HTTP 429 | 0 / 0 |
| `20260730T225400Z-arxiv-refined` | refined arXiv A01–A09 | 9 | 9 successful, 0 failed | 36 / 32 |
| `20260730T234022Z` | new exact-title DBLP/Crossref seeds D29–D32 and C11–C14 | 8 | 8 successful, 0 failed | 87 / 85 |
| `20260730T235824Z` | classical Treiber progress seeds D33–D35 and C15–C17 | 6 | 6 successful, 0 failed | 63 / 61 |
| `20260731T001529Z` | Mirror, resource-liveness, RC11-tool, and Zoo seeds D36–D39 and C18–C21 | 8 | 8 successful, 0 failed | 83 / 80 |
| `20260731T002216Z` | Relinche, reclamation, and work/span seeds D40–D42 and C22–C24 | 6 | 6 successful, 0 failed | 62 / 60 |
| `20260731T004931Z` | seven final theorem/lineage seeds D43–D49 and C25–C31 | 14 | 14 successful, 0 failed; every Crossref row transparently truncated at its top-20 ceiling | 146 / 136 |
| `20260731T014904Z` | nine direct-triage and lineage seeds D50–D58 and C32–C40 | 18 | 18 successful, 0 failed; every Crossref row transparently truncated at its top-20 ceiling | 194 / 164 |
| `20260731T032100Z-seed-supplement` | S52–S56/A32 exact seeds OA59–OA64, S259–S264, D59–D64, C41–C46 | 24 | 12 DBLP/Crossref requests succeeded; 12 credential-dependent OpenAlex/Semantic Scholar requests explicitly skipped; 0 failed | 65 / 60 |
| `20260731T035200Z-rsan-seed` | RSan exact seed OA65, S265, D65, C47 | 4 | DBLP/Crossref succeeded; OpenAlex/Semantic Scholar explicitly skipped; 0 failed | 22 / 21 |

Interpretation:

- The arXiv portion of `20260730T224855Z-core` was superseded for discovery by
  `20260730T225400Z-arxiv-refined`, which restricts searches to title and
  abstract fields and avoids author-name collisions.
- The Crossref component is exact-title DOI reconciliation, limited to the top
  20 results per seed. It is not an exhaustive discovery search.
- The initial DBLP failures D17–D22 were recovered in the retry. D23–D28 are
  expanded DBLP queries. The two DBLP runs have not been deduplicated against
  one another or against other providers.
- The later eight-query seed run resolves Spirea, Memento, the C11-style
  refinement paper, and RGITL directly in DBLP; Crossref resolves the first
  three as the top result, while its fuzzy RGITL query does not return the
  expected paper within the retained top 20. The retained Crossref rows remain DOI
  reconciliation evidence, not exhaustive discovery.
- The intermediate `20260730T235824Z`, `20260731T001529Z`, and
  `20260731T002216Z` terminal runs preserve reproducible DBLP/Crossref seed
  results for ten added comparisons: the 2007/2009 PVS lineage, the 2011 KIV
  hazard-pointer stack, Mirror, Will It Fit?, the Miri–GenMC thesis, Zoo,
  Relinche, modular reclamation, and the finite-workload work/span result. A
  successful request does not mean that every expected title was resolved;
  these are seed checks, not substitutes for keyed discovery or citation
  snowballing.
- The final 18-request run resolves the Friggens thesis in DBLP, the FAC 2026
  TSO article in both indexes, the MASCOTS descriptor-progress paper, the
  open LL/SC position paper, the KIV temporal-lock-freedom work, the scalable
  stack lineage, and thread-modular counter abstraction. The Peterson and
  Serra dissertations remain negative exact-title results in these two
  indexes; their institutional full texts and metadata are retained directly.
- The two later seed supplements resolve the six citation-wave additions and
  RSan in DBLP/Crossref. Missing keys are represented by explicit skip rows,
  never zero-result claims.
- Semantic Scholar’s official bulk search was skipped because
  `SEMANTIC_SCHOLAR_API_KEY` was not set.
- The OpenAlex probe confirms that a keyed, backoff-aware production rerun is
  still required for dependable access.

Every terminal directory contains its query snapshot, request
manifest, normalized records, deduplicated records, and `run.json`, including
the query and script hashes. These run records identify repository commit
`764d8dc6b37c7a8d08dd10c70d6a33c4de272682`.

### Current reproduction behavior

The open-index runner is now script version 3, SHA-256
`678f96d668cd88b1ededafdaaf9fafd545fa1171c960aba9916e4dda3ae05fb7`.
The current `provider-queries.csv` contains 472 provider rows: 121 OpenAlex,
120 DBLP, 120 Semantic Scholar, 102 Crossref, and nine arXiv. Its SHA-256 is
`2755f87305b71c4b7e655f9c5371d939c85579dde1789156fe192e21348551b2`.
The expansion adds exact-title seeds for every mandatory comparison in the
external review packet, including Spirea, Memento, the C11-style Isabelle
work, RGITL, the classical PVS/KIV progress lineage, Mirror, Will It Fit?, Zoo,
Relinche, modular reclamation, the work/span result, iRC11 traversals, the
2007/2008 stack-safety lineage, Coachman, bounded lock-freedom, and the
weak-CAS reclamation thesis.
The subsequent expansions additionally seed Friggens's thesis, the substantive
FAC TSO version, the descriptor-helping paper and dissertation, the LL/SC
proof-system lineage, the KIV temporal-liveness method, the scalable stack,
thread-modular counter abstraction, six citation-wave closest additions, and
RSan, CQS, GenMC, Gao and Hesselink's 2004 proof, and Jacobs et al.'s 2018
termination proof. The final catalogue has 110 closest-work seeds, SHA-256
`c0701685e5662af2059b93d77d0b415aa2e6972f5347cd81255fe7e7a834c545`.
Version 3 records OpenAlex as skipped unless `OPENALEX_API_KEY` is set and
Semantic Scholar as skipped unless `SEMANTIC_SCHOLAR_API_KEY` is set. A smoke
run passed outside the tracked `data/runs/` tree; it verifies runner operation
but is not search evidence. The earlier run snapshots, script versions, and
hashes remain immutable historical evidence and are not retroactively
reinterpreted as version-3 runs.

## Reproducible two-index citation-graph runs

### Historical 29-seed run

Run directory: `data/citation-runs/20260731T010300Z/`

- Seeds: the 29 `include-closest` records present at run start; the later
  31-seed snapshot added S44 Friggens and S45 Wang et al.; subsequent
  historical snapshots reached 38 and 42 seeds, while the current catalogue
  has 110;
- providers: Semantic Scholar Academic Graph and the unified OpenCitations
  Index v1 API;
- operations: 203 were planned, 192 issued provider requests (263 actual HTTP
  attempts after retries), 157 issued operations succeeded, 35 failed, and 11
  planned operations were explicitly skipped for two seeds without the
  required provider identifier;
- normalized occurrences: 3,040 works and 2,057 directed edges;
- deduplicated view: 956 works and 1,456 directed edges;
- forward edges with an unresolved cutoff date: 26; and
- run status: `incomplete-with-errors`, with request and coverage status both
  `incomplete`.

The run used citation catalogue SHA-256
`a0aeec1a2cce5afafb35825fb130c1b825af0bf6757e921bebb84e6816d947e7`
and script snapshot SHA-256
`b21bffebf9219f6bd36d767e7d8101aa50ddab03dcc151859df20e920fe1499d`.
It archives the exact seed, screening, and script bytes used. Its
`checksums.csv` covers those snapshots, all 192 compressed terminal responses,
the request manifest, normalized and deduplicated tables, and run metadata;
the checksum-manifest SHA-256 is
`08848da056d3cbd4ac7df59b3ec5302c01d62ffe98c6186059eb6769cb515422`.
The later 31-seed catalogue SHA-256 was
`a2e0f1cabbcd3244bbcf88fdeda6903b859c892c28a615b084888d82af574b21`.
The later historical 42-seed catalogue SHA-256 was
`654ade4d34d385a2b298ead39c8592fe958073f056f45a39c2447aadf6843e16`.
The current 110-seed catalogue SHA-256 is
`c0701685e5662af2059b93d77d0b415aa2e6972f5347cd81255fe7e7a834c545`.
The current citation runner is version 6, SHA-256
`30f7790e0bc8a96923d69d43044d6c4060efa832fa7f0e551c99201b198d91bc`;
none of these later inputs or script versions is retroactively attributed to
the version-2 run snapshot.

OpenCitations completed all 108 requested count and relation operations with
HTTP 200 for the 27 DOI-addressable seeds. The independent
`reference-count`/`citation-count` results matched the returned relation-array
sizes. Thirteen relation operations remain coverage-limited because one or
more unified-index rows lacked a usable DOI or because the DOI was only a
version alias for the cutoff-eligible arXiv seed.

Semantic Scholar was attempted without an API key: 60 requests returned HTTP
200, 19 returned HTTP 429, and five returned HTTP 404. Eleven of the HTTP-200
reference responses validly contained `data: null` with a publisher-elision
notice; the immutable version-2 run conservatively classifies them as failed.
The current runner classifies that same shape as
`success-with-limitations`, without treating it as an empty reference list.
Two seed families also require manual DOI/arXiv version reconciliation.
Fourteen seeds nevertheless completed both directions in both indexes;
OpenCitations completed both directions for all 27 DOI-addressable seeds.

This is a reproducible two-index, one-hop retrieval pass, not a complete
snowballing wave. Rate limits, publisher-elided references, identifier skips,
DOI-less OpenCitations edges, unresolved forward dates, and unscreened
candidates prevent the stopping rule from advancing.

The lossless follow-up queue is
`data/citation-screening-runs/20260731T011000Z/`. Its generator verified all
202 files named by the source checksum manifest and retained all 956
deduplicated works: 29 existing seeds, 48 priority title screens, 607 ordinary
title screens, 248 manual date checks, and 24 missing-title checks. The queue's
checksum-manifest SHA-256 is
`1bcc1f2b050379054f414573495bdaef189462daf77b9491ffcbba7c63c65acc`.
These are workload states, not inclusion/exclusion decisions.

### Supplement for the two newly retained seeds

The then-current 31-seed catalogue added CS030, Friggens's bounded Treiber
progress thesis, and CS031, the final FAC TSO liveness article, after the
historical run. The create-only supplement
`data/citation-runs/20260731T020306Z/` used that 31-seed catalogue snapshot and
version-3 runner:

- seeds: CS030 and CS031;
- providers: Semantic Scholar and the unified OpenCitations Index v1 API;
- operations: 14 issued requests and 17 actual HTTP attempts, with 13
  successful operations and one failed operation;
- failure: CS031 Semantic Scholar metadata returned HTTP 429, while both
  citation directions for that seed and all CS030 operations completed;
- normalized occurrences: 328 works and 296 directed edges;
- deduplicated view: 269 works and 271 directed edges; all 271 edges are
  cutoff-eligible, with no unresolved forward-edge dates; and
- run status: `incomplete-with-errors`, with request and coverage status both
  `incomplete`.

Its checksum-manifest SHA-256 is
`ed1a9420e1b65f319025b5c554ad70733c3af0e23e9c87704e67b17908ef9768`.
The separate create-only version-3 repair run
`data/citation-runs/20260731T020357Z/` repeated CS031's three Semantic Scholar
operations. All three succeeded, producing 43 deduplicated works and 42
directed edges; every repair result was already present in the larger
supplement. Under the version-3 identity check, that run recorded complete
request and coverage status for its one-seed, one-provider scope. Its
checksum-manifest SHA-256 is
`882307506375f4416e06e3ebe58f2c8e06f3ab73695e1583a4c611a423ea53fb`.

Cross-file QA then found that Semantic Scholar's DOI-addressed CS031 record
carried the 2021 arXiv year, date, and identifier rather than cleanly
representing only the 2026 final article. Version 4 therefore treats a
matching DOI with conflicting year/date or an unrecorded arXiv alias as a
coverage limitation. The create-only v4 audit
`data/citation-runs/20260731T021519Z/` completed all three CS031 Semantic
Scholar operations, reproduced the same 43 works and 42 edges, and explicitly
records CS031 in
`version_alias_seed_ids_requiring_manual_reconciliation`. Its request status
is complete, its coverage status is incomplete, and its checksum-manifest
SHA-256 is
`98c95abc0e18d8cc64729113fee5ba3633fdd3e902140139948031df43ffd281`.

Taken together, the supplement and repairs provide successful endpoint
retrieval for both newly retained seeds in both requested indexes. They do
not settle the CS031 version lineage, retroactively repair any historical
29-seed failure, or form a protocol-complete 31-seed wave.

The supplement's lossless screening queue is
`data/citation-screening-runs/20260731T020418Z/`. Its generator verified all
24 files named by the source checksum manifest and retained all 269 works:
two existing seeds, 15 priority title screens, 243 ordinary title screens,
and nine manual date checks. Because neither repair added a unique work or
edge, the same queue covers their results. It is subsumed by the later
compatible-union screening described below; all decisions remain pending
human confirmation. Its checksum-manifest SHA-256 is
`cf3703c5c8f8334c2f2c842d80e311b6264e4e5dd40c77777af898f112bed4d6`.

### 31-seed OpenCitations snapshot

Run directory: `data/citation-runs/20260731T022106Z/`

This create-only version-4 run gives one coherent 31-seed snapshot
for the OpenCitations side of the planned two-index audit:

- seeds: all 31 `include-closest` records in that snapshot;
- addressability: 29 seeds had a DOI; CS012 and CS020 did not;
- operations: 116 issued provider requests, all successful, plus eight
  explicitly skipped count/relation operations for the two DOI-less seeds;
- manifest dispositions: 103 `success`, 13
  `success-with-limitations`, eight `skipped`, and zero failures;
- normalized occurrences: 1,981 works and 975 directed edges;
- deduplicated view: 641 works and 941 directed edges;
- cutoff state: 936 edges included and five forward edges with unresolved
  dates;
- version reconciliation: CS005 and CS023 remain explicit version aliases;
  and
- run status: `complete-with-coverage-limitations`; request status is
  `complete`, while coverage status is `incomplete`.

The 13 limited relation operations either returned rows without a usable DOI
pair or addressed a publication DOI that is only a version alias for the
cutoff-eligible seed. Count endpoints and returned DOI-addressable relation
arrays otherwise completed without a failed request. The checksum-manifest
SHA-256 is
`8a20379c30a72038fc3a5749226f6808bdbbe38b7012db05840e2f1120869fdf`.

The lossless queue
`data/citation-screening-runs/20260731T022253Z/` verified all 126 files named
by the source checksum manifest and retained all 641 works: 31 existing
seeds, 460 manual date checks, and 150 missing-title checks. OpenCitations
relation records frequently expose DOI/date information without titles, so
metadata completion is part of screening rather than an implicit exclusion.
This provider-specific queue is subsumed by the later compatible union; its
checksum-manifest SHA-256 is
`e9e6dfa917045d0b7e4aa7b8d4a91114e7dac1230ef820d4806ce41a7975f2ff`.

This pass materially improved the recorded OpenCitations coverage, but it is
not a
complete snowballing wave: the two DOI-less seeds require the second index,
five citing dates remain unresolved, version aliases remain, and no candidate
in the queue has yet received a human-confirmed decision.

### 31-seed Semantic Scholar snapshot

Run directory: `data/citation-runs/20260731T022348Z/`

This create-only version-4 run gives the matching 31-seed Semantic
Scholar snapshot:

- seeds: all 31 `include-closest` records in that snapshot;
- addressability: 30 seeds had a Semantic Scholar identifier; CS020 had none;
- operations: 90 issued provider requests and three explicit skips, with 187
  actual HTTP attempts;
- terminal HTTP results: 70 HTTP 200, 14 HTTP 429, and six HTTP 404;
- manifest dispositions: 57 `success`, 13
  `success-with-limitations`, 20 `failed`, and three `skipped`;
- normalized occurrences: 1,423 works and 1,378 directed edges;
- deduplicated view: 979 works and 1,355 directed edges;
- cutoff state: 1,330 edges included and 25 forward edges with unresolved
  dates;
- version reconciliation: CS005, CS008, CS023, and CS031 remain explicit
  version aliases; and
- run status: `incomplete-with-errors`, with request and coverage status both
  `incomplete`.

Sixteen metadata operations, two reference operations, and two citation
operations failed after bounded retries. Successful relation calls still
contribute their complete preserved payloads; failed siblings are not treated
as empty graphs. The checksum-manifest SHA-256 is
`5e726b371b3b781b17a186efdd1f50f6942d330f31ec8e71cdec7ee7e8af209b`.

The provider-specific lossless queue
`data/citation-screening-runs/20260731T023657Z/` verified all 100 files named
by the source checksum manifest and retained all 979 works: 31 existing
seeds, 75 manual date checks, 57 priority title screens, and 816 ordinary
title screens. It is subsumed by the later compatible union; its
checksum-manifest SHA-256 is
`bad83f387030e2d1e0529847e1cd1c2204f5a5daff327aab9f82c2cdff224abc`.

### Compatible 31-seed two-provider union

The primary 31-seed screening workload is
`data/citation-screening-runs/20260731T024138Z/`. Version 3 of the queue
generator verified all 226 checksum entries across the paired 31-seed
OpenCitations and Semantic Scholar runs and established that both use:

- publication cutoff `2026-07-31`;
- the identical 31-seed set and citation-seed SHA-256
  `a2e0f1cabbcd3244bbcf88fdeda6903b859c892c28a615b084888d82af574b21`;
  and
- the identical screening snapshot SHA-256
  `0ef3795bcc9bbc5db2dd18c65aaf257fc6d25cd55bb14545ede8c760478fe28c`.

The lossless union deduplicated 1,620 source work rows and 2,296 source edge
rows into 1,167 unique works and 1,722 unique directed edges. The queue
retained every work: 31 are existing seeds, 239 need a manual date check, 24
lack a title, 57 are priority title screens, and 816 are ordinary title
screens. Provider, seed, edge, and source-run provenance are unioned rather
than discarded. The generator script SHA-256 is
`973a783f45238d8833789c92196e877d35c67ccdbeea54acf70374726c9cc3a5`;
the queue checksum-manifest SHA-256 is
`c162b61f8d04f4b6ca08449fedd60802a400ce10d616846281c588c87154a227`.

This is a coherent 31-seed two-provider candidate union, not a complete
snowballing wave. The OpenCitations run has coverage limitations, the
Semantic Scholar run has failed operations, 25 Semantic Scholar and five
OpenCitations forward-edge dates remain unresolved, and six seed-version-alias
occurrences cover four distinct seeds across the two provider snapshots.
All 57 priority-title rows have checksum-bound Codex-assisted decisions in
`citation-screening-decisions.csv`: 53 `linked-existing`, two
`exclude-duplicate`, and two `exclude-topic`. A later exhaustive overlay
described below covers all 1,167 rows. Every decision still awaits human
confirmation.

An earlier version-2 cumulative diagnostic,
`data/citation-screening-runs/20260731T024024Z/`, combined all six historical,
supplemental, repair, and current runs. It happened to produce the same 1,167
unique works and 1,722 edges, but mixed a 29-seed historical snapshot with
31-seed snapshots. It is retained as a checksum-recorded cumulative
diagnostic, not interpreted as one protocol wave, and is superseded as the
primary workload by the compatible 31-seed pair above. Its
checksum-manifest SHA-256 is
`75387fa0657a1b1cceb4b6be5035f9f1d8551ad97c21be882802d12412e81352`.

### CS032–CS037 citation supplement

CS032–CS037 were selected from the then-current 37-seed catalogue snapshot
`d3db305b77dbd511cbb34cafbb2d94041b793ccac1f5da843f97a38a1ccb6223`.
The paired create-only runs used the same six-seed set, screening snapshot,
publication cutoff, and version-4 runner:

- `data/citation-runs/20260731T032300Z-new-seeds-opencitations/` completed all
  24 count and relation operations. It produced 201 deduplicated works and
  205 directed edges. One forward date and two DOI-less relation rows keep
  coverage incomplete, so the terminal status is
  `complete-with-coverage-limitations`. Its checksum-manifest SHA-256 is
  `c169f0d44b36b859305a4940419b12a2712e72aef584f019e4033febd0965d16`.
- `data/citation-runs/20260731T032400Z-new-seeds-semanticscholar/` completed
  16 of 18 operations and produced 197 deduplicated works and 199 directed
  edges. The CS032 and CS034 metadata calls ended in HTTP 429 after bounded
  retries, and four forward dates remain unresolved. Its terminal status is
  `incomplete-with-errors`; its checksum-manifest SHA-256 is
  `9161131cd004947dc7669455faf9993b38c228f3cb9f3a2be2ce5a8264029419`.

The compatible union
`data/citation-screening-runs/20260731T033000Z-new-seeds/` contains 268 unique
works and 275 unique directed edges: six existing seeds, 71 manual date
checks, 11 missing-title checks, 22 priority title screens, and 158 ordinary
title screens. Its checksum-manifest SHA-256 is
`113f9916181baf7e5e66d702df03e7ce65e51cd029385465b921a6262e4db4bc`.
The historical first pass over the priority rows recorded 18
`linked-existing`, three `exclude-topic`, and one `pending-full-text`
decision. The completed checksum-bound overlay
`citation-screening-decisions-20260731T033000Z.csv` now records 19
`linked-existing` and three `exclude-topic` decisions; all 22 remain
human-pending. Full-text follow-up promoted S57–S61, including RSan as
S59/PA47. None subsumes the six-part conjunction.

### CS038 RSan follow-up

RSan was then frozen as CS038 in the then-current 38-seed snapshot
`e408cf3770ae7827c788979e7e24c3e40c93da2d18b4bea6b44dfa38f8835027`.
The exact DBLP/Crossref seed run is recorded at
`data/runs/20260731T035200Z-rsan-seed/`; both credential-independent requests
succeeded, while OpenAlex and Semantic Scholar discovery requests were
explicitly skipped because their keys were absent.

The two citation runs used the same CS038 identity and cutoff:

- `data/citation-runs/20260731T035300Z-rsan-opencitations/` completed all four
  operations and produced 58 works and 57 edges. The paper/arXiv identity
  remains a version-alias limitation. Its checksum-manifest SHA-256 is
  `bb212de48d6672e6eba6bedab316481b5d9455eeecf405afd8bf0a600811b1fb`.
- `data/citation-runs/20260731T035400Z-rsan-semanticscholar/` completed both
  citation directions but its metadata call ended in HTTP 429. It produced
  72 works and 71 edges and retains the same version-alias limitation. Its
  checksum-manifest SHA-256 is
  `8c854117286f090b77cf44e2ae272c28c312d5491301e23709e5864f8caa9320`.

Their compatible union
`data/citation-screening-runs/20260731T035500Z-rsan/` contains 78 works and
77 edges: one existing seed, 11 manual date checks, four priority title
screens, and 62 ordinary title screens. Its checksum-manifest SHA-256 is
`603b0548ed4343ac90661845b688b6caf9c11b98da8afd03dcd4d9765b589c28`.
All four priority rows are linked to existing ledger records in
`citation-screening-decisions-20260731T035500Z.csv` and remain
human-pending. This follow-up promoted S62 and S63 as context/adjacent work
but found no theorem-level defeat.

### CS039–CS042 pending-full-text resolution supplement

Full-text resolution promoted S64–S85 and froze four new closest seeds:
CS039 CQS, CS040 GenMC, CS041 Gao and Hesselink's 2004 Treiber proof, and
CS042 Jacobs et al.'s 2018 termination proof. The corrected exact-title
provider run at
`data/runs/20260731T052100Z-pending-closest-seeds-corrected/` issued 16
catalogued requests: all four DBLP queries found the exact title and each
Crossref query returned the exact work first; eight keyed OpenAlex/Semantic
Scholar requests were explicitly skipped, with no failed issued request.

The paired citation runs used the same four-seed snapshot and cutoff:

- `data/citation-runs/20260731T052200Z-pending-closest-opencitations/`
  completed all 16 operations, retaining 151 works and 147 edges. Its
  checksum-manifest SHA-256 is
  `c4de6ab63d259089ca666c478ecb4b28b844b15e0e2a95c4e2d3c659958d5d52`.
- `data/citation-runs/20260731T052300Z-pending-closest-semanticscholar/`
  retained 190 works and 186 edges. CS039 and CS040 metadata calls ended in
  HTTP 429, while CS041 and CS042 reference responses were
  publisher-elided. Its checksum-manifest SHA-256 is
  `b21c650dde7075e48ad6083304eb8c7154aee0f616b0cde90a3652b20a6919ed`.

Their lossless union at
`data/citation-screening-runs/20260731T052500Z-pending-closest-union/`
contains 237 unique works and 233 unique directed edges: four existing seeds,
50 manual-date checks, 11 missing-title checks, 12 priority title screens,
and 160 ordinary title screens. Its checksum-manifest SHA-256 is
`bddb8c1df7380092cba1a9df363d60ce34e9f294e74d90c6abb9d073d8b90b1d`.
Its completed overlay records 102 `linked-existing`, four `include-adjacent`,
one `include-context`, 20 `exclude-duplicate`, six `exclude-secondary`, and
104 `exclude-topic` decisions. It retained no new closest work.

These supplements and their later exhaustive overlays close the
machine-assisted screening workload, but they are not protocol-complete
waves. Provider failures and coverage limitations remain, and every decision
awaits human confirmation.

### Exhaustive legacy screening and closing expansion

The compatible 31-seed union at
`data/citation-screening-runs/20260731T024138Z/` was subsequently screened in
full. Its 1,167-row checksum-bound overlay records 192 `linked-existing`, 30
`include-closest`, 187 `include-adjacent`, 89 `include-context`, 97
`exclude-duplicate`, 91 `exclude-secondary`, and 481 `exclude-topic`
decisions. Thus, the earlier priority-only disposition is historical rather
than an open workload.

A later 313-work citation union at
`data/citation-screening-runs/20260731T073200Z-closest-wave2-union/` was also
screened exhaustively. Its overlay records 47 `linked-existing`, eight
`include-closest`, 60 `include-adjacent`, 45 `include-context`, 42
`exclude-duplicate`, 23 `exclude-secondary`, and 88 `exclude-topic`
decisions. The eight closest promotions were added to the canonical ledgers
and seeded for the next expansion.

The resulting legacy-promotion expansion used both citation providers:

- `data/citation-runs/20260731T091600Z-legacy-promotions-opencitations/`
  retained 754 works and 1,242 directed edges;
- `data/citation-runs/20260731T091700Z-legacy-promotions-semanticscholar/`
  retained 1,719 works and 2,416 directed edges, but 21 requests ended in HTTP
  429 and four in HTTP 404; and
- `data/citation-runs/20260731T092500Z-legacy-promotions-semanticscholar-recovery/`
  retained 1,444 works and 1,776 directed edges from the retryable portion.
  Adding that recovery provenance did not add a candidate to the compatible
  union:
  `data/citation-screening-runs/20260731T094000Z-legacy-promotions-recovered-union/`
  remained exactly 1,978 works.

The exhaustive overlay for
`data/citation-screening-runs/20260731T092100Z-legacy-promotions-union/`
records 157 `linked-existing`, four `include-closest`, 413
`include-adjacent`, 157 `include-context`, 102 `exclude-duplicate`, 197
`exclude-secondary`, and 948 `exclude-topic` decisions. The four closest
promotions are PA119, *Trace-based derivation of a scalable lock-free stack
algorithm*; PA120, *Temporally Bounding TSO for Fence-Free Asymmetric
Synchronization*; PA121, *Progress of Concurrent Objects*; and PA122,
*Progress of Concurrent Objects with Partial Methods*. Their theorem-level
audits respectively delimit an SC exact-CAS stack derivation with a fair
internal-choice premise, a hardware store-drain-time bound, a tutorial
synthesis of exact-CAS progress reasoning, and a direct partial-pop Treiber
partial-deadlock-freedom (PDF) result under scheduler fairness. None supplies
genuine weak CAS under RC11, separate primitive justice, the integrated
all-spurious separation, or the candidate's mechanized composition.
S227/PA119 remains explicitly `partial` for full-text coverage because the
exact journal PDF is
subscription-restricted and the detailed audit relies on its open precursor
plus official metadata.

The four promotions were reconciled in exact-title index runs before their
closing citation pass. `data/runs/20260731T095000Z-new-closest-exact-indexes/`
issued 12 catalogued queries: six DBLP/Crossref requests succeeded and six
keyed OpenAlex/Semantic Scholar requests were explicitly skipped, yielding
38 normalized and 32 deduplicated records.
`data/runs/20260731T100000Z-partial-progress-exact-indexes/` added four more
catalogued queries: two DBLP/Crossref successes and two keyed-provider skips,
yielding 11 normalized and ten deduplicated records.

The final four-seed citation runs were
`data/citation-runs/20260731T100500Z-final-four-opencitations/`, with 124 works
and 131 edges, and
`data/citation-runs/20260731T100600Z-final-four-semanticscholar/`, with 116
works and 114 edges. Their compatible lossless union at
`data/citation-screening-runs/20260731T101000Z-final-four-union/` contains 179
works and 189 merged edges; its checksum-manifest SHA-256 is
`c975d98aca38b4cfb845a8b66574c41ad8edc82f1cf2f7d0d9b2aedc80d18c9b`.
Its exhaustive overlay,
`citation-screening-decisions-20260731T101000Z.csv`, records 41
`linked-existing`, 46 `include-adjacent`, 17 `include-context`, 12
`exclude-duplicate`, 21 `exclude-secondary`, and 42 `exclude-topic`
decisions, with zero new `include-closest` records. The overlay SHA-256 is
`410fa05c4ba828d9731588d54849b0fcbfb18be41d515919a8a487d66b852086`.

Across all ten checksum-bound overlays there are therefore 4,267 decision
rows. The queues overlap by design and their provenance is preserved, so
4,267 must not be read as a distinct-work count. This completes the recorded
Codex-assisted citation screening workload and leaves the canonical catalogue
at 230 sources with 179 locally retained PDFs, 240 screening decisions, 110
closest works, 122 theorem-level matrix rows, eleven pinned artifact archives,
and 472 provider queries. It does not complete a protocol wave: every decision
remains human-pending, and the provider limitations above prevent the stopping
counter from advancing.

The run directories are create-only and checksum-rooted locally, but the
audit tree is not yet committed or published. The checksum root therefore
detects local mutation but is not an independent external timestamp or
priority anchor. Because raw responses and downloaded corpora are excluded
from ordinary Git tracking, committing the manifests alone would still not
make the historical payloads clone-reproducible; publication requires a
checksum-addressed raw archive or selectively tracked payloads.

## One-hop OpenAlex citation-neighborhood audit

This was a separate diagnostic pass on 2026-07-30, not a tracked production
run. Initial requests ran from 22:23:44Z to 22:24:04Z; singleton fallbacks ran
from 22:28:33Z to 22:28:43Z. Forward citations were restricted to publications
on or before 2026-07-31.

| Seed | OpenAlex ID | Backward edges | Related IDs | Forward citations |
|---|---|---:|---:|---:|
| Making Weak Memory Models Fair | W3110596251 | 48 | 20 | 2 |
| Fair Operational Semantics | W4379512370 | 27 | 10 | 10 |
| Recurrence Sets for Proving Fair Non-termination | W7119470772 | 36 | 0 | 2 |
| Overcoming Memory Weakness with Unified Fairness | W4384471299 | 45 | 10 | 9 |
| Towards Proving Liveness on Weak Memory | W7161495752 | 33 | 0 | 0 |
| Compass | W4281945852 | 69 | 10 | 19 |
| A Proof Recipe for Linearizability | W4399872385 | 46 | 10 | 4 |
| Lilo | W4409311357 | 33 | 10 | 3 |
| **Raw totals** | — | **337** | **70** | **49** |

The raw neighborhoods contained 337 backward edges (253 unique IDs), 70
related-work edges (68 unique IDs), and 49 forward-citation edges (41 unique
IDs): 456 edges in total. Twenty-four initial API requests returned HTTP 200
and yielded 331 unique retrievable work records. Exact singleton fallback was
then attempted for 20 missed IDs: five returned HTTP 200 and 15 returned 404.
The fallbacks recovered five live records that the batched exact-ID filter had
missed, producing 336 unique retrievable records. Fifteen unique edge targets
remain unresolved overall: 13 backward-reference IDs and three related-work
IDs, with one ID appearing in both groups.

Reproduction pattern, with an OpenAlex API key and normal retry handling:

```text
GET /works/https://doi.org/{DOI}?select=...
GET /works?filter=cites:{OPENALEX_ID},to_publication_date:2026-07-31&per-page=200&cursor=*
GET /works?filter=openalex_id:{WID1}|{WID2}|...
```

Batch results must be checked against requested IDs and missing IDs retried as
singletons.

### Citation-audit limitations

- The diagnostic output and request manifest were not persisted in the
  repository. The counts are audit notes, not reproducible production
  evidence.
- This diagnostic itself used only OpenAlex. It is superseded for
  reproducible evidence by the persisted Semantic Scholar/OpenCitations runs
  and compatible unions above, which remain coverage-incomplete.
- This was one hop, not two complete snowballing waves. No
  protocol-complete wave has yet been achieved.
- OpenAlex’s forward set was visibly incomplete for some seeds; for example,
  only two citing records were returned for the Lahav seed.
- “Related works” is heuristic and was empty for the Haas and Bargmann seeds.
- Five live records were missed by an exact-ID batch filter, 15 IDs remained
  unresolved after singleton lookup, and version/self-citation edges around
  the Abdulla work require manual deduplication.
- Abstracts and reference metadata were incomplete for some records.
- A one-index search cannot recover unindexed papers, theses, unpublished
  artifacts, or repositories without bibliographic links.
- The unauthenticated requests succeeded during this diagnostic pass, but
  dependable current use of the official API requires a free API key.

## Screening disposition

`screening.csv` uses the following decision vocabulary:

- `include-closest`: theorem-level prior art that directly narrows one or more
  central dimensions;
- `include-version-audit`: a materially changed version retained separately;
- `include-context`: normative or language-level semantic context;
- `include-adjacent`: relevant liveness, weak-memory, or mechanization work
  that does not closely match the conjunction; and
- `exclude-secondary`: a tutorial or secondary treatment that adds no
  independent theorem beyond retained primary work.

Current screening disposition:

| Decision | Count |
|---|---:|
| include-closest | 110 |
| include-version-audit | 11 |
| include-context | 34 |
| include-adjacent | 84 |
| exclude-secondary | 1 |
| **Total** | **240** |

The highest-severity wording threats are FOS, Lilo, Haas et al., CQS, GenMC,
RSan, and the classical strong-CAS Treiber progress literature:

- FOS already provides a formal address-indexed fair weak-CAS primitive that
  excludes an infinite same-address all-spurious behavior.
- Lilo already provides a mechanized strong-CAS Treiber termination result,
  and its artifact separately contains the unused FOS-style fair weak CAS.
- Haas et al. explicitly identify spurious weak CAS and LL/SC as an additional
  platform-fairness dimension, although they omit it from the developed
  paper theory. A follow-up source audit found an implementation-level
  Dartagnan suffix constraint excluding infinite spurious
  `RMWStoreExclusive` failure. Current Dartagnan also preserves LLVM's weak
  compare-exchange flag, but its bundled Treiber benchmark uses strong CAS
  and receives `UNKNOWN`, not a positive C11/RC11 termination result.
- RSan explicitly models genuine strong and weak compare-and-exchange under
  RC20 and dynamically checks robustness. Its bounded-CAS abstraction erases
  failed events, however, and the paper proves neither a Treiber theorem nor
  liveness, separated fairness/justice, an all-spurious witness, or
  proof-assistant composition. It defeats a broad “first weak-memory tool
  supporting genuine weak CAS” claim, but not the exact six-part claim.
- CQS mechanizes a fair synchronization framework and uses a Treiber-derived
  stack in its outer storage design. The pinned public proof branch does not
  contain the paper's blocking-pool/outer-stack proof files or a mechanized
  progress theorem, so it narrows fair-synchronizer wording without
  subsuming the candidate.
- GenMC is prior weak-memory model-checking infrastructure with an executable
  Treiber benchmark. Its v0.6 Treiber input uses strong compare-exchange, and
  the audited engine treats compare-exchange success by value equality rather
  than exploiting the source-level weak flag. It defeats broad tool/benchmark
  wording, not the target liveness theorem.
- Gao and Hesselink's 2004 proof already separates scheduler fairness from an
  additional success/reservation premise for a Treiber-style stack.
  Jacobs et al. already give a 2018 formal/tool-checked exact-CAS termination
  proof for Treiber retry loops. These works defeat broad “first extra
  primitive-success premise” and “first formal Treiber CAS-loop termination”
  claims, while neither supplies genuine weak CAS under RC11 or the integrated
  all-spurious separation.
- Gotsman et al., Hoffmann–Marmar–Shao, Jia–Li–Vafeiadis, Total-TaDA, Lilo,
  and Tofan et al. already establish substantial strong-CAS Treiber
  lock-freedom or termination results. Tofan et al. additionally mechanize
  both linearizability and lock-freedom in KIV for Treiber-derived data and
  allocator stacks with explicit reuse.
- Memento formally establishes detectability/erasure refinement for typed
  persistent programs and implements a persistent Treiber stack using an
  exact-match helping CAS on Intel x86; it has no target weak-CAS or
  response-progress theorem.
- Spirea Coq-mechanizes a durable Treiber safety case under weak persistent
  memory. Its CAS failure rule requires inequality, and its paper explicitly
  says the verified specification does not imply linearizability or LIFO; no
  liveness or fairness-separated progress theorem was found. An unreviewed
  2026 `high-nextgen-logic` branch strengthens the safety development but
  retains mismatch-only strong CAS and ordinary partial-correctness proofs.
- Tofan–Schellhorn–Reif already KIV-mechanize memory safety, ABA prevention,
  linearizability, and system lock-freedom for a hazard-pointer Treiber stack.
  Colvin–Dongol already PVS-check a direct Treiber lock-freedom argument using
  a global well-founded order. Both are SC-style strong-CAS results; the 2009
  generic PVS bundle contains completed queue cases, but its legacy
  `treiber.pvs` has no proof file and leaves two obligations explicitly
  unproved.
- Derrick–Schellhorn–Wehrheim already KIV-mechanize Treiber linearizability
  for arbitrary process counts, but not progress. Parkinson et al.'s earlier
  manual hazard-pointer proof explicitly establishes neither linearizability
  nor liveness.
- Petrank–Musuvathi–Steensgaard define and check bounded lock-freedom for a
  strong-CAS SC stack and separately warn that spurious weak LL/SC can destroy
  lock-freedom despite CPU scheduling. Pani–Weissenbacher–Zuleger's Coachman
  analysis derives symbolic-\(N\) bounds for a finite
  one-operation-per-thread Treiber batch under SC, strong CAS, and garbage
  collection. Neither supplies the target infinite-demand RC11 theorem.
- Friggens checks scheduling-aware Treiber lock-freedom formulas with Spin on
  fixed small instances and separately proves unbounded Treiber
  linearizability with TVLA/3VMC. The thesis explicitly does not lift the
  progress checks to an unbounded theorem. Hoffmann–Marmar–Shao manually
  prove quantitative system-wide Treiber lock-freedom for arbitrary fixed
  finite thread/client instances under strong CAS, while
  Jia–Li–Vafeiadis automatically establish the corresponding classical result
  with CAVE and a Coq-checked generic soundness core. None admits spurious CAS
  or RC11.
- The FAC 2026 TSO article strengthens its preliminary version with
  fixed-\(k\) bounded-wait-freedom decidability, non-primitive-recursive
  complexity, and a TSO separation between wait-freedom and every fixed
  \(k\)-bound. Its generic bounded-process libraries use strong CAS and no
  Treiber. Peterson–Cook–Dechev's Coq/VST descriptor method proves progress
  for a transactional list and wait-free queue under helping assumptions,
  again without Treiber, weak memory, or primitive justice.
- Will It Fit? combines a Coq/Iris strong-CAS Treiber functional/space proof
  with bounded-time allocation-enablement liveness, not push/pop response.
  The 2026 work/span development proves finite-workload Treiber cost bounds
  and explicitly disclaims a formal lock-freedom result.
- Relinche automatically checks bounded Treiber contextual refinement under
  RC11, but only for finite executions and a fixed method-invocation bound.
  The Miri–GenMC thesis independently records that GenMC omits equal-value
  spurious weak-CAS failure and uses strong CAS in its RC11 Treiber benchmark.
- Park et al.'s iRC11 traversal development mechanizes relaxed-memory safety
  for lists, skiplists, and a priority queue with mismatch-only CAS. It has no
  Treiber client or proved progress property. Pöter's 2018 thesis already
  discusses genuine weak-CAS spurious failure inside an informal non-Treiber
  lock-freedom argument, so no priority can be claimed for that practical
  intuition.
- Mirror is Not Strong mechanizes the discovery of a genuine durable weak CAS,
  but has no Treiber client or liveness theorem and leaves its upper refinement
  unfinished. Zoo and the modular-reclamation work mechanize substantial
  Treiber safety under SC-style strong CAS, without operation progress.
- The final citation screens also retained Vafeiadis's relaxed-memory
  separation-logic work, Mével–Jourdan's weak-memory queue, Burckhardt–
  Musuvathi relaxed-memory verification, Linden–Wolper fence insertion,
  Dang's thesis version, and Baumann's context-bounded liveness work as
  context, adjacent evidence, or version audit. None supplies the target
  Treiber/weak-CAS/fairness/progress conjunction.

Accordingly, the audit already defeats broad claims such as “first Treiber
lock-freedom proof,” “first mechanized Treiber liveness proof,” “first
relaxed-memory Treiber safety proof,” “first weak-memory liveness framework,”
“first formal weak-CAS fairness mechanism,” and “first weak-memory analysis
tool supporting genuine weak CAS.” It also defeats claims to the first
additional primitive-success premise beyond scheduler fairness, the first
formal/tool-checked exact-CAS Treiber retry-loop termination proof, or the
first weak-memory model checker carrying a Treiber benchmark.

## Current conclusion and evidence level

No screened work currently proves the exact six-part conjunction. The
defensible contribution boundary remains an explicit RC11, genuinely weak-CAS
Treiber result that separates scheduler fairness, prefix-finite memory
fairness, and primitive justice; supplies an integrated all-spurious
counterexecution without primitive justice; proves unbounded system-wide
response; and composes it with machine-checked finite-prefix safety.

The audit remains between N0 and N1. N1 has not been reached because:

1. the 472-row query catalogue has not been executed as one keyed production
   discovery run: OpenAlex and Semantic Scholar rows were skipped where keys
   were unavailable, while earlier unauthenticated attempts were rate-limited;
2. OpenCitations and Semantic Scholar citation snapshots retain DOI-less or
   invalid-DOI edges, publisher-elided references, HTTP 429/404 failures,
   identifier/version aliases, and unresolved forward dates;
3. those coverage gaps mean that citation retrieval has completed zero
   protocol-complete waves even though all recorded checksum-bound queues now
   have Codex-assisted decision overlays;
4. only 179 of 230 catalogued sources have locally retained PDFs, and
   S227/PA119 in particular has only partial full-text coverage through an open
   precursor plus official journal metadata;
5. the first public formal-artifact pass is complete, but Software Heritage
   content search, package-source coverage, and systematic author-page/branch
   checks remain incomplete; and
6. the 240 canonical screening decisions and 4,267 overlay rows have not been
   human-confirmed, and the external expert-review packet has not been
   independently adjudicated.

The stopping rule is two consecutive complete snowballing rounds with no new
eligible closest work. The current count is zero protocol-complete rounds, so
the stopping rule has not been reached.

Until independent review, use a factual contribution statement rather than a
priority claim:

> We give a machine-checked progress and separation result for an explicit
> finite-thread, reclamation-free Treiber/RC11 model with genuinely weak CAS:
> weak thread fairness, prefix-finite memory visibility, and a separate weak-CAS
> justice assumption imply system-wide response progress, while thread and
> memory fairness alone admit an RC11-valid all-spurious execution.

## Required next actions

1. Execute the full 472-row catalogue with working OpenAlex and Semantic
   Scholar credentials, bounded exponential backoff, and the 2026-07-31
   cutoff; archive and checksum every response.
2. Produce one coherent two-provider citation snapshot for all 110 current
   closest seeds. Reconcile DOI/arXiv/version aliases, recover or explicitly
   bound publisher-elided and DOI-less relations, and resolve unknown forward
   dates and retryable HTTP failures.
3. Record decisions for any genuinely new candidates from that repaired
   snapshot. Only a coverage-complete first wave can advance the stopping
   counter; if it adds a closest work, seed it before running the required
   second complete no-new-closest wave.
4. Obtain independent access to the exact S227 journal text or preserve the
   current partial qualification, and complete targeted author-page, branch,
   package-source, and archival checks where the artifact report identifies a
   concrete gap.
5. Have a human reviewer confirm or correct every canonical and overlay
   decision, then send `expert-review-packet.md` to external weak-memory and
   concurrent-liveness experts. Silence must not be treated as agreement.
6. Publish a checksum-addressed raw-response and paper archive, or explicitly
   document which payloads cannot be redistributed, so the local checksum
   roots become independently reproducible evidence.
