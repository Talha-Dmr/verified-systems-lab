# Reproducible Novelty Audit

## Status

This audit is active. It is designed to support a date-bounded,
evidence-backed novelty assessment for the fair weak-CAS Treiber result. A
negative search result is not a proof that no unpublished, unindexed, or
undiscovered result exists.

The current formal result is kernel-checked and reproducible. Its publication
priority and relationship to all prior work still require the remaining
provider-complete searches, independent expert review, and peer review
described here.

Current audit snapshot (cutoff 2026-07-31):

- 230 canonical primary sources, with 179 locally retained PDFs and extracted
  texts across checksum-recorded manifests; access and retrieval failures stay
  explicit rather than being treated as negative evidence;
- five checksum-recorded primary WG21/LWG standards-history pages;
- 240 canonical screening decisions: 110 closest, 84 adjacent, 34 context,
  11 version-audit, and one secondary exclusion; all still await human
  confirmation;
- ten completed checksum-bound queue overlays containing 4,267 decisions
  with overlap preserved; the closing 179-work four-seed queue is fully
  classified and contains no new closest work, although all decisions remain
  human-pending;
- 122 theorem-level prior-art comparisons, each currently marked as not
  subsuming the candidate;
- eleven checksum-verified fixed formal-artifact bundles, plus an exact metadata
  audit of the 12.3 GB RSan image that was not downloaded; and
- 472 executable provider queries: 121 OpenAlex, 120 Semantic Scholar,
  120 DBLP, 102 Crossref, and nine arXiv rows.

No screened work currently establishes the exact six-part conjunction below.
This leaves the audit between N0 and N1, not at a priority-proof threshold.

Current canonical-file SHA-256 values:

- `primary-sources.csv`: `362e7fb072546e2214bfb1955150bfca111103071d02440add4beac7c9bcb8f7`;
- `screening.csv`: `249d17974fa20a32fa8817c55a4377f31e190a8e275342cbeaf4ccccea7da443`;
- `prior-art-matrix.csv`: `b018d07e865f299485abba919d6b2b3f39fcfd0c12935cb81e63355a35b47877`;
- `closest-work-map.csv`: `488fef5c13b613cd16c89cec7378839420f2ea64e8f8b9a86404343c57348dad`;
- `citation-seeds.csv`: `c0701685e5662af2059b93d77d0b415aa2e6972f5347cd81255fe7e7a834c545`;
- `provider-queries.csv`: `2755f87305b71c4b7e655f9c5371d939c85579dde1789156fe192e21348551b2`; and
- `artifact-sources.csv`: `7b4236830d9df5db7dc27c26ad14ef4770c8702a6fa97db0662c581b5a484be2`.

## Audit question

Has prior work already established the exact combination of:

1. an explicit finite-thread, reclamation-free Treiber stack under C11/RC11;
2. weak compare-and-exchange with unbounded spurious failure;
3. primitive weak-CAS justice separated from scheduler and memory fairness;
4. an integrated all-spurious execution proving that scheduler and memory
   fairness alone do not imply progress;
5. an unbounded system-wide response-progress theorem; and
6. machine-checked finite-prefix safety and liveness composition?

The audit also records stronger or adjacent results that would require the
claim to be narrowed even if they do not match all six dimensions.

## Files

- `claim-card.md`: exact result, assumptions, exclusions, and candidate claim;
- `protocol.md`: databases, queries, screening, extraction, and stopping rule;
- `queries.csv`: stable natural-language query families;
- `provider-queries.csv`: exact provider-specific executable queries;
- `screening.csv`: canonical inclusion and exclusion ledger (currently
  Codex-assisted and human-pending);
- `citation-screening-decisions*.csv`: checksum-bound decision overlays for
  immutable citation queues;
- `prior-art-matrix.csv`: theorem-level comparison against the closest work;
- `closest-work-map.csv`: complete foreign-key map from every current
  `include-closest` decision to its theorem-level matrix row;
- `prior-art-analysis.md`: readable synthesis and claim boundaries;
- `primary-sources.csv`: immutable paper/source download catalogue;
- `standards-history-sources.csv`: primary WG21/LWG progress-history
  catalogue;
- `artifact-sources.csv`: versioned formal-artifact download catalogue;
- `artifact-audit.md`: theorem- and source-level artifact findings;
- `artifact-index-queries.csv`: exact Zenodo and public GitHub code queries;
- `artifact-search-report.md`: public artifact and proof-archive search;
- `citation-seeds.csv`: exact snapshot of every closest-work snowball seed;
- `search-report.md`: run ledger, counts, failures, and remaining coverage;
- `expert-review-packet.md`: concise packet for independent domain experts;
- `expert-review-ledger.csv`: append-only outreach and explicit-response
  tracker;
- `scripts/search_open_indexes.py`: reproducible open-index search;
- `scripts/search_citation_graphs.py`: reproducible Semantic Scholar and
  OpenCitations backward/forward citation collector;
- `scripts/prepare_citation_screening.py`: checksum-verifying, lossless
  multi-run citation-candidate union and priority queue generator;
- `scripts/search_artifact_indexes.py`: reproducible public artifact search;
- `scripts/fetch_primary_sources.py`: checksum-recorded primary-source fetch;
- `scripts/fetch_web_sources.py`: checksum-recorded primary HTML-source
  fetch;
- `scripts/fetch_artifacts.py`: checksum-verified, path-safe artifact fetch; and
- `data/`: dated manifests, normalized records, and raw provider responses.

## Reproduce the open-index search

From `weak-memory/research/novelty-audit`:

```bash
python3 scripts/search_open_indexes.py --validate-only
python3 scripts/search_open_indexes.py \
  --providers arxiv crossref dblp semanticscholar openalex
python3 scripts/search_citation_graphs.py --validate-only
python3 scripts/search_citation_graphs.py
python3 scripts/prepare_citation_screening.py \
  --citation-run \
    data/citation-runs/20260731T022106Z \
    data/citation-runs/20260731T022348Z \
  --validate-only
python3 scripts/search_artifact_indexes.py --validate-only
python3 scripts/search_artifact_indexes.py
python3 scripts/validate_audit.py
python3 scripts/validate_citation_screening_decisions.py \
  --queue-run \
    data/citation-screening-runs/20260731T101000Z-final-four-union \
  --decisions citation-screening-decisions-20260731T101000Z.csv \
  --require-all
```

The script reads `provider-queries.csv` and writes a new UTC-stamped directory
under `data/runs/`. It never overwrites an existing run. Each run preserves
the exact query catalogue, query and script hashes, raw responses, an
append-only request manifest, normalized records, and a deduplicated view.
The current catalogue SHA-256 is
`2755f87305b71c4b7e655f9c5371d939c85579dde1789156fe192e21348551b2`.

The citation runner requires `citation-seeds.csv` to match every current
`include-closest` record. It queries Semantic Scholar and OpenCitations,
archives exact input snapshots and compressed raw responses, preserves
directed reference/citation edges, validates OpenCitations relation counts,
and writes a root checksum manifest. `SEMANTIC_SCHOLAR_API_KEY` and
`OPENCITATIONS_ACCESS_TOKEN` are optional environment variables; their values
are never written to the run. Request completion and citation-coverage
completion are separate statuses.

The current seed catalogue contains 110 closest works, SHA-256
`c0701685e5662af2059b93d77d0b415aa2e6972f5347cd81255fe7e7a834c545`.
No single historical run is retroactively presented as a complete 110-seed
wave. The historical 29-seed two-provider pass at
`data/citation-runs/20260731T010300Z/` retained 956 works and 1,456 edges but
had rate limits, publisher-elided references, identifier gaps, and unresolved
dates.

The later 31-seed union at
`data/citation-screening-runs/20260731T024138Z/` retained 1,167 works and
1,722 edges. The initial 57-row priority overlay is complete: 53 linked
existing records, two duplicate exclusions, and two topic exclusions. The
subsequent exhaustive 1,167-row overlay classifies every queued work as 192
linked-existing, 30 closest, 187 adjacent, 89 context, 97 duplicate, 91
secondary, or 481 topic decisions. All decisions remain human-pending.

The six-work CS032--CS037 supplement retained 201 works/205 edges from
OpenCitations and 197 works/199 edges from Semantic Scholar. Its lossless union
contains 268 works and 275 edges; the completed 22-row overlay has 19 linked
existing records and three topic exclusions. It led to S57--S61, including
S59/PA47 (RSan). The subsequent CS038 RSan union contains 78 works and 77
edges, and all four priority rows are linked to canonical records; that line
of screening added S62--S63.

Resolving the next high-priority full texts added S64--S85 and four closest
comparisons: CQS (PA48), GenMC (PA49), Gao and Hesselink's 2004 Treiber proof
(PA50), and Jacobs et al.'s 2018 termination proof (PA51). The matching
CS039--CS042 union at
`data/citation-screening-runs/20260731T052500Z-pending-closest-union/`
contains 237 works and 233 unique edges; all 237 are now classified. The later
65-, 245-, and 313-work overlays are also complete. The 313-work wave promoted
eight closest records, while its other 305 rows were linked, adjacent,
contextual, duplicate, secondary, or topic decisions.

An exhaustive legacy-promotion expansion at
`data/citation-screening-runs/20260731T092100Z-legacy-promotions-union/`
contains 1,978 classified works. It promoted four final theorem-level entries,
PA119--PA122; the other decisions are 157 linked-existing, 413 adjacent, 157
context, 102 duplicate, 197 secondary, and 948 topic rows.

The four promoted seeds were then expanded once more. OpenCitations retained
124 works and 131 edges; Semantic Scholar retained 116 works and 114 edges,
with two seed-metadata HTTP 429 failures and some publisher-elided references.
Their closing union at
`data/citation-screening-runs/20260731T101000Z-final-four-union/` contains 179
works. Its checksum-bound overlay is complete: 41 linked-existing, 46
adjacent, 17 context, 42 topic, 21 secondary, and 12 duplicate decisions, with
zero new closest works. The overlay SHA-256 is
`410fa05c4ba828d9731588d54849b0fcbfb18be41d515919a8a487d66b852086`;
all 179 rows remain human-pending.

The ten immutable overlays contain
57 + 22 + 4 + 237 + 65 + 245 + 313 + 1,167 + 1,978 + 179 = 4,267 decisions.
They overlap and therefore must not be interpreted as 4,267 unique works. The
protocol-complete stopping-rule count remains zero: keyed OpenAlex and Semantic
Scholar bulk discovery was unavailable for some exact-title waves, and the
citation providers retain explicit 429, DOI/identifier, publisher-elision,
date, and version-alias coverage gaps. Human confirmation, access-limited
full-text checks, an independent expert review, and two clean
protocol-complete snowballing waves remain open.

Large downloaded papers, artifact archives, and raw provider payloads are
excluded from ordinary Git tracking. Their local manifests and checksum roots
detect mutation, but a Git commit alone does not make those bytes
clone-reproducible. A publication release must include a checksum-addressed
raw-data archive (for example, a Zenodo deposit) or selectively track the
payloads it claims to preserve.

OpenAlex now requires a free `OPENALEX_API_KEY` for dependable API access.
Semantic Scholar bulk search is deliberately recorded as skipped unless
`SEMANTIC_SCHOLAR_API_KEY` is present. `CROSSREF_MAILTO` is optional. Secrets
are redacted from preserved request URLs.

Fetch the fixed primary-source and artifact corpus with:

```bash
python3 scripts/fetch_primary_sources.py
python3 scripts/fetch_web_sources.py
python3 scripts/fetch_artifacts.py
```

Paper retrieval is distributed across immutable manifests because the source
catalogue grew during citation screening. Of the 230 canonical sources, 179
PDFs and corresponding text extractions are currently retained locally.
The latest incremental manifest,
`data/papers/manifest-20260731T095210Z.csv`, downloaded S228--S230 and records
the subscription-blocked S227 journal PDF as a failure; the accessible 2007
precursor and official 2009 metadata are used only with an explicit
`full_text_checked=partial` qualification.

The current eleven-artifact integrity manifest is
`data/artifacts/manifest-20260731T091909Z.csv` (zero failures; SHA-256
`8d8c700790081215f3784dc6db8a953218ddfeaa6b6a6221405d7811064d3613`).
A08 (CQS) was safely extracted. A09 (GenMC) passed archive and per-byte
integrity checks but was audited directly from its tar stream because it
contains one absolute symbolic link; the generic extractor correctly rejected
that member. A11 is the Promising-ARM/RISC-V supplement.

Publisher and subscription-index coverage, keyed bulk-provider reruns, two
protocol-complete snowballing waves, human confirmation, and independent
expert review remain explicit steps in `protocol.md`. The recorded citation
queues themselves are fully classified.

## Evidence levels

- **N0 — candidate:** an exact theorem exists, but novelty has not been
  systematically checked.
- **N1 — reproducible internal audit:** recorded multi-index search,
  snowballing, artifact search, and a completed prior-art matrix.
- **N2 — independent field check:** the closest-work authors or other
  weak-memory experts have reviewed the claim and supplied no defeating prior
  result.
- **N3 — peer reviewed:** the scientific claim has passed venue peer review.
- **N4 — independently reproduced:** an external evaluator has exercised the
  artifact and checked its relationship to the stated claims.

The internal decision ledger, theorem-level matrix, and fixed-artifact screen
are complete, but the audit remains below N1 until the mandatory provider
coverage, two protocol-complete snowballing waves, and human confirmation are
complete. Failed, interrupted, rate-limited, or credential-skipped runs are
evidence about coverage limits, not successful searches.

## Claim discipline

Until N2, use:

> We give a machine-checked progress and separation result for an explicit
> finite-thread, reclamation-free Treiber/RC11 model with genuinely weak CAS:
> weak thread fairness, prefix-finite memory visibility, and a separate weak-CAS
> justice assumption imply system-wide response progress, while thread and
> memory fairness alone admit an RC11-valid all-spurious execution.

Do not use an unqualified “first” or “solves the open problem” claim. Any
date-bounded first-result wording must identify the search cutoff and link to
this audit.
