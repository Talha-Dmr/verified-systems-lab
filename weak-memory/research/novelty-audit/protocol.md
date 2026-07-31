# Novelty-Audit Protocol

## 1. Objective

Determine the strongest defensible, date-bounded novelty statement for the
result in `claim-card.md`. The protocol searches for exact matches, stronger
subsuming results, adjacent work that narrows the claim, and unpublished or
mechanized artifacts that ordinary bibliographic searches may miss.

## 2. Search cutoff and update policy

Each run records its UTC timestamp, provider, exact query, and
terminal/interruption status. Completed bibliographic and citation runs
preserve raw responses and normalized records; privacy-filtered interfaces and
interrupted runs document their narrower evidence boundary. The final paper
must repeat the search no more than 30 days before submission and again during
the author-response period if the venue permits updates.

## 3. Information sources

### Open bibliographic indexes

- DBLP;
- OpenAlex;
- Crossref;
- Semantic Scholar;
- the unified OpenCitations Index v1 for DOI citation edges;
- arXiv; and
- zbMATH Open where its scope applies.

### Publisher and venue archives

- ACM Digital Library;
- IEEE Xplore;
- SpringerLink;
- Dagstuhl DROPS; and
- relevant author or institutional publication pages.

Primary standards-history pages that delimit weak-CAS progress claims are
listed in `standards-history-sources.csv`. `scripts/fetch_web_sources.py`
preserves their exact HTML bytes, a deterministic text extraction, and both
checksums in a create-only manifest; live links alone are not treated as a
durable local archive.

### Subscription indexes, when available

- MathSciNet;
- Scopus; and
- Web of Science.

### Formal and software artifacts

- GitHub code and repository search;
- Software Heritage;
- Zenodo;
- Lean Reservoir, Loogle, and LeanSearch;
- Isabelle Archive of Formal Proofs;
- Rocq/Coq package and project repositories; and
- Iris project papers and artifacts.

## 4. Query strategy

`queries.csv` contains stable natural-language query families.
`provider-queries.csv` records the exact provider-specific encodings. The
encodings are deliberately not assumed to be textually identical: each
provider has different Boolean, phrase, field, paging, and cutoff semantics.
For example, arXiv searches title and abstract fields explicitly so that
authors named “Treiber” do not dominate the result set. Publisher interfaces
must also be searched with Boolean and exact-phrase variants.

The query catalogue deliberately includes:

- algorithm-first searches;
- primitive-first searches;
- fairness-first searches;
- exact counterexample terminology;
- formalization/proof-assistant searches; and
- known-author and known-paper citation expansion.

Searching for all concepts in one query is insufficient because earlier work
may use different vocabulary. Pairwise and three-way combinations are
therefore retained even when they produce more false positives.

Credential-dependent providers remain in the catalogue. A missing required
credential is recorded as `skipped`, never converted into a zero-result
search. As of the cutoff, dependable OpenAlex search requires
`OPENALEX_API_KEY`; Semantic Scholar bulk search requires
`SEMANTIC_SCHOLAR_API_KEY`.

## 5. Eligibility criteria

### Include for full-text screening

A record is included when it addresses at least two of these dimensions:

1. Treiber stacks or closely related CAS retry loops;
2. C11, RC11, axiomatic weak memory, or a model claimed to cover them;
3. weak CAS, weak compare-and-exchange, LL/SC spurious failure, or weak RMW;
4. scheduler, memory, transition, primitive, or probabilistic fairness;
5. lock-freedom, response progress, liveness, starvation, or fair
   nontermination; and
6. a mechanized proof or executable formal artifact.

A one-dimension paper may still be included when its reference graph or
terminology is likely to lead to relevant work.

### Exclude after recording

Exclude records that are:

- unrelated uses of “Treiber,” “CAS,” “justice,” or “fairness”;
- purely bounded performance experiments with no relevant semantic claim;
- duplicate versions of a work already retained, while linking all versions;
- informal tutorials that add no theorem or primary evidence; or
- secondary summaries when the primary source is available.

No record is excluded merely because it predates C11: classical progress work
is needed to delimit what is genuinely weak-memory-specific.

## 6. Deduplication

Normalize DOI values to lowercase without URL prefixes. Merge exact DOI
matches first, then arXiv identifiers, then normalized
`title + first-author + year`. Preserve a provenance list containing every
provider and query that retrieved the record. Conference, technical-report,
preprint, and journal versions are related but not silently collapsed when
their theorem content differs.

## 7. Screening procedure

1. **Metadata screening:** title, abstract, venue, year, and keywords.
2. **Full-text screening:** definitions, theorem statements, limitations,
   related work, appendices, and artifact links.
3. **Claim extraction:** populate every applicable column in
   `prior-art-matrix.csv`.
4. **Adversarial check:** search the retained full text for `weak`,
   `spurious`, `compare_exchange`, `CAS`, `RMW`, `fair`, `justice`,
   `progress`, `lock-free`, `Treiber`, `RC11`, `C11`, and `liveness`.

Every exclusion after full-text screening requires a concise reason in
`screening.csv`.

Automated relevance filtering may prioritize records, but it may not silently
discard them. Provider false-positive mechanisms—such as names, acronyms, and
stem collisions—are recorded in the run report.

## 8. Citation snowballing

For every closest work:

1. inspect all references relevant to progress, fairness, weak RMW, and
   Treiber;
2. retrieve all citing works from at least two citation indexes;
3. inspect related-work and survey papers for alternate vocabulary;
4. search every author's publication and artifact pages; and
5. repeat on each newly included closest work.

`citation-seeds.csv` must exactly snapshot every current `include-closest`
screening record. `scripts/search_citation_graphs.py` can query one or both of
Semantic Scholar and OpenCitations per pass and stores request manifests,
compressed raw responses, normalized works and directed edges, deduplicated
views, input snapshots, checksums, cutoff decisions, pagination state,
truncation, skips, and failures in a new create-only UTC-stamped directory.
Provider-specific passes may count toward one wave only when their seed set,
seed and screening snapshots, and publication cutoff match. A checksum root
detects later local mutation; independent immutability or priority requires
committing or publishing that root. Request success and citation-coverage
completeness are reported as different states.
A repository commit that excludes raw responses or downloaded corpora
timestamps only the manifests and checksum roots; it is not by itself a
clone-reproducible data release. Publication must either track the cited
payloads or deposit a checksum-addressed raw archive and record its persistent
identifier.
A run with a skipped seed, an unresolved cutoff, a
provider-imposed ceiling, unknown pagination completeness, or a failed
request is not a complete snowballing wave.

`scripts/prepare_citation_screening.py` accepts one or more citation runs,
verifies every source checksum manifest, requires one explicit publication
cutoff, and emits one queue row for every unique work while preserving the
union of provider, seed, edge, and source-run provenance. It records whether
the runs use identical seed sets, citation-seed snapshots, and screening
snapshots. Mixed historical/current snapshots may be retained as a cumulative
candidate union, but must not be represented as one protocol wave.
Transparent title-keyword scores may order the queue, but cannot exclude a
work or replace metadata/full-text judgment. Unknown dates, missing titles,
version aliases, and existing seeds remain explicit states.

Generated queue directories are immutable evidence and are not edited to add
decisions. Each `citation-screening-decisions*.csv` file is a separate overlay
bound to exactly one source queue and keyed by that queue's `candidate_id` and
`work_key`; every row repeats the source run and checksum-manifest hash. The
filename suffix identifies later queue-specific overlays, while the unsuffixed
file remains the overlay for the original 31-seed union.
`scripts/validate_citation_screening_decisions.py` verifies the entire bound
source queue checksum manifest, exact candidate identity/title, unique keys,
decision vocabulary, and links to the primary screening and theorem-level
matrix ledgers. Overlays must not be concatenated as though overlapping works
were independent candidates. Metadata exclusions may remain in an overlay.
Any new work retained after full-text review is promoted to `screening.csv`,
added to the primary-source catalogue, and, if classified as closest, receives
a `prior-art-matrix.csv` row before it becomes a seed. AI-assisted decisions
remain explicitly marked as awaiting human confirmation.

The planned stopping rule is two consecutive complete snowballing rounds with
no new eligible closest work. The report must state the actual stopping
condition reached rather than implying completeness.

## 9. Formal-artifact search

Search both repository metadata and code content with combinations of:

```text
Treiber
compare_exchange_weak
weak CAS
spurious failure
all-spurious
memory fairness
prefix-finite
weak-CAS justice
lock-freedom
system response progress
```

Record false-positive patterns and inaccessible search surfaces. A proof
artifact can defeat novelty even when its associated paper does not advertise
the theorem in its abstract.

## 10. Data extraction

For each closest work, record:

- bibliographic identity and version;
- model and language level;
- algorithm/client;
- primitive and spurious-failure semantics;
- scheduler, memory, and primitive fairness assumptions;
- positive liveness conclusion and quantifier structure;
- negative separation or counterexample;
- safety/linearizability composition;
- mechanization and proof assistant;
- artifact availability;
- exact overlap;
- exact missing dimension; and
- confidence with a supporting page, theorem, or section reference.

`closest-work-map.csv` must map every current `include-closest` screening
record to exactly one row in `prior-art-matrix.csv`. This makes extraction
coverage machine-checkable even though matrix identifiers remain stable when
screening records or versions are reorganized.

Unknown values remain `unknown`; they are never inferred from an abstract.

## 11. Independent review

Send `expert-review-packet.md`, the claim card, the closest-work matrix, and
the immutable artifact link to:

1. authors of the closest weak-memory fairness work;
2. authors of the closest weak-memory liveness work;
3. an RC11/Treiber verification expert; and
4. a formal-methods reviewer able to exercise the Lean artifact.

Ask narrow prior-art and model-fidelity questions. Silence is not treated as
agreement. Record only explicit responses that the respondent permits to be
quoted or summarized.

## 12. Reporting

The final audit reports:

- databases and exact interfaces;
- complete queries and dates;
- retrieved, deduplicated, screened, included, and excluded counts;
- the search and snowballing stopping state;
- access limitations;
- the complete prior-art matrix;
- expert feedback and unresolved objections;
- changes made to the candidate claim; and
- an N0--N4 evidence level from `README.md`.

AI systems may expand synonyms, rank records, and assist extraction. Every
included/excluded decision and every theorem-level comparison must be checked
against the primary source by a human reviewer.
