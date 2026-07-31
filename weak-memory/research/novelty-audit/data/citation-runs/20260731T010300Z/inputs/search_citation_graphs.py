#!/usr/bin/env python3
"""Collect reproducible one-hop citation graphs for the novelty-audit seeds.

The collector uses only Python's standard library and public, unauthenticated
endpoints:

* Semantic Scholar Academic Graph individual-paper, references, and citations;
* the OpenCitations COCI v1 references and citations compatibility endpoints.

Every run is a new timestamped directory. Provider payloads are retained as
deterministically gzipped bytes, and provider limitations are represented in
the manifest instead of being silently treated as negative search results.
"""

from __future__ import annotations

import argparse
import csv
import email.utils
import gzip
import hashlib
import http.client
import io
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


SCRIPT_VERSION = "2"
PUBLICATION_CUTOFF = "2026-07-31"
DEFAULT_PROVIDERS = ("semanticscholar", "opencitations")
PROVIDERS = set(DEFAULT_PROVIDERS)
USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
SEMANTIC_SCHOLAR_BASE = "https://api.semanticscholar.org/graph/v1"
OPENCITATIONS_COCI_BASE = "https://api.opencitations.net/index/v1"
SEMANTIC_SCHOLAR_PAGE_SIZE = 1000
SEMANTIC_SCHOLAR_DELAY_SECONDS = 1.0
OPENCITATIONS_DELAY_SECONDS = 0.5
MAX_RESPONSE_BYTES = 100 * 1024 * 1024
DOI_RE = re.compile(r"^10\.\d{4,9}/\S+$", re.IGNORECASE)
RUN_ID_RE = re.compile(r"^\d{8}T\d{6}Z(?:-[a-z0-9][a-z0-9._-]*)?$")

SEED_FIELDS = (
    "seed_id",
    "screening_record_id",
    "title",
    "year",
    "publication_date",
    "doi",
    "arxiv_id",
    "semantic_scholar_id",
    "screening_decision",
    "cutoff_basis",
    "provider_notes",
)

MANIFEST_FIELDS = (
    "provider",
    "seed_id",
    "screening_record_id",
    "direction",
    "operation_status",
    "identity_status",
    "page_index",
    "cursor_in",
    "cursor_out",
    "requested_url",
    "final_url",
    "retrieved_at_utc",
    "http_status",
    "response_date",
    "response_etag",
    "rate_limit_remaining",
    "attempt_count",
    "retry_delays_seconds",
    "content_type",
    "total_results",
    "returned_results",
    "retained_results",
    "cumulative_results",
    "normalization_error_count",
    "raw_file",
    "raw_sha256",
    "raw_gzip_sha256",
    "truncated",
    "pagination_complete",
    "coverage_note",
    "error",
)

WORK_FIELDS = (
    "provider",
    "seed_id",
    "screening_record_id",
    "provider_work_id",
    "work_key",
    "title",
    "year",
    "publication_date",
    "authors",
    "doi",
    "arxiv_id",
    "venue",
    "url",
    "citation_count",
    "reference_count",
    "cutoff_status",
    "raw_file",
)

EDGE_FIELDS = (
    "provider",
    "seed_id",
    "screening_record_id",
    "direction",
    "edge_key",
    "source_work_key",
    "target_work_key",
    "source_provider_id",
    "target_provider_id",
    "source_doi",
    "target_doi",
    "provider_edge_id",
    "citing_publication_date",
    "cutoff_status",
    "raw_file",
)

DEDUP_WORK_FIELDS = (
    "work_key",
    "title",
    "year",
    "publication_date",
    "authors",
    "doi",
    "arxiv_id",
    "venue",
    "url",
    "citation_count",
    "reference_count",
    "providers",
    "provider_work_ids",
    "seed_ids",
    "screening_record_ids",
    "cutoff_status",
    "cutoff_statuses",
)

DEDUP_EDGE_FIELDS = (
    "edge_key",
    "source_work_key",
    "target_work_key",
    "source_doi",
    "target_doi",
    "providers",
    "seed_ids",
    "screening_record_ids",
    "directions",
    "provider_edge_ids",
    "citing_publication_date",
    "cutoff_status",
    "cutoff_statuses",
)

SEMANTIC_SCHOLAR_FIELDS = ",".join(
    (
        "paperId",
        "corpusId",
        "externalIds",
        "url",
        "title",
        "venue",
        "year",
        "referenceCount",
        "citationCount",
        "publicationDate",
        "publicationTypes",
        "authors",
    )
)


@dataclass(frozen=True)
class Seed:
    seed_id: str
    screening_record_id: str
    title: str
    year: str
    publication_date: str
    doi: str
    arxiv_id: str
    semantic_scholar_id: str
    screening_decision: str
    cutoff_basis: str
    provider_notes: str


@dataclass(frozen=True)
class HttpResult:
    payload: bytes
    status: int
    headers: dict[str, str]
    final_url: str
    error: str
    attempt_count: int
    retry_delays_seconds: str


def clean_text(value: Any) -> str:
    if value is None:
        return ""
    text = str(value)
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def normalize_doi(value: Any) -> str:
    doi = clean_text(value).lower()
    for prefix in (
        "https://doi.org/",
        "http://doi.org/",
        "doi:",
    ):
        if doi.startswith(prefix):
            doi = doi[len(prefix) :]
    return doi.strip()


def normalize_arxiv_id(value: Any) -> str:
    identifier = clean_text(value)
    for prefix in (
        "https://arxiv.org/abs/",
        "http://arxiv.org/abs/",
        "arxiv:",
    ):
        if identifier.lower().startswith(prefix):
            identifier = identifier[len(prefix) :]
            break
    identifier = identifier.lower().strip()
    return re.sub(r"v\d+$", "", identifier)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def git_commit(path: Path) -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=path,
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def csv_rows_from_bytes(
    payload: bytes,
    path: Path,
) -> tuple[list[str], list[dict[str, str]]]:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path} is not UTF-8: {error}") from error
    with io.StringIO(text, newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
        fields = list(reader.fieldnames or [])
    malformed = [
        index + 2
        for index, row in enumerate(rows)
        if row.get(None) is not None
        or any(
            value is None
            for key, value in row.items()
            if key is not None
        )
    ]
    if malformed:
        raise ValueError(f"{path} has malformed CSV rows: {malformed}")
    return fields, rows


def valid_partial_date(value: str) -> bool:
    if not value:
        return True
    formats = {
        4: "%Y",
        7: "%Y-%m",
        10: "%Y-%m-%d",
    }
    date_format = formats.get(len(value))
    if not date_format:
        return False
    try:
        datetime.strptime(value, date_format)
        return True
    except ValueError:
        return False


def read_seeds(path: Path, payload: bytes) -> list[Seed]:
    fields, rows = csv_rows_from_bytes(payload, path)
    if tuple(fields) != SEED_FIELDS:
        raise ValueError(
            f"{path} must have exactly these columns in this order: "
            f"{list(SEED_FIELDS)}"
        )
    seeds = [
        Seed(
            seed_id=clean_text(row["seed_id"]),
            screening_record_id=clean_text(row["screening_record_id"]),
            title=clean_text(row["title"]),
            year=clean_text(row["year"]),
            publication_date=clean_text(row["publication_date"]),
            doi=normalize_doi(row["doi"]),
            arxiv_id=normalize_arxiv_id(row["arxiv_id"]),
            semantic_scholar_id=clean_text(
                row["semantic_scholar_id"]
            ),
            screening_decision=clean_text(
                row["screening_decision"]
            ),
            cutoff_basis=clean_text(row["cutoff_basis"]),
            provider_notes=clean_text(row["provider_notes"]),
        )
        for row in rows
    ]
    if not seeds:
        raise ValueError("the citation seed catalogue is empty")

    for field in ("seed_id", "screening_record_id"):
        values = [getattr(seed, field) for seed in seeds]
        if any(not value for value in values):
            raise ValueError(f"{field} values must be nonempty")
        if len(values) != len(set(values)):
            raise ValueError(f"{field} values must be unique")

    if any(not re.fullmatch(r"CS\d{3}", seed.seed_id) for seed in seeds):
        raise ValueError("seed_id values must match CS followed by three digits")
    if any(not seed.title for seed in seeds):
        raise ValueError("every seed needs a nonempty title")
    if any(not re.fullmatch(r"\d{4}", seed.year) for seed in seeds):
        raise ValueError("every seed year must contain four digits")
    invalid_dates = [
        (seed.seed_id, seed.publication_date)
        for seed in seeds
        if not valid_partial_date(seed.publication_date)
    ]
    if invalid_dates:
        raise ValueError(f"invalid seed publication dates: {invalid_dates}")
    inconsistent_dates = [
        seed.seed_id
        for seed in seeds
        if seed.publication_date
        and not seed.publication_date.startswith(seed.year)
    ]
    if inconsistent_dates:
        raise ValueError(
            "seed year/publication_date disagreement: "
            f"{inconsistent_dates}"
        )
    unresolved_cutoffs = [
        seed.seed_id
        for seed in seeds
        if cutoff_status(seed.publication_date, seed.year)
        != "included"
    ]
    if unresolved_cutoffs:
        raise ValueError(
            "every seed must identify an eligible version on or before "
            f"{PUBLICATION_CUTOFF}; unresolved={unresolved_cutoffs}"
        )
    if any(not seed.cutoff_basis for seed in seeds):
        raise ValueError("every seed needs a nonempty cutoff_basis")
    if any(seed.screening_decision != "include-closest" for seed in seeds):
        raise ValueError("every citation seed must be an include-closest record")

    dois = [seed.doi for seed in seeds if seed.doi]
    if len(dois) != len(set(dois)):
        raise ValueError("nonempty DOI values must be unique")
    invalid_dois = [doi for doi in dois if not DOI_RE.fullmatch(doi)]
    if invalid_dois:
        raise ValueError(f"invalid DOI values: {invalid_dois}")
    arxiv_ids = [seed.arxiv_id for seed in seeds if seed.arxiv_id]
    if len(arxiv_ids) != len(set(arxiv_ids)):
        raise ValueError("nonempty arXiv identifiers must be unique")

    scholar_ids = [
        seed.semantic_scholar_id
        for seed in seeds
        if seed.semantic_scholar_id
    ]
    if len(scholar_ids) != len(set(scholar_ids)):
        raise ValueError("nonempty semantic_scholar_id values must be unique")
    for seed in seeds:
        if seed.semantic_scholar_id:
            prefix, separator, value = seed.semantic_scholar_id.partition(":")
            if not separator or prefix.upper() not in {
                "ARXIV",
                "DOI",
                "CORPUSID",
                "DBLP",
                "MAG",
                "PMID",
                "PMCID",
                "URL",
            } or not value:
                raise ValueError(
                    f"{seed.seed_id} has an unsupported Semantic Scholar "
                    "identifier"
                )
            if (
                prefix.upper() == "DOI"
                and normalize_doi(value) != seed.doi
            ):
                raise ValueError(
                    f"{seed.seed_id} Semantic Scholar DOI does not match "
                    "the catalog DOI"
                )
            if (
                prefix.upper() == "ARXIV"
                and normalize_arxiv_id(value) != seed.arxiv_id
            ):
                raise ValueError(
                    f"{seed.seed_id} Semantic Scholar arXiv ID does not "
                    "match the catalog arxiv_id"
                )
    return seeds


def cross_check_screening(
    seeds: list[Seed],
    path: Path,
    payload: bytes,
) -> None:
    fields, rows = csv_rows_from_bytes(payload, path)
    required = {"record_id", "title", "year", "doi", "decision"}
    missing = required - set(fields)
    if missing:
        raise ValueError(
            f"{path} lacks screening columns: {sorted(missing)}"
        )
    record_ids = [clean_text(row["record_id"]) for row in rows]
    duplicates = sorted(
        {
            record_id
            for record_id in record_ids
            if record_ids.count(record_id) > 1
        }
    )
    if any(not record_id for record_id in record_ids):
        raise ValueError(f"{path} contains an empty record_id")
    if duplicates:
        raise ValueError(
            f"{path} contains duplicate record IDs: {duplicates}"
        )
    closest = {
        clean_text(row["record_id"]): row
        for row in rows
        if clean_text(row["decision"]) == "include-closest"
    }

    catalog = {seed.screening_record_id: seed for seed in seeds}
    missing_seeds = set(closest) - set(catalog)
    stale_seeds = set(catalog) - set(closest)
    if missing_seeds or stale_seeds:
        raise ValueError(
            "citation-seeds.csv does not exactly snapshot current "
            f"include-closest records; missing={sorted(missing_seeds)}, "
            f"stale={sorted(stale_seeds)}"
        )
    for record_id, row in closest.items():
        seed = catalog[record_id]
        expected = (
            clean_text(row["title"]),
            clean_text(row["year"]),
            normalize_doi(row["doi"]),
        )
        actual = (seed.title, seed.year, seed.doi)
        if actual != expected:
            raise ValueError(
                f"{seed.seed_id} disagrees with screening.csv for "
                f"{record_id}: expected={expected!r}, actual={actual!r}"
            )


def response_headers(value: Any) -> dict[str, str]:
    return {
        "date": clean_text(value.get("Date")),
        "etag": clean_text(value.get("ETag")),
        "rate_limit_remaining": clean_text(
            value.get("x-ratelimit-remaining")
            or value.get("x-rate-limit-remaining")
        ),
        "content_type": clean_text(value.get("Content-Type")),
    }


def retry_delay_seconds(
    retry_after: str,
    attempt: int,
) -> float:
    retry_after = clean_text(retry_after)
    if re.fullmatch(r"\d+(?:\.\d+)?", retry_after):
        base = float(retry_after)
    else:
        base = float(2**attempt)
        if retry_after:
            try:
                retry_date = email.utils.parsedate_to_datetime(
                    retry_after
                )
                if retry_date.tzinfo is None:
                    retry_date = retry_date.replace(tzinfo=timezone.utc)
                base = max(
                    0.0,
                    (retry_date - datetime.now(timezone.utc)).total_seconds(),
                )
            except (TypeError, ValueError, OverflowError):
                pass
    return min(60.0, max(1.0, base + random.uniform(0.0, 0.25)))


def request_bytes(url: str, timeout: float, retries: int) -> HttpResult:
    headers = {
        "Accept": "application/json",
        "User-Agent": USER_AGENT,
    }
    if url.startswith(SEMANTIC_SCHOLAR_BASE):
        api_key = os.environ.get("SEMANTIC_SCHOLAR_API_KEY", "")
        if api_key:
            headers["x-api-key"] = api_key
    if url.startswith(OPENCITATIONS_COCI_BASE):
        token = os.environ.get("OPENCITATIONS_ACCESS_TOKEN", "")
        if token:
            headers["authorization"] = token
    request = urllib.request.Request(
        url,
        headers=headers,
    )
    delays: list[str] = []
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read(MAX_RESPONSE_BYTES + 1)
                if len(payload) > MAX_RESPONSE_BYTES:
                    raise RuntimeError(
                        "response exceeds MAX_RESPONSE_BYTES"
                    )
                return HttpResult(
                    payload=payload,
                    status=int(response.status),
                    headers=response_headers(response.headers),
                    final_url=response.geturl(),
                    error="",
                    attempt_count=attempt + 1,
                    retry_delays_seconds=";".join(delays),
                )
        except urllib.error.HTTPError as error:
            payload = error.read()
            retryable = error.code == 429 or 500 <= error.code < 600
            if retryable and attempt < retries:
                delay = retry_delay_seconds(
                    clean_text(error.headers.get("Retry-After")),
                    attempt,
                )
                delays.append(f"{delay:.3f}")
                time.sleep(delay)
                continue
            return HttpResult(
                payload=payload,
                status=int(error.code),
                headers=response_headers(error.headers),
                final_url=error.geturl(),
                error=f"HTTPError: {error.code} {clean_text(error.reason)}",
                attempt_count=attempt + 1,
                retry_delays_seconds=";".join(delays),
            )
        except (
            urllib.error.URLError,
            TimeoutError,
            ConnectionResetError,
            http.client.RemoteDisconnected,
        ) as error:
            if attempt < retries:
                delay = retry_delay_seconds("", attempt)
                delays.append(f"{delay:.3f}")
                time.sleep(delay)
                continue
            raise RuntimeError(
                f"{type(error).__name__}: {clean_text(error)}"
            ) from error
    raise RuntimeError("unreachable request retry state")


def write_csv(
    path: Path,
    fields: Iterable[str],
    rows: Iterable[dict[str, Any]],
) -> None:
    with path.open("x", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(fields),
            extrasaction="ignore",
        )
        writer.writeheader()
        writer.writerows(rows)


def append_csv_row(
    path: Path,
    fields: Iterable[str],
    row: dict[str, Any],
) -> None:
    exists = path.exists()
    with path.open("a", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(fields),
            extrasaction="ignore",
        )
        if not exists:
            writer.writeheader()
        writer.writerow(row)
        handle.flush()


def write_json(path: Path, value: Any) -> None:
    with path.open("x", encoding="utf-8") as handle:
        json.dump(
            value,
            handle,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        handle.write("\n")


def cutoff_status(publication_date: str, year: str) -> str:
    date = clean_text(publication_date)
    year = clean_text(year)
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
        return (
            "included"
            if date <= PUBLICATION_CUTOFF
            else "excluded-after-cutoff"
        )
    if re.fullmatch(r"\d{4}-\d{2}", date):
        cutoff_month = PUBLICATION_CUTOFF[:7]
        return (
            "included"
            if date <= cutoff_month
            else "excluded-after-cutoff"
        )
    candidate_year = date if re.fullmatch(r"\d{4}", date) else year
    if re.fullmatch(r"\d{4}", candidate_year):
        if candidate_year < PUBLICATION_CUTOFF[:4]:
            return "included"
        if candidate_year > PUBLICATION_CUTOFF[:4]:
            return "excluded-after-cutoff"
    return "unknown-date"


def canonical_work_key(
    doi: str,
    arxiv_id: str,
    provider_work_id: str,
    fallback: str,
) -> str:
    doi = normalize_doi(doi)
    arxiv_id = normalize_arxiv_id(arxiv_id)
    provider_work_id = clean_text(provider_work_id)
    arxiv_doi = re.fullmatch(
        r"10\.48550/arxiv\.(.+)",
        doi,
        re.IGNORECASE,
    )
    if arxiv_doi:
        arxiv_id = normalize_arxiv_id(arxiv_doi.group(1))
        doi = ""
    if doi:
        return f"doi:{doi}"
    if arxiv_id:
        return f"arxiv:{arxiv_id}"
    if provider_work_id:
        return f"s2:{provider_work_id.lower()}"
    return fallback


def seed_work(seed: Seed) -> dict[str, str]:
    prefer_arxiv = seed.semantic_scholar_id.upper().startswith("ARXIV:")
    work_key = canonical_work_key(
        "" if prefer_arxiv else seed.doi,
        seed.arxiv_id,
        "",
        f"seed:{seed.screening_record_id.lower()}",
    )
    return {
        "provider": "seed-catalog",
        "seed_id": seed.seed_id,
        "screening_record_id": seed.screening_record_id,
        "provider_work_id": seed.semantic_scholar_id,
        "work_key": work_key,
        "title": seed.title,
        "year": seed.year,
        "publication_date": seed.publication_date,
        "authors": "",
        "doi": seed.doi,
        "arxiv_id": seed.arxiv_id,
        "venue": "",
        "url": "",
        "citation_count": "",
        "reference_count": "",
        "cutoff_status": cutoff_status(
            seed.publication_date,
            seed.year,
        ),
        "raw_file": "",
    }


def join_authors(value: Any) -> str:
    if not isinstance(value, list):
        return ""
    return "; ".join(
        clean_text(author.get("name"))
        for author in value
        if isinstance(author, dict) and clean_text(author.get("name"))
    )


def semantic_scholar_work(
    paper: dict[str, Any],
    seed: Seed,
    raw_file: str,
    fallback: str,
    forced_work_key: str = "",
) -> dict[str, str]:
    external = paper.get("externalIds") or {}
    if not isinstance(external, dict):
        external = {}
    doi = normalize_doi(external.get("DOI"))
    arxiv_id = normalize_arxiv_id(external.get("ArXiv"))
    provider_id = clean_text(paper.get("paperId"))
    publication_date = clean_text(paper.get("publicationDate"))
    year = clean_text(paper.get("year"))
    return {
        "provider": "semanticscholar",
        "seed_id": seed.seed_id,
        "screening_record_id": seed.screening_record_id,
        "provider_work_id": provider_id,
        "work_key": forced_work_key
        or canonical_work_key(
            doi,
            arxiv_id,
            provider_id,
            fallback,
        ),
        "title": clean_text(paper.get("title")),
        "year": year,
        "publication_date": publication_date,
        "authors": join_authors(paper.get("authors")),
        "doi": doi,
        "arxiv_id": arxiv_id,
        "venue": clean_text(paper.get("venue")),
        "url": clean_text(paper.get("url")),
        "citation_count": clean_text(paper.get("citationCount")),
        "reference_count": clean_text(paper.get("referenceCount")),
        "cutoff_status": cutoff_status(publication_date, year),
        "raw_file": raw_file,
    }


def normalized_title(value: Any) -> str:
    return re.sub(
        r"[^a-z0-9]+",
        "",
        clean_text(value).casefold(),
    )


def semantic_seed_identity(
    paper: dict[str, Any],
    seed: Seed,
) -> str:
    external = paper.get("externalIds") or {}
    if not isinstance(external, dict):
        external = {}
    returned_doi = normalize_doi(external.get("DOI"))
    returned_arxiv = normalize_arxiv_id(external.get("ArXiv"))
    requested_prefix, _, requested_value = (
        seed.semantic_scholar_id.partition(":")
    )
    if requested_prefix.upper() == "DOI" and (
        returned_doi == normalize_doi(requested_value)
    ):
        return "verified-primary"
    if requested_prefix.upper() == "ARXIV" and (
        returned_arxiv == normalize_arxiv_id(requested_value)
    ):
        return "verified-primary"
    if (
        (seed.doi and returned_doi == seed.doi)
        or (
            seed.arxiv_id
            and returned_arxiv == seed.arxiv_id
        )
    ):
        return "verified-alias"
    if normalized_title(paper.get("title")) == normalized_title(seed.title):
        return "title-only"
    return "mismatch"


def edge_row(
    provider: str,
    seed: Seed,
    direction: str,
    source: dict[str, str],
    target: dict[str, str],
    provider_edge_id: str,
    citing_publication_date: str,
    raw_file: str,
) -> dict[str, str]:
    source_key = source["work_key"]
    target_key = target["work_key"]
    return {
        "provider": provider,
        "seed_id": seed.seed_id,
        "screening_record_id": seed.screening_record_id,
        "direction": direction,
        "operation_status": "pending",
        "edge_key": f"{source_key}->{target_key}",
        "source_work_key": source_key,
        "target_work_key": target_key,
        "source_provider_id": source["provider_work_id"],
        "target_provider_id": target["provider_work_id"],
        "source_doi": source["doi"],
        "target_doi": target["doi"],
        "provider_edge_id": clean_text(provider_edge_id),
        "citing_publication_date": citing_publication_date,
        "cutoff_status": cutoff_status(
            citing_publication_date,
            source["year"],
        ),
        "raw_file": raw_file,
    }


def manifest_template(
    provider: str,
    seed: Seed,
    direction: str,
    page_index: int,
    cursor_in: str,
    requested_url: str,
) -> dict[str, str]:
    return {
        "provider": provider,
        "seed_id": seed.seed_id,
        "screening_record_id": seed.screening_record_id,
        "direction": direction,
        "operation_status": "pending",
        "identity_status": "not-checked",
        "page_index": str(page_index),
        "cursor_in": cursor_in,
        "cursor_out": "",
        "requested_url": requested_url,
        "final_url": "",
        "retrieved_at_utc": "",
        "http_status": "",
        "response_date": "",
        "response_etag": "",
        "rate_limit_remaining": "",
        "attempt_count": "",
        "retry_delays_seconds": "",
        "content_type": "",
        "total_results": "",
        "returned_results": "0",
        "retained_results": "0",
        "cumulative_results": "0",
        "normalization_error_count": "0",
        "raw_file": "",
        "raw_sha256": "",
        "raw_gzip_sha256": "",
        "truncated": "unknown",
        "pagination_complete": "no",
        "coverage_note": "",
        "error": "",
    }


def skipped_manifest(
    provider: str,
    seed: Seed,
    direction: str,
    reason: str,
) -> dict[str, str]:
    row = manifest_template(provider, seed, direction, 0, "", "")
    row.update(
        {
            "retrieved_at_utc": utc_now(),
            "operation_status": "skipped",
            "truncated": "unknown",
            "pagination_complete": "not-attempted",
            "error": f"SKIPPED: {reason}",
        }
    )
    return row


def fetch_json(
    run_dir: Path,
    raw_relative: Path,
    entry: dict[str, str],
    timeout: float,
    retries: int,
) -> tuple[Any | None, dict[str, str]]:
    try:
        result = request_bytes(
            entry["requested_url"],
            timeout,
            retries,
        )
    except Exception as error:
        entry.update(
            {
                "retrieved_at_utc": utc_now(),
                "operation_status": "failed",
                "error": f"{type(error).__name__}: {clean_text(error)}",
            }
        )
        return None, entry

    entry.update(
        {
            "retrieved_at_utc": utc_now(),
            "http_status": str(result.status),
            "response_date": result.headers["date"],
            "response_etag": result.headers["etag"],
            "rate_limit_remaining": result.headers[
                "rate_limit_remaining"
            ],
            "attempt_count": str(result.attempt_count),
            "retry_delays_seconds": result.retry_delays_seconds,
            "content_type": result.headers["content_type"],
            "final_url": result.final_url,
        }
    )
    if result.payload:
        raw_path = run_dir / raw_relative
        compressed = gzip.compress(
            result.payload,
            compresslevel=9,
            mtime=0,
        )
        with raw_path.open("xb") as handle:
            handle.write(compressed)
        entry.update(
            {
                "raw_file": str(raw_relative),
                "raw_sha256": sha256_bytes(result.payload),
                "raw_gzip_sha256": sha256_bytes(compressed),
            }
        )
    if result.error:
        entry["operation_status"] = "failed"
        entry["error"] = result.error
        return None, entry
    try:
        document = json.loads(result.payload)
        entry["operation_status"] = "success"
        return document, entry
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        entry["operation_status"] = "failed"
        entry["error"] = (
            f"{type(error).__name__}: {clean_text(error)}"
        )
        return None, entry


def query_semantic_scholar(
    seed: Seed,
    run_dir: Path,
    manifest_path: Path,
    works: list[dict[str, str]],
    edges: list[dict[str, str]],
    timeout: float,
    retries: int,
    ceiling: int,
) -> None:
    if not seed.semantic_scholar_id:
        reason = "the seed has no Semantic Scholar-supported identifier"
        for direction in ("metadata", "references", "citations"):
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                skipped_manifest(
                    "semanticscholar",
                    seed,
                    direction,
                    reason,
                ),
            )
        return

    encoded_id = urllib.parse.quote(
        seed.semantic_scholar_id,
        safe="",
    )
    metadata_url = (
        f"{SEMANTIC_SCHOLAR_BASE}/paper/{encoded_id}?"
        f"{urllib.parse.urlencode({'fields': SEMANTIC_SCHOLAR_FIELDS})}"
    )
    metadata_raw = Path("raw") / (
        f"{seed.seed_id.lower()}-metadata-p0001-"
        "semanticscholar.json.gz"
    )
    metadata_entry = manifest_template(
        "semanticscholar",
        seed,
        "metadata",
        0,
        "",
        metadata_url,
    )
    document, metadata_entry = fetch_json(
        run_dir,
        metadata_raw,
        metadata_entry,
        timeout,
        retries,
    )
    semantic_seed = seed_work(seed)
    if document is not None:
        if not isinstance(document, dict) or (
            not document.get("paperId") and not document.get("title")
        ):
            metadata_entry["error"] = (
                "ValueError: Semantic Scholar metadata response is not "
                "a paper object"
            )
            metadata_entry["operation_status"] = "failed"
        else:
            semantic_seed = semantic_scholar_work(
                document,
                seed,
                metadata_entry["raw_file"],
                seed_work(seed)["work_key"],
                seed_work(seed)["work_key"],
            )
            works.append(semantic_seed)
            metadata_entry["identity_status"] = semantic_seed_identity(
                document,
                seed,
            )
            if metadata_entry["identity_status"] == "mismatch":
                metadata_entry["error"] = (
                    "IdentityMismatch: Semantic Scholar metadata does not "
                    "match the requested seed identifier or title"
                )
                metadata_entry["operation_status"] = "failed"
            elif metadata_entry["identity_status"] == "title-only":
                metadata_entry["coverage_note"] = (
                    "Seed identity matched only by normalized title; "
                    "provider identifiers did not match the catalog"
                )
                metadata_entry["operation_status"] = (
                    "success-with-limitations"
                )
            metadata_entry.update(
                {
                    "total_results": "1",
                    "returned_results": "1",
                    "retained_results": "1",
                    "cumulative_results": "1",
                    "truncated": "no",
                    "pagination_complete": "yes",
                }
            )
    append_csv_row(
        manifest_path,
        MANIFEST_FIELDS,
        metadata_entry,
    )
    time.sleep(SEMANTIC_SCHOLAR_DELAY_SECONDS)
    if metadata_entry["identity_status"] == "mismatch":
        for direction in ("references", "citations"):
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                skipped_manifest(
                    "semanticscholar",
                    seed,
                    direction,
                    "seed metadata identity mismatch",
                ),
            )
        return

    for direction, paper_field in (
        ("references", "citedPaper"),
        ("citations", "citingPaper"),
    ):
        offset = 0
        cumulative = 0
        page_index = 0
        while cumulative < ceiling:
            limit = min(
                SEMANTIC_SCHOLAR_PAGE_SIZE,
                ceiling - cumulative,
            )
            parameters = urllib.parse.urlencode(
                {
                    "fields": SEMANTIC_SCHOLAR_FIELDS,
                    "offset": str(offset),
                    "limit": str(limit),
                }
            )
            url = (
                f"{SEMANTIC_SCHOLAR_BASE}/paper/{encoded_id}/"
                f"{direction}?{parameters}"
            )
            raw_relative = Path("raw") / (
                f"{seed.seed_id.lower()}-{direction}-"
                f"p{page_index + 1:04d}-semanticscholar.json.gz"
            )
            entry = manifest_template(
                "semanticscholar",
                seed,
                direction,
                page_index,
                str(offset),
                url,
            )
            document, entry = fetch_json(
                run_dir,
                raw_relative,
                entry,
                timeout,
                retries,
            )
            if document is None:
                append_csv_row(
                    manifest_path,
                    MANIFEST_FIELDS,
                    entry,
                )
                break
            if not isinstance(document, dict) or not isinstance(
                document.get("data"),
                list,
            ):
                entry["error"] = (
                    "ValueError: Semantic Scholar relation response lacks "
                    "a data array"
                )
                entry["operation_status"] = "failed"
                append_csv_row(
                    manifest_path,
                    MANIFEST_FIELDS,
                    entry,
                )
                break

            data = document["data"]
            remaining = ceiling - cumulative
            retained = data[:remaining]
            returned = len(data)
            cumulative += len(retained)
            total = document.get("total")
            next_value = document.get("next")
            if isinstance(next_value, int):
                next_cursor = str(next_value)
            elif (
                isinstance(next_value, str)
                and next_value.isdigit()
            ):
                next_cursor = next_value
            elif next_value is None:
                next_cursor = ""
            else:
                entry["error"] = (
                    "ValueError: Semantic Scholar returned a "
                    "non-numeric pagination cursor"
                )
                entry["operation_status"] = "failed"
                entry["truncated"] = "unknown"
                entry["pagination_complete"] = "no"
                append_csv_row(
                    manifest_path,
                    MANIFEST_FIELDS,
                    entry,
                )
                break
            more_pages = bool(next_cursor)
            if more_pages and cumulative >= ceiling:
                truncated = "yes"
                pagination_complete = "no"
            elif more_pages:
                truncated = "unknown"
                pagination_complete = "no"
            else:
                truncated = "no"
                pagination_complete = "yes"

            entry.update(
                {
                    "cursor_out": next_cursor,
                    "total_results": (
                        str(total) if isinstance(total, int) else ""
                    ),
                    "returned_results": str(returned),
                    "retained_results": str(len(retained)),
                    "cumulative_results": str(cumulative),
                    "truncated": truncated,
                    "pagination_complete": pagination_complete,
                }
            )
            if returned > limit:
                entry["coverage_note"] = (
                    "Semantic Scholar returned more rows than requested"
                )
                entry["operation_status"] = "success-with-limitations"
            if (
                not more_pages
                and isinstance(total, int)
                and cumulative != total
            ):
                entry["coverage_note"] = (
                    "Semantic Scholar terminal cumulative count does not "
                    f"match provider total ({cumulative} != {total})"
                )
                entry["operation_status"] = "success-with-limitations"
                entry["pagination_complete"] = "no"
                entry["truncated"] = "unknown"

            normalization_errors = 0
            for index, relation in enumerate(retained):
                if not isinstance(relation, dict):
                    normalization_errors += 1
                    continue
                paper = relation.get(paper_field)
                if not isinstance(paper, dict):
                    normalization_errors += 1
                    continue
                related = semantic_scholar_work(
                    paper,
                    seed,
                    entry["raw_file"],
                    (
                        f"unknown:semanticscholar:{seed.seed_id.lower()}:"
                        f"{direction}:{page_index}:{index}"
                    ),
                )
                works.append(related)
                if direction == "references":
                    source, target = semantic_seed, related
                else:
                    source, target = related, semantic_seed
                citing_date = (
                    source["publication_date"] or source["year"]
                )
                edges.append(
                    edge_row(
                        "semanticscholar",
                        seed,
                        direction,
                        source,
                        target,
                        "",
                        citing_date,
                        entry["raw_file"],
                    )
                )
            if normalization_errors:
                entry["normalization_error_count"] = str(
                    normalization_errors
                )
                entry["operation_status"] = "success-with-limitations"
                note = (
                    f"{normalization_errors} relation rows lacked a "
                    "normalizable paper object"
                )
                entry["coverage_note"] = "; ".join(
                    part
                    for part in (entry["coverage_note"], note)
                    if part
                )
            if more_pages:
                if int(next_cursor) <= offset:
                    entry["error"] = (
                        "ValueError: Semantic Scholar pagination did not "
                        "advance"
                    )
                    entry["operation_status"] = "failed"
                    entry["truncated"] = "unknown"
                    append_csv_row(
                        manifest_path,
                        MANIFEST_FIELDS,
                        entry,
                    )
                    break
                offset = int(next_cursor)
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                entry,
            )
            if entry["error"] or not more_pages:
                break
            page_index += 1
            time.sleep(SEMANTIC_SCHOLAR_DELAY_SECONDS)
        time.sleep(SEMANTIC_SCHOLAR_DELAY_SECONDS)


def unprefix_opencitations(value: Any) -> str:
    text = clean_text(value)
    parts = [part.strip() for part in text.split(";") if part.strip()]
    preferred: list[str] = []
    fallback: list[str] = []
    for part in parts:
        if "=>" in part:
            prefix, content = part.split("=>", 1)
            content = content.strip()
            fallback.append(content)
            if clean_text(prefix).casefold() == "coci":
                preferred.append(content)
        else:
            fallback.append(part)
    values = preferred or fallback
    return values[0] if values else ""


def opencitations_doi(value: Any) -> str:
    text = unprefix_opencitations(value)
    matches = re.findall(
        r"(?:doi:)?(10\.\d{4,9}/[^\s;]+)",
        text,
        re.IGNORECASE,
    )
    return normalize_doi(matches[0]) if matches else ""


def opencitations_work(
    doi: str,
    seed: Seed,
    publication_date: str,
    raw_file: str,
) -> dict[str, str]:
    is_seed = doi == seed.doi
    year = publication_date[:4] if re.match(r"^\d{4}", publication_date) else ""
    if is_seed:
        result = seed_work(seed)
        result.update(
            {
                "provider": "opencitations",
                "provider_work_id": doi,
                "publication_date": (
                    publication_date or seed.publication_date
                ),
                "url": f"https://doi.org/{doi}",
                "cutoff_status": cutoff_status(
                    publication_date or seed.publication_date,
                    seed.year,
                ),
                "raw_file": raw_file,
            }
        )
        return result
    return {
        "provider": "opencitations",
        "seed_id": seed.seed_id,
        "screening_record_id": seed.screening_record_id,
        "provider_work_id": doi,
        "work_key": (
            f"doi:{doi}"
            if doi
            else f"unknown:opencitations:{seed.seed_id.lower()}"
        ),
        "title": "",
        "year": year,
        "publication_date": publication_date,
        "authors": "",
        "doi": doi,
        "arxiv_id": "",
        "venue": "",
        "url": f"https://doi.org/{doi}" if doi else "",
        "citation_count": "",
        "reference_count": "",
        "cutoff_status": cutoff_status(publication_date, year),
        "raw_file": raw_file,
    }


def query_opencitations(
    seed: Seed,
    run_dir: Path,
    manifest_path: Path,
    works: list[dict[str, str]],
    edges: list[dict[str, str]],
    timeout: float,
    retries: int,
    ceiling: int,
) -> None:
    if not seed.doi:
        reason = "OpenCitations COCI requires a DOI"
        for direction in (
            "references-count",
            "references",
            "citations-count",
            "citations",
        ):
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                skipped_manifest(
                    "opencitations",
                    seed,
                    direction,
                    reason,
                ),
            )
        return

    encoded_doi = urllib.parse.quote(seed.doi, safe="")
    doi_is_version_alias = seed.semantic_scholar_id.upper().startswith(
        "ARXIV:"
    )
    for direction, count_operation in (
        ("references", "reference-count"),
        ("citations", "citation-count"),
    ):
        count_url = (
            f"{OPENCITATIONS_COCI_BASE}/{count_operation}/"
            f"{encoded_doi}"
        )
        count_raw = Path("raw") / (
            f"{seed.seed_id.lower()}-{direction}-"
            "count-opencitations.json.gz"
        )
        count_entry = manifest_template(
            "opencitations",
            seed,
            f"{direction}-count",
            0,
            "",
            count_url,
        )
        count_document, count_entry = fetch_json(
            run_dir,
            count_raw,
            count_entry,
            timeout,
            retries,
        )
        expected_count: int | None = None
        if (
            isinstance(count_document, list)
            and len(count_document) == 1
            and isinstance(count_document[0], dict)
            and clean_text(count_document[0].get("count")).isdigit()
        ):
            expected_count = int(
                clean_text(count_document[0].get("count"))
            )
            count_entry.update(
                {
                    "identity_status": "verified-primary",
                    "total_results": str(expected_count),
                    "returned_results": "1",
                    "retained_results": "1",
                    "cumulative_results": "1",
                    "truncated": "no",
                    "pagination_complete": "yes",
                }
            )
        elif count_document is not None:
            count_entry["operation_status"] = "success-with-limitations"
            count_entry["coverage_note"] = (
                "OpenCitations count response was not a singleton "
                "numeric count"
            )
            count_entry["truncated"] = "unknown"
            count_entry["pagination_complete"] = "no"
        append_csv_row(
            manifest_path,
            MANIFEST_FIELDS,
            count_entry,
        )
        time.sleep(OPENCITATIONS_DELAY_SECONDS)

        url = (
            f"{OPENCITATIONS_COCI_BASE}/{direction}/{encoded_doi}"
        )
        raw_relative = Path("raw") / (
            f"{seed.seed_id.lower()}-{direction}-"
            "p0001-opencitations.json.gz"
        )
        entry = manifest_template(
            "opencitations",
            seed,
            direction,
            0,
            "",
            url,
        )
        document, entry = fetch_json(
            run_dir,
            raw_relative,
            entry,
            timeout,
            retries,
        )
        if document is None:
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                entry,
            )
            continue
        if not isinstance(document, list):
            entry["error"] = (
                "ValueError: OpenCitations response is not a JSON array"
            )
            entry["operation_status"] = "failed"
            append_csv_row(
                manifest_path,
                MANIFEST_FIELDS,
                entry,
            )
            continue

        retained = document[:ceiling]
        returned_count = len(document)
        coverage_notes: list[str] = []
        if expected_count is None:
            truncated = "unknown"
            pagination_complete = "no"
            coverage_notes.append(
                "OpenCitations relation count could not be verified"
            )
        elif expected_count > ceiling:
            truncated = "yes"
            pagination_complete = "no"
            coverage_notes.append(
                f"provider count {expected_count} exceeds local ceiling "
                f"{ceiling}"
            )
        elif returned_count == expected_count:
            truncated = "no"
            pagination_complete = "yes"
        else:
            truncated = "unknown"
            pagination_complete = "no"
            coverage_notes.append(
                "OpenCitations returned row count does not match count "
                f"endpoint ({returned_count} != {expected_count})"
            )
        if doi_is_version_alias:
            coverage_notes.append(
                "The DOI is a version alias; the cutoff-eligible seed "
                "version is addressed by arXiv in Semantic Scholar"
            )
        entry.update(
            {
                "identity_status": "verified-primary",
                "total_results": (
                    str(expected_count)
                    if expected_count is not None
                    else ""
                ),
                "returned_results": str(returned_count),
                "retained_results": str(len(retained)),
                "cumulative_results": str(len(retained)),
                "truncated": truncated,
                "pagination_complete": pagination_complete,
                "coverage_note": "; ".join(coverage_notes),
            }
        )
        normalization_errors = 0
        anchor_errors = 0
        for index, relation in enumerate(retained):
            if not isinstance(relation, dict):
                normalization_errors += 1
                continue
            source_doi = opencitations_doi(relation.get("citing"))
            target_doi = opencitations_doi(relation.get("cited"))
            if (
                not DOI_RE.fullmatch(source_doi)
                or not DOI_RE.fullmatch(target_doi)
            ):
                normalization_errors += 1
                continue
            anchored = (
                source_doi == seed.doi
                if direction == "references"
                else target_doi == seed.doi
            )
            if not anchored:
                anchor_errors += 1
                continue
            creation = unprefix_opencitations(
                relation.get("creation")
            )
            source = opencitations_work(
                source_doi,
                seed,
                creation,
                entry["raw_file"],
            )
            target = opencitations_work(
                target_doi,
                seed,
                "",
                entry["raw_file"],
            )
            works.extend((source, target))
            edges.append(
                edge_row(
                    "opencitations",
                    seed,
                    direction,
                    source,
                    target,
                    unprefix_opencitations(
                        relation.get("oci") or relation.get("id")
                    ),
                    creation,
                    entry["raw_file"],
                )
            )
        if normalization_errors:
            entry["normalization_error_count"] = str(
                normalization_errors
            )
            entry["coverage_note"] = "; ".join(
                part
                for part in (
                    entry["coverage_note"],
                    f"{normalization_errors} rows lacked a valid DOI pair",
                )
                if part
            )
        if anchor_errors:
            entry["identity_status"] = "mismatch"
            entry["coverage_note"] = "; ".join(
                part
                for part in (
                    entry["coverage_note"],
                    f"{anchor_errors} rows did not anchor to the seed DOI",
                )
                if part
            )
        if entry["coverage_note"]:
            entry["operation_status"] = "success-with-limitations"
        append_csv_row(
            manifest_path,
            MANIFEST_FIELDS,
            entry,
        )
        time.sleep(OPENCITATIONS_DELAY_SECONDS)


def best_text(rows: list[dict[str, str]], field: str) -> str:
    values = [row[field] for row in rows if row.get(field)]
    return max(values, key=len) if values else ""


def best_date(rows: list[dict[str, str]], field: str) -> str:
    values = [row[field] for row in rows if row.get(field)]
    return max(values, key=lambda value: (len(value), value)) if values else ""


def max_integer(rows: list[dict[str, str]], field: str) -> str:
    values = [
        int(row[field])
        for row in rows
        if row.get(field, "").isdigit()
    ]
    return str(max(values)) if values else ""


def join_unique(rows: list[dict[str, str]], field: str) -> str:
    return ";".join(sorted({row[field] for row in rows if row.get(field)}))


def merge_cutoff_status(statuses: set[str]) -> str:
    known = statuses - {"unknown-date"}
    if known == {"included", "excluded-after-cutoff"}:
        return "conflict"
    if "excluded-after-cutoff" in known:
        return "excluded-after-cutoff"
    if "included" in known:
        return "included"
    return "unknown-date"


def deduplicate_works(
    works: list[dict[str, str]],
) -> list[dict[str, str]]:
    groups: dict[str, list[dict[str, str]]] = {}
    for work in works:
        groups.setdefault(work["work_key"], []).append(work)
    result: list[dict[str, str]] = []
    for key, rows in groups.items():
        statuses = {row["cutoff_status"] for row in rows}
        result.append(
            {
                "work_key": key,
                "title": best_text(rows, "title"),
                "year": best_date(rows, "year"),
                "publication_date": best_date(
                    rows,
                    "publication_date",
                ),
                "authors": best_text(rows, "authors"),
                "doi": best_text(rows, "doi"),
                "arxiv_id": best_text(rows, "arxiv_id"),
                "venue": best_text(rows, "venue"),
                "url": best_text(rows, "url"),
                "citation_count": max_integer(
                    rows,
                    "citation_count",
                ),
                "reference_count": max_integer(
                    rows,
                    "reference_count",
                ),
                "providers": join_unique(rows, "provider"),
                "provider_work_ids": join_unique(
                    rows,
                    "provider_work_id",
                ),
                "seed_ids": join_unique(rows, "seed_id"),
                "screening_record_ids": join_unique(
                    rows,
                    "screening_record_id",
                ),
                "cutoff_status": merge_cutoff_status(statuses),
                "cutoff_statuses": ";".join(sorted(statuses)),
            }
        )
    return sorted(result, key=lambda row: row["work_key"])


def deduplicate_edges(
    edges: list[dict[str, str]],
) -> list[dict[str, str]]:
    groups: dict[str, list[dict[str, str]]] = {}
    for edge in edges:
        groups.setdefault(edge["edge_key"], []).append(edge)
    result: list[dict[str, str]] = []
    for key, rows in groups.items():
        statuses = {row["cutoff_status"] for row in rows}
        result.append(
            {
                "edge_key": key,
                "source_work_key": best_text(
                    rows,
                    "source_work_key",
                ),
                "target_work_key": best_text(
                    rows,
                    "target_work_key",
                ),
                "source_doi": best_text(rows, "source_doi"),
                "target_doi": best_text(rows, "target_doi"),
                "providers": join_unique(rows, "provider"),
                "seed_ids": join_unique(rows, "seed_id"),
                "screening_record_ids": join_unique(
                    rows,
                    "screening_record_id",
                ),
                "directions": join_unique(rows, "direction"),
                "provider_edge_ids": join_unique(
                    rows,
                    "provider_edge_id",
                ),
                "citing_publication_date": best_date(
                    rows,
                    "citing_publication_date",
                ),
                "cutoff_status": merge_cutoff_status(statuses),
                "cutoff_statuses": ";".join(sorted(statuses)),
            }
        )
    return sorted(result, key=lambda row: row["edge_key"])


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_checksum_manifest(run_dir: Path) -> tuple[Path, str]:
    manifest_path = run_dir / "checksums.csv"
    rows = []
    for path in sorted(run_dir.rglob("*")):
        if not path.is_file() or path == manifest_path:
            continue
        rows.append(
            {
                "path": str(path.relative_to(run_dir)),
                "sha256": sha256_file(path),
                "bytes": str(path.stat().st_size),
            }
        )
    write_csv(
        manifest_path,
        ("path", "sha256", "bytes"),
        rows,
    )
    return manifest_path, sha256_file(manifest_path)


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--seeds",
        type=Path,
        default=audit_dir / "citation-seeds.csv",
        help="explicit citation seed catalogue",
    )
    parser.add_argument(
        "--screening",
        type=Path,
        default=audit_dir / "screening.csv",
        help="screening ledger used to detect a stale seed catalogue",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=audit_dir / "data" / "citation-runs",
        help="root under which a new timestamped run is created",
    )
    parser.add_argument(
        "--run-id",
        default=default_run_id(),
        help=(
            "new timestamped directory name; defaults to current UTC "
            "(YYYYMMDDTHHMMSSZ)"
        ),
    )
    parser.add_argument(
        "--providers",
        nargs="+",
        choices=sorted(PROVIDERS),
        default=list(DEFAULT_PROVIDERS),
        help="citation indexes to query",
    )
    parser.add_argument(
        "--seed-ids",
        nargs="+",
        help="optional subset of seed IDs",
    )
    parser.add_argument(
        "--max-records-per-seed-direction",
        type=int,
        default=5000,
        help="transparent local normalization ceiling",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="HTTP timeout in seconds",
    )
    parser.add_argument(
        "--retries",
        type=int,
        default=3,
        help="retries for rate limits, server failures, and network errors",
    )
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="validate catalogue and screening agreement without a run",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    if not RUN_ID_RE.fullmatch(arguments.run_id):
        raise ValueError(
            "--run-id must begin with an immutable UTC timestamp in "
            "YYYYMMDDTHHMMSSZ form"
        )
    if arguments.max_records_per_seed_direction < 1:
        raise ValueError(
            "--max-records-per-seed-direction must be positive"
        )
    if arguments.timeout <= 0:
        raise ValueError("--timeout must be positive")
    if arguments.retries < 0:
        raise ValueError("--retries must be nonnegative")

    seeds_path = arguments.seeds.resolve()
    screening_path = arguments.screening.resolve()
    script_path = Path(__file__).resolve()
    seeds_payload = seeds_path.read_bytes()
    screening_payload = screening_path.read_bytes()
    script_payload = script_path.read_bytes()
    seeds = read_seeds(seeds_path, seeds_payload)
    cross_check_screening(
        seeds,
        screening_path,
        screening_payload,
    )

    if arguments.seed_ids:
        requested = set(arguments.seed_ids)
        known = {seed.seed_id for seed in seeds}
        unknown = requested - known
        if unknown:
            raise ValueError(f"unknown seed IDs: {sorted(unknown)}")
        seeds = [seed for seed in seeds if seed.seed_id in requested]
    if not seeds:
        raise ValueError("no seeds remain after filtering")

    providers = list(dict.fromkeys(arguments.providers))
    if arguments.validate_only:
        print(f"seeds: {len(seeds)}")
        print(f"with DOI: {sum(bool(seed.doi) for seed in seeds)}")
        print(
            "Semantic Scholar addressable: "
            f"{sum(bool(seed.semantic_scholar_id) for seed in seeds)}"
        )
        print(
            "OpenCitations addressable: "
            f"{sum(bool(seed.doi) for seed in seeds)}"
        )
        print(f"providers: {','.join(providers)}")
        print(f"publication cutoff: {PUBLICATION_CUTOFF}")
        return 0

    output_root = arguments.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    run_dir = output_root / arguments.run_id
    run_dir.mkdir(exist_ok=False)
    (run_dir / "raw").mkdir()
    inputs_dir = run_dir / "inputs"
    inputs_dir.mkdir()
    for filename, payload in (
        ("citation-seeds.csv", seeds_payload),
        ("screening.csv", screening_payload),
        ("search_citation_graphs.py", script_payload),
    ):
        with (inputs_dir / filename).open("xb") as handle:
            handle.write(payload)

    started_at = utc_now()
    seed_digest = sha256_bytes(seeds_payload)
    screening_digest = sha256_bytes(screening_payload)
    script_digest = sha256_bytes(script_payload)
    write_json(
        run_dir / "run-start.json",
        {
            "status": "started",
            "script_version": SCRIPT_VERSION,
            "script_sha256": script_digest,
            "repository_commit": git_commit(script_dir := script_path.parent),
            "started_at_utc": started_at,
            "citation_seeds_file": str(seeds_path),
            "citation_seeds_sha256": seed_digest,
            "screening_file": str(screening_path),
            "screening_sha256": screening_digest,
            "input_snapshots": {
                "citation_seeds": "inputs/citation-seeds.csv",
                "screening": "inputs/screening.csv",
                "script": "inputs/search_citation_graphs.py",
            },
            "providers": providers,
            "seed_ids": [seed.seed_id for seed in seeds],
            "seed_count": len(seeds),
            "publication_cutoff": PUBLICATION_CUTOFF,
            "max_records_per_seed_direction": (
                arguments.max_records_per_seed_direction
            ),
            "credentials_present": {
                "semantic_scholar_api_key": bool(
                    os.environ.get("SEMANTIC_SCHOLAR_API_KEY")
                ),
                "opencitations_access_token": bool(
                    os.environ.get("OPENCITATIONS_ACCESS_TOKEN")
                ),
            },
        },
    )

    manifest_path = run_dir / "manifest.csv"
    works: list[dict[str, str]] = [seed_work(seed) for seed in seeds]
    edges: list[dict[str, str]] = []
    for seed in seeds:
        for provider in providers:
            if provider == "semanticscholar":
                query_semantic_scholar(
                    seed,
                    run_dir,
                    manifest_path,
                    works,
                    edges,
                    arguments.timeout,
                    arguments.retries,
                    arguments.max_records_per_seed_direction,
                )
            elif provider == "opencitations":
                query_opencitations(
                    seed,
                    run_dir,
                    manifest_path,
                    works,
                    edges,
                    arguments.timeout,
                    arguments.retries,
                    arguments.max_records_per_seed_direction,
                )

    deduplicated_works = deduplicate_works(works)
    deduplicated_edges = deduplicate_edges(edges)
    write_csv(run_dir / "works.csv", WORK_FIELDS, works)
    write_csv(run_dir / "edges.csv", EDGE_FIELDS, edges)
    write_csv(
        run_dir / "deduplicated-works.csv",
        DEDUP_WORK_FIELDS,
        deduplicated_works,
    )
    write_csv(
        run_dir / "deduplicated-edges.csv",
        DEDUP_EDGE_FIELDS,
        deduplicated_edges,
    )

    with manifest_path.open(newline="", encoding="utf-8") as handle:
        manifest = list(csv.DictReader(handle))
    failures = [
        row
        for row in manifest
        if row["operation_status"] == "failed"
        or (
            row["error"]
            and not row["error"].startswith("SKIPPED:")
        )
    ]
    skipped = [
        row
        for row in manifest
        if row["operation_status"] == "skipped"
    ]
    limited_rows = [
        row
        for row in manifest
        if row["operation_status"] == "success-with-limitations"
        or bool(row["coverage_note"])
        or row["identity_status"] in {"title-only", "mismatch"}
        or (
            row["direction"]
            in {
                "references",
                "citations",
                "references-count",
                "citations-count",
            }
            and row["operation_status"] != "skipped"
            and (
                row["truncated"] != "no"
                or row["pagination_complete"] != "yes"
            )
        )
    ]
    unresolved_cutoff_edges = [
        row["edge_key"]
        for row in deduplicated_edges
        if "citations" in row["directions"].split(";")
        and row["cutoff_status"] in {"unknown-date", "conflict"}
    ]
    version_alias_seed_ids = [
        seed.seed_id
        for seed in seeds
        if seed.doi and seed.arxiv_id
    ]
    request_status = "incomplete" if failures else "complete"
    coverage_complete = not (
        failures
        or skipped
        or limited_rows
        or unresolved_cutoff_edges
        or version_alias_seed_ids
    )
    coverage_status = "complete" if coverage_complete else "incomplete"
    if failures:
        run_status = "incomplete-with-errors"
    elif coverage_complete:
        run_status = "complete"
    else:
        run_status = "complete-with-coverage-limitations"
    finished_at = utc_now()
    write_json(
        run_dir / "run.json",
        {
            "status": run_status,
            "request_status": request_status,
            "coverage_status": coverage_status,
            "script_version": SCRIPT_VERSION,
            "script_sha256": script_digest,
            "repository_commit": git_commit(script_dir),
            "started_at_utc": started_at,
            "finished_at_utc": finished_at,
            "citation_seeds_file": str(seeds_path),
            "citation_seeds_sha256": seed_digest,
            "screening_file": str(screening_path),
            "screening_sha256": screening_digest,
            "providers": providers,
            "seed_ids": [seed.seed_id for seed in seeds],
            "seed_count": len(seeds),
            "publication_cutoff": PUBLICATION_CUTOFF,
            "max_records_per_seed_direction": (
                arguments.max_records_per_seed_direction
            ),
            "request_count": len(
                [row for row in manifest if row["requested_url"]]
            ),
            "successful_request_count": len(
                [
                    row
                    for row in manifest
                    if row["operation_status"].startswith("success")
                ]
            ),
            "failed_request_or_normalization_count": len(failures),
            "skipped_operation_count": len(skipped),
            "coverage_limited_manifest_row_count": len(limited_rows),
            "unresolved_forward_cutoff_edge_count": len(
                unresolved_cutoff_edges
            ),
            "unresolved_forward_cutoff_edge_sample": (
                unresolved_cutoff_edges[:50]
            ),
            "version_alias_seed_ids_requiring_manual_reconciliation": (
                version_alias_seed_ids
            ),
            "normalized_work_occurrence_count": len(works),
            "normalized_edge_occurrence_count": len(edges),
            "deduplicated_work_count": len(deduplicated_works),
            "deduplicated_edge_count": len(deduplicated_edges),
            "cutoff_edge_counts": {
                status: sum(
                    row["cutoff_status"] == status
                    for row in deduplicated_edges
                )
                for status in (
                    "included",
                    "excluded-after-cutoff",
                    "unknown-date",
                    "conflict",
                )
            },
            "user_agent": USER_AGENT,
            "coverage_notes": {
                "semantic_scholar": (
                    "The Academic Graph API is a mutable provider snapshot. "
                    "An API key is read from SEMANTIC_SCHOLAR_API_KEY when "
                    "present but is never persisted. Relation pagination is "
                    "followed until the provider omits next, an error occurs, "
                    "or the recorded local ceiling is hit."
                ),
                "opencitations": (
                    "The unified OpenCitations Index v1 API is queried. An "
                    "authorization token is read from "
                    "OPENCITATIONS_ACCESS_TOKEN when present but is never "
                    "persisted. Citation/reference counts are fetched and "
                    "must match returned relation rows before pagination is "
                    "treated as complete."
                ),
                "publication_cutoff": (
                    "Raw payloads are never discarded. Normalized works and "
                    "edges carry included, excluded-after-cutoff, or "
                    "unknown-date status. Every 2026 seed has an exact "
                    "eligible-version date, while citing works with "
                    "insufficient dates remain explicit coverage limits."
                ),
                "identity_and_versions": (
                    "Seed metadata is checked against requested identifiers "
                    "and normalized titles, arXiv version suffixes are "
                    "collapsed, and 10.48550/arXiv aliases map to arXiv keys. "
                    "Seeds carrying both a publication DOI and an arXiv ID "
                    "still require manual version reconciliation before a "
                    "snowballing wave can be called complete."
                ),
                "interpretation": (
                    "Index absence is not evidence of nonexistence; citation "
                    "graphs complement, but do not replace, database queries, "
                    "full-text screening, artifact inspection, and expert "
                    "review."
                ),
            },
        },
    )
    checksum_path, checksum_digest = write_checksum_manifest(run_dir)

    print(f"run: {run_dir}")
    print(f"status: {run_status}")
    print(f"request status: {request_status}")
    print(f"coverage status: {coverage_status}")
    print(f"manifest rows: {len(manifest)}")
    print(f"failures: {len(failures)}")
    print(f"skipped operations: {len(skipped)}")
    print(f"normalized edges: {len(edges)}")
    print(f"deduplicated edges: {len(deduplicated_edges)}")
    print(
        "checksum manifest: "
        f"{checksum_path} sha256={checksum_digest}"
    )
    return 0 if run_status == "complete" else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
