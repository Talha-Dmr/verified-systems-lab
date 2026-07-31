#!/usr/bin/env python3
"""Run a dated, reproducible search across open scholarly indexes.

The script intentionally uses only Python's standard library. It preserves
provider responses, a request manifest, normalized per-hit records, and a
cross-provider deduplicated view. Human screening and publisher full-text
searches remain separate steps in protocol.md.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import html
import http.client
import json
import os
import re
import shutil
import subprocess
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable


SCRIPT_VERSION = "3"
PUBLICATION_CUTOFF = "2026-07-31"
ARXIV_SUBMISSION_CUTOFF = "202607312359"
USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
DEFAULT_PROVIDERS = ("dblp", "openalex", "crossref", "semanticscholar", "arxiv")
JSON_PROVIDERS = {"dblp", "openalex", "crossref", "semanticscholar"}
REQUIRED_API_KEYS = {
    "openalex": (
        "OPENALEX_API_KEY",
        "the official OpenAlex search endpoint",
    ),
    "semanticscholar": (
        "SEMANTIC_SCHOLAR_API_KEY",
        "the official Semantic Scholar bulk-search endpoint",
    ),
}

MANIFEST_FIELDS = (
    "provider",
    "query_id",
    "family_id",
    "query_text",
    "provider_query",
    "page_index",
    "cursor_in",
    "cursor_out",
    "requested_url",
    "retrieved_at_utc",
    "http_status",
    "response_date",
    "response_etag",
    "rate_limit_remaining",
    "total_results",
    "returned_results",
    "cumulative_results",
    "raw_file",
    "raw_sha256",
    "truncated",
    "error",
)

RECORD_FIELDS = (
    "provider",
    "query_id",
    "provider_record_id",
    "title",
    "year",
    "authors",
    "doi",
    "arxiv_id",
    "venue",
    "record_type",
    "url",
    "cited_by_count",
    "abstract",
    "canonical_key",
)

DEDUP_FIELDS = (
    "canonical_key",
    "title",
    "year",
    "authors",
    "doi",
    "arxiv_id",
    "venue",
    "record_type",
    "url",
    "cited_by_count",
    "providers",
    "query_ids",
    "provider_record_ids",
)


@dataclass(frozen=True)
class Query:
    query_id: str
    family_id: str
    provider: str
    query_text: str
    purpose: str


@dataclass(frozen=True)
class ProviderSpec:
    name: str
    parse: Callable[[bytes, str], tuple[int | None, list[dict[str, str]]]]
    suffix: str
    minimum_delay_seconds: float
    maximum_page_size: int


@dataclass(frozen=True)
class RequestSpec:
    provider_query: str
    url: str
    redacted_url: str
    headers: dict[str, str]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def clean_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, (list, tuple)):
        value = " ".join(clean_text(item) for item in value if item is not None)
    elif isinstance(value, dict):
        value = value.get("text") or value.get("#text") or ""
    value = html.unescape(str(value))
    value = re.sub(r"<[^>]+>", " ", value)
    value = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def normalize_doi(value: Any) -> str:
    doi = clean_text(value).lower()
    for prefix in ("https://doi.org/", "http://doi.org/", "doi:"):
        if doi.startswith(prefix):
            doi = doi[len(prefix) :]
    return doi.strip()


def normalize_title(value: Any) -> str:
    text = unicodedata.normalize("NFKD", clean_text(value)).casefold()
    text = "".join(character for character in text if not unicodedata.combining(character))
    return re.sub(r"[^a-z0-9]+", " ", text).strip()


def canonical_key(record: dict[str, str]) -> str:
    if record.get("doi"):
        return f"doi:{record['doi']}"
    if record.get("arxiv_id"):
        return f"arxiv:{record['arxiv_id'].lower()}"
    normalized = normalize_title(record.get("title", ""))
    year = record.get("year", "")
    if normalized:
        return f"title:{normalized}|year:{year}"
    return (
        f"provider:{record.get('provider', '')}:"
        f"{record.get('provider_record_id', '')}"
    )


def first_nonempty(*values: Any) -> str:
    for value in values:
        text = clean_text(value)
        if text:
            return text
    return ""


def join_people(value: Any) -> str:
    if not value:
        return ""
    people = value if isinstance(value, list) else [value]
    names: list[str] = []
    for person in people:
        if isinstance(person, str):
            name = clean_text(person)
        elif isinstance(person, dict):
            name = first_nonempty(
                person.get("text"),
                person.get("#text"),
                " ".join(
                    part
                    for part in (
                        clean_text(person.get("given")),
                        clean_text(person.get("family")),
                    )
                    if part
                ),
                person.get("name"),
            )
        else:
            name = clean_text(person)
        if name:
            names.append(name)
    return "; ".join(names)


def nested_first(value: Any) -> Any:
    while isinstance(value, list) and value:
        value = value[0]
    return value


def extract_crossref_year(item: dict[str, Any]) -> str:
    for field in ("published-print", "published-online", "published", "issued", "created"):
        date_value = item.get(field)
        if not isinstance(date_value, dict):
            continue
        parts = date_value.get("date-parts")
        first = nested_first(parts)
        first = nested_first(first)
        if isinstance(first, int):
            return str(first)
        if isinstance(first, str) and first.isdigit():
            return first
    return ""


def reconstruct_openalex_abstract(index: Any) -> str:
    if not isinstance(index, dict):
        return ""
    positions: list[tuple[int, str]] = []
    for word, offsets in index.items():
        if not isinstance(offsets, list):
            continue
        for offset in offsets:
            if isinstance(offset, int):
                positions.append((offset, clean_text(word)))
    positions.sort()
    return clean_text(" ".join(word for _, word in positions))


def request_bytes(
    url: str,
    timeout: float,
    retries: int,
    extra_headers: dict[str, str] | None = None,
) -> tuple[bytes, int, dict[str, str]]:
    headers = {
        "Accept": "application/json, application/atom+xml, application/xml;q=0.9",
        "User-Agent": USER_AGENT,
    }
    headers.update(extra_headers or {})
    request = urllib.request.Request(
        url,
        headers=headers,
    )
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                response_headers = {
                    "date": clean_text(response.headers.get("Date")),
                    "etag": clean_text(response.headers.get("ETag")),
                    "rate_limit_remaining": first_nonempty(
                        response.headers.get("x-ratelimit-remaining"),
                        response.headers.get("x-rate-limit-remaining"),
                    ),
                }
                return response.read(), int(response.status), response_headers
        except urllib.error.HTTPError as error:
            retryable = error.code == 429 or 500 <= error.code < 600
            if not retryable or attempt == retries:
                raise
            retry_after = error.headers.get("Retry-After")
            delay = float(retry_after) if retry_after and retry_after.isdigit() else 2**attempt
            time.sleep(min(60.0, max(1.0, delay)))
        except (
            urllib.error.URLError,
            TimeoutError,
            ConnectionResetError,
            http.client.RemoteDisconnected,
        ):
            if attempt == retries:
                raise
            time.sleep(2**attempt)
    raise RuntimeError("unreachable request retry state")


def build_dblp_request(query: str, limit: int, cursor: str) -> RequestSpec:
    parameters = urllib.parse.urlencode(
        {"q": query, "h": str(limit), "f": cursor or "0", "c": "0", "format": "json"}
    )
    url = f"https://dblp.org/search/publ/api?{parameters}"
    return RequestSpec(query, url, url, {})


def parse_dblp(payload: bytes, query_id: str) -> tuple[int | None, list[dict[str, str]]]:
    document = json.loads(payload)
    hits = document.get("result", {}).get("hits", {})
    total_text = clean_text(hits.get("@total"))
    total = int(total_text) if total_text.isdigit() else None
    raw_hits = hits.get("hit", [])
    if isinstance(raw_hits, dict):
        raw_hits = [raw_hits]
    records: list[dict[str, str]] = []
    for hit in raw_hits:
        info = hit.get("info", {}) if isinstance(hit, dict) else {}
        authors_value = info.get("authors", {}).get("author", [])
        record = {
            "provider": "dblp",
            "query_id": query_id,
            "provider_record_id": clean_text(hit.get("@id") if isinstance(hit, dict) else ""),
            "title": clean_text(info.get("title")),
            "year": clean_text(info.get("year")),
            "authors": join_people(authors_value),
            "doi": normalize_doi(info.get("doi")),
            "arxiv_id": "",
            "venue": first_nonempty(info.get("venue"), info.get("booktitle"), info.get("journal")),
            "record_type": clean_text(info.get("type")),
            "url": first_nonempty(info.get("ee"), info.get("url")),
            "cited_by_count": "",
            "abstract": "",
        }
        record["canonical_key"] = canonical_key(record)
        records.append(record)
    return total, records


def build_openalex_request(query: str, limit: int, cursor: str) -> RequestSpec:
    parameters = {
        "search": query,
        "filter": f"to_publication_date:{PUBLICATION_CUTOFF}",
        "per_page": str(limit),
        "cursor": cursor or "*",
    }
    api_key = os.environ.get("OPENALEX_API_KEY", "").strip()
    public_parameters = dict(parameters)
    if api_key:
        parameters["api_key"] = api_key
        public_parameters["api_key"] = "<redacted>"
    url = f"https://api.openalex.org/works?{urllib.parse.urlencode(parameters)}"
    redacted = (
        "https://api.openalex.org/works?"
        f"{urllib.parse.urlencode(public_parameters)}"
    )
    return RequestSpec(query, url, redacted, {})


def parse_openalex(
    payload: bytes, query_id: str
) -> tuple[int | None, list[dict[str, str]]]:
    document = json.loads(payload)
    count = document.get("meta", {}).get("count")
    total = count if isinstance(count, int) else None
    records: list[dict[str, str]] = []
    for item in document.get("results", []):
        authorships = item.get("authorships", [])
        authors = [
            authorship.get("author", {}).get("display_name", "")
            for authorship in authorships
            if isinstance(authorship, dict)
        ]
        ids = item.get("ids") or {}
        arxiv_url = clean_text(ids.get("arxiv"))
        arxiv_id = arxiv_url.rsplit("/", 1)[-1] if arxiv_url else ""
        location = item.get("primary_location") or {}
        source = location.get("source") or {}
        record = {
            "provider": "openalex",
            "query_id": query_id,
            "provider_record_id": clean_text(item.get("id")),
            "title": first_nonempty(item.get("display_name"), item.get("title")),
            "year": clean_text(item.get("publication_year")),
            "authors": join_people(authors),
            "doi": normalize_doi(item.get("doi")),
            "arxiv_id": arxiv_id,
            "venue": clean_text(source.get("display_name")),
            "record_type": clean_text(item.get("type")),
            "url": first_nonempty(location.get("landing_page_url"), item.get("id")),
            "cited_by_count": clean_text(item.get("cited_by_count")),
            "abstract": reconstruct_openalex_abstract(item.get("abstract_inverted_index")),
        }
        record["canonical_key"] = canonical_key(record)
        records.append(record)
    return total, records


def build_crossref_request(query: str, limit: int, cursor: str) -> RequestSpec:
    parameters = {
        "query.bibliographic": query,
        "filter": f"until-pub-date:{PUBLICATION_CUTOFF}",
        "rows": str(limit),
        "sort": "relevance",
        "order": "desc",
        "select": "DOI,title,author,published,type,URL,is-referenced-by-count",
    }
    mailto = os.environ.get("CROSSREF_MAILTO", "").strip()
    public_parameters = dict(parameters)
    if mailto:
        parameters["mailto"] = mailto
        public_parameters["mailto"] = "<redacted>"
    url = f"https://api.crossref.org/works?{urllib.parse.urlencode(parameters)}"
    redacted = (
        "https://api.crossref.org/works?"
        f"{urllib.parse.urlencode(public_parameters)}"
    )
    return RequestSpec(query, url, redacted, {})


def parse_crossref(
    payload: bytes, query_id: str
) -> tuple[int | None, list[dict[str, str]]]:
    document = json.loads(payload)
    message = document.get("message", {})
    count = message.get("total-results")
    total = count if isinstance(count, int) else None
    records: list[dict[str, str]] = []
    for item in message.get("items", []):
        record = {
            "provider": "crossref",
            "query_id": query_id,
            "provider_record_id": clean_text(item.get("DOI")),
            "title": clean_text(item.get("title")),
            "year": extract_crossref_year(item),
            "authors": join_people(item.get("author", [])),
            "doi": normalize_doi(item.get("DOI")),
            "arxiv_id": "",
            "venue": clean_text(item.get("container-title")),
            "record_type": clean_text(item.get("type")),
            "url": clean_text(item.get("URL")),
            "cited_by_count": clean_text(item.get("is-referenced-by-count")),
            "abstract": clean_text(item.get("abstract")),
        }
        record["canonical_key"] = canonical_key(record)
        records.append(record)
    return total, records


def build_semantic_scholar_request(
    query: str, limit: int, cursor: str
) -> RequestSpec:
    fields = (
        "paperId,corpusId,externalIds,title,abstract,year,publicationDate,"
        "authors,venue,url,citationCount,referenceCount,publicationTypes"
    )
    parameters = {
        "query": query,
        "publicationDateOrYear": f":{PUBLICATION_CUTOFF}",
        "fields": fields,
        "sort": "paperId:asc",
    }
    if cursor:
        parameters["token"] = cursor
    url = (
        "https://api.semanticscholar.org/graph/v1/paper/search/bulk?"
        f"{urllib.parse.urlencode(parameters)}"
    )
    api_key = os.environ.get("SEMANTIC_SCHOLAR_API_KEY", "").strip()
    headers = {"x-api-key": api_key} if api_key else {}
    return RequestSpec(query, url, url, headers)


def parse_semantic_scholar(
    payload: bytes, query_id: str
) -> tuple[int | None, list[dict[str, str]]]:
    document = json.loads(payload)
    count = document.get("total")
    total = count if isinstance(count, int) else None
    records: list[dict[str, str]] = []
    for item in document.get("data", []):
        external = item.get("externalIds") or {}
        publication_types = item.get("publicationTypes") or []
        record = {
            "provider": "semanticscholar",
            "query_id": query_id,
            "provider_record_id": clean_text(item.get("paperId")),
            "title": clean_text(item.get("title")),
            "year": clean_text(item.get("year")),
            "authors": join_people(item.get("authors", [])),
            "doi": normalize_doi(external.get("DOI")),
            "arxiv_id": clean_text(external.get("ArXiv")),
            "venue": clean_text(item.get("venue")),
            "record_type": "; ".join(clean_text(value) for value in publication_types),
            "url": clean_text(item.get("url")),
            "cited_by_count": clean_text(item.get("citationCount")),
            "abstract": clean_text(item.get("abstract")),
        }
        record["canonical_key"] = canonical_key(record)
        records.append(record)
    return total, records


def build_arxiv_request(query: str, limit: int, cursor: str) -> RequestSpec:
    provider_query = (
        f"({query}) AND submittedDate:[199101010000 TO {ARXIV_SUBMISSION_CUTOFF}]"
    )
    parameters = urllib.parse.urlencode(
        {
            "search_query": provider_query,
            "start": cursor or "0",
            "max_results": str(limit),
            "sortBy": "submittedDate",
            "sortOrder": "descending",
        }
    )
    url = f"https://export.arxiv.org/api/query?{parameters}"
    return RequestSpec(provider_query, url, url, {})


def parse_arxiv(payload: bytes, query_id: str) -> tuple[int | None, list[dict[str, str]]]:
    root = ET.fromstring(payload)
    atom = "{http://www.w3.org/2005/Atom}"
    open_search = "{http://a9.com/-/spec/opensearch/1.1/}"
    total_text = clean_text(root.findtext(f"{open_search}totalResults"))
    total = int(total_text) if total_text.isdigit() else None
    records: list[dict[str, str]] = []
    for entry in root.findall(f"{atom}entry"):
        entry_id = clean_text(entry.findtext(f"{atom}id"))
        arxiv_id = entry_id.rsplit("/", 1)[-1]
        published = clean_text(entry.findtext(f"{atom}published"))
        year = published[:4] if re.match(r"^\d{4}", published) else ""
        authors = [
            clean_text(author.findtext(f"{atom}name"))
            for author in entry.findall(f"{atom}author")
        ]
        doi = ""
        for child in entry:
            if child.tag.endswith("doi"):
                doi = normalize_doi(child.text)
                break
        record = {
            "provider": "arxiv",
            "query_id": query_id,
            "provider_record_id": arxiv_id,
            "title": clean_text(entry.findtext(f"{atom}title")),
            "year": year,
            "authors": join_people(authors),
            "doi": doi,
            "arxiv_id": arxiv_id,
            "venue": "arXiv",
            "record_type": "preprint",
            "url": entry_id,
            "cited_by_count": "",
            "abstract": clean_text(entry.findtext(f"{atom}summary")),
        }
        record["canonical_key"] = canonical_key(record)
        records.append(record)
    return total, records


PROVIDERS = {
    "dblp": ProviderSpec(
        "dblp", parse_dblp, "json", 3.0, 1000
    ),
    "openalex": ProviderSpec(
        "openalex", parse_openalex, "json", 0.2, 100
    ),
    "crossref": ProviderSpec(
        "crossref", parse_crossref, "json", 0.2, 20
    ),
    "semanticscholar": ProviderSpec(
        "semanticscholar",
        parse_semantic_scholar,
        "json",
        3.0,
        1000,
    ),
    "arxiv": ProviderSpec(
        "arxiv", parse_arxiv, "xml", 3.0, 200
    ),
}

REQUEST_BUILDERS = {
    "dblp": build_dblp_request,
    "openalex": build_openalex_request,
    "crossref": build_crossref_request,
    "semanticscholar": build_semantic_scholar_request,
    "arxiv": build_arxiv_request,
}


def read_queries(path: Path) -> list[Query]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        required = {
            "query_id",
            "family_id",
            "provider",
            "query_text",
            "purpose",
        }
        if set(reader.fieldnames or []) != required:
            raise ValueError(
                f"{path} must have exactly these columns: {sorted(required)}"
            )
        queries = [
            Query(
                query_id=clean_text(row["query_id"]),
                family_id=clean_text(row["family_id"]),
                provider=clean_text(row["provider"]).lower(),
                query_text=clean_text(row["query_text"]),
                purpose=clean_text(row["purpose"]),
            )
            for row in reader
        ]
    identifiers = [query.query_id for query in queries]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("query_id values must be unique")
    if any(
        not query.query_id
        or not query.family_id
        or not query.provider
        or not query.query_text
        for query in queries
    ):
        raise ValueError(
            "every query needs nonempty query_id, family_id, provider, and query_text"
        )
    unknown_providers = {query.provider for query in queries} - set(PROVIDERS)
    if unknown_providers:
        raise ValueError(
            f"queries contain unknown providers: {sorted(unknown_providers)}"
        )
    return queries


def write_csv(path: Path, fields: Iterable[str], rows: Iterable[dict[str, Any]]) -> None:
    with path.open("x", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fields), extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def append_csv_row(
    path: Path, fields: Iterable[str], row: dict[str, Any]
) -> None:
    exists = path.exists()
    with path.open("a", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(fields), extrasaction="ignore"
        )
        if not exists:
            writer.writeheader()
        writer.writerow(row)
        handle.flush()


def write_json(path: Path, value: Any) -> None:
    with path.open("x", encoding="utf-8") as handle:
        json.dump(value, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")


def deduplicate(records: list[dict[str, str]]) -> list[dict[str, str]]:
    groups: dict[str, list[dict[str, str]]] = {}
    for record in records:
        groups.setdefault(record["canonical_key"], []).append(record)
    merged: list[dict[str, str]] = []
    for key, group in groups.items():
        def best(field: str) -> str:
            candidates = [record.get(field, "") for record in group]
            candidates = [candidate for candidate in candidates if candidate]
            return max(candidates, key=len) if candidates else ""

        citations = [
            int(record["cited_by_count"])
            for record in group
            if record.get("cited_by_count", "").isdigit()
        ]
        merged.append(
            {
                "canonical_key": key,
                "title": best("title"),
                "year": best("year"),
                "authors": best("authors"),
                "doi": best("doi"),
                "arxiv_id": best("arxiv_id"),
                "venue": best("venue"),
                "record_type": best("record_type"),
                "url": best("url"),
                "cited_by_count": str(max(citations)) if citations else "",
                "providers": ";".join(
                    sorted({record["provider"] for record in group})
                ),
                "query_ids": ";".join(
                    sorted({record["query_id"] for record in group})
                ),
                "provider_record_ids": ";".join(
                    sorted(
                        {
                            f"{record['provider']}:{record['provider_record_id']}"
                            for record in group
                            if record["provider_record_id"]
                        }
                    )
                ),
            }
        )
    return sorted(
        merged,
        key=lambda record: (
            -int(record["cited_by_count"])
            if record["cited_by_count"].isdigit()
            else 0,
            record["year"],
            record["title"].casefold(),
        ),
    )


def payload_sha256(payload: bytes) -> str:
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


def initial_cursor(provider: str) -> str:
    if provider == "openalex":
        return "*"
    if provider == "arxiv":
        return "0"
    return ""


def next_cursor(
    provider: str,
    payload: bytes,
    cursor_in: str,
    returned: int,
    total: int | None,
) -> str:
    if provider == "openalex":
        value = json.loads(payload).get("meta", {}).get("next_cursor")
        return clean_text(value)
    if provider == "semanticscholar":
        return clean_text(json.loads(payload).get("token"))
    if provider == "arxiv":
        start = int(cursor_in or "0")
        next_start = start + returned
        if returned and (total is None or next_start < total):
            return str(next_start)
    return ""


def provider_coverage_is_truncated(
    provider: str,
    cumulative: int,
    total: int | None,
    ceiling: int,
    cursor_out: str,
) -> bool:
    if provider == "crossref":
        return total is not None and total > cumulative
    if provider == "dblp":
        return total is not None and total > cumulative
    if cumulative >= ceiling and (cursor_out or (total is not None and total > cumulative)):
        return True
    return False


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--queries",
        type=Path,
        default=audit_dir / "provider-queries.csv",
        help="provider-specific query catalogue CSV",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=audit_dir / "data" / "runs",
        help="directory under which a new run directory is created",
    )
    parser.add_argument(
        "--run-id",
        default=default_run_id(),
        help="new run directory name; defaults to the current UTC timestamp",
    )
    parser.add_argument(
        "--providers",
        nargs="+",
        choices=sorted(PROVIDERS),
        default=list(DEFAULT_PROVIDERS),
        help="providers to query",
    )
    parser.add_argument(
        "--query-ids",
        nargs="+",
        help="optional subset of query IDs to run",
    )
    parser.add_argument(
        "--max-records-per-query",
        type=int,
        default=2000,
        help="transparent per-query retrieval ceiling",
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
        help="retries for rate limits, server errors, and transient network failures",
    )
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="validate configuration and print counts without creating a run",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    if arguments.max_records_per_query < 1:
        raise ValueError("--max-records-per-query must be positive")
    if arguments.retries < 0:
        raise ValueError("--retries must be nonnegative")

    queries_path = arguments.queries.resolve()
    queries = read_queries(queries_path)
    if arguments.query_ids:
        requested_ids = set(arguments.query_ids)
        known_ids = {query.query_id for query in queries}
        unknown_ids = requested_ids - known_ids
        if unknown_ids:
            raise ValueError(f"unknown query IDs: {sorted(unknown_ids)}")
        queries = [query for query in queries if query.query_id in requested_ids]
    requested_providers = set(arguments.providers)
    queries = [query for query in queries if query.provider in requested_providers]
    if not queries:
        raise ValueError("no queries remain after provider and query-ID filtering")

    if arguments.validate_only:
        counts: dict[str, int] = {}
        for query in queries:
            counts[query.provider] = counts.get(query.provider, 0) + 1
        print(f"queries: {len(queries)}")
        for provider_name in arguments.providers:
            print(f"{provider_name}: {counts.get(provider_name, 0)}")
        return 0

    run_dir = arguments.output_root.resolve() / arguments.run_id
    raw_dir = run_dir / "raw"
    run_dir.mkdir(parents=True, exist_ok=False)
    raw_dir.mkdir()
    shutil.copyfile(queries_path, run_dir / "provider-queries.csv")

    started_at = utc_now()
    query_digest = hashlib.sha256(queries_path.read_bytes()).hexdigest()
    script_digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    repository_commit = git_commit(Path(__file__).resolve().parent)
    write_json(
        run_dir / "run-start.json",
        {
            "status": "started",
            "script_version": SCRIPT_VERSION,
            "script_sha256": script_digest,
            "repository_commit": repository_commit,
            "started_at_utc": started_at,
            "queries_file": str(queries_path),
            "queries_sha256": query_digest,
            "providers": arguments.providers,
            "publication_cutoff": PUBLICATION_CUTOFF,
            "max_records_per_provider_query": (
                arguments.max_records_per_query
            ),
            "query_count": len(queries),
        },
    )
    manifest: list[dict[str, Any]] = []
    records: list[dict[str, str]] = []
    manifest_path = run_dir / "manifest.csv"

    def record_manifest(entry: dict[str, Any]) -> None:
        manifest.append(entry)
        append_csv_row(manifest_path, MANIFEST_FIELDS, entry)

    for provider_name in arguments.providers:
        provider = PROVIDERS[provider_name]
        provider_queries = [
            query for query in queries if query.provider == provider_name
        ]
        for query in provider_queries:
            required_key = REQUIRED_API_KEYS.get(provider_name)
            if required_key and not os.environ.get(required_key[0], "").strip():
                record_manifest(
                    {
                        "provider": provider.name,
                        "query_id": query.query_id,
                        "family_id": query.family_id,
                        "query_text": query.query_text,
                        "provider_query": query.query_text,
                        "page_index": "0",
                        "cursor_in": "",
                        "cursor_out": "",
                        "requested_url": "",
                        "retrieved_at_utc": utc_now(),
                        "http_status": "",
                        "response_date": "",
                        "response_etag": "",
                        "rate_limit_remaining": "",
                        "total_results": "",
                        "returned_results": "0",
                        "cumulative_results": "0",
                        "raw_file": "",
                        "raw_sha256": "",
                        "truncated": "",
                        "error": (
                            f"SKIPPED: {required_key[0]} is not set; "
                            f"{required_key[1]} was not queried"
                        ),
                    }
                )
                continue

            cursor = initial_cursor(provider_name)
            cumulative = 0
            page_index = 0
            while cumulative < arguments.max_records_per_query:
                remaining = arguments.max_records_per_query - cumulative
                page_size = min(provider.maximum_page_size, remaining)
                request_spec = REQUEST_BUILDERS[provider_name](
                    query.query_text, page_size, cursor
                )
                raw_relative = Path("raw") / (
                    f"{query.query_id.lower()}-p{page_index + 1:04d}-"
                    f"{provider.name}.{provider.suffix}.gz"
                )
                raw_path = run_dir / raw_relative
                entry: dict[str, Any] = {
                    "provider": provider.name,
                    "query_id": query.query_id,
                    "family_id": query.family_id,
                    "query_text": query.query_text,
                    "provider_query": request_spec.provider_query,
                    "page_index": str(page_index),
                    "cursor_in": cursor,
                    "cursor_out": "",
                    "requested_url": request_spec.redacted_url,
                    "retrieved_at_utc": "",
                    "http_status": "",
                    "response_date": "",
                    "response_etag": "",
                    "rate_limit_remaining": "",
                    "total_results": "",
                    "returned_results": "0",
                    "cumulative_results": str(cumulative),
                    "raw_file": "",
                    "raw_sha256": "",
                    "truncated": "",
                    "error": "",
                }
                try:
                    payload, status, response_headers = request_bytes(
                        request_spec.url,
                        arguments.timeout,
                        arguments.retries,
                        request_spec.headers,
                    )
                    digest = payload_sha256(payload)
                    raw_path.write_bytes(
                        gzip.compress(payload, compresslevel=9, mtime=0)
                    )
                    total, parsed_records = provider.parse(
                        payload, query.query_id
                    )
                    if len(parsed_records) > remaining:
                        parsed_records = parsed_records[:remaining]
                    returned = len(parsed_records)
                    cumulative += returned
                    cursor_out = next_cursor(
                        provider_name, payload, cursor, returned, total
                    )
                    truncated = provider_coverage_is_truncated(
                        provider_name,
                        cumulative,
                        total,
                        arguments.max_records_per_query,
                        cursor_out,
                    )
                    entry.update(
                        {
                            "retrieved_at_utc": utc_now(),
                            "http_status": str(status),
                            "response_date": response_headers["date"],
                            "response_etag": response_headers["etag"],
                            "rate_limit_remaining": response_headers[
                                "rate_limit_remaining"
                            ],
                            "total_results": (
                                "" if total is None else str(total)
                            ),
                            "returned_results": str(returned),
                            "cumulative_results": str(cumulative),
                            "cursor_out": cursor_out,
                            "raw_file": str(raw_relative),
                            "raw_sha256": digest,
                            "truncated": "yes" if truncated else "no",
                        }
                    )
                    records.extend(parsed_records)
                except Exception as error:
                    entry.update(
                        {
                            "retrieved_at_utc": utc_now(),
                            "error": (
                                f"{type(error).__name__}: "
                                f"{clean_text(error)}"
                            ),
                        }
                    )
                    print(
                        f"{provider.name} {query.query_id} page "
                        f"{page_index} failed: {entry['error']}",
                        file=sys.stderr,
                    )
                    record_manifest(entry)
                    break

                record_manifest(entry)
                page_index += 1
                if not cursor_out or returned == 0:
                    break
                cursor = cursor_out
                time.sleep(provider.minimum_delay_seconds)
            time.sleep(provider.minimum_delay_seconds)

    finished_at = utc_now()
    deduplicated = deduplicate(records)
    write_csv(run_dir / "records.csv", RECORD_FIELDS, records)
    write_csv(run_dir / "deduplicated.csv", DEDUP_FIELDS, deduplicated)
    write_json(
        run_dir / "run.json",
        {
            "status": "complete",
            "script_version": SCRIPT_VERSION,
            "script_sha256": script_digest,
            "repository_commit": repository_commit,
            "started_at_utc": started_at,
            "finished_at_utc": finished_at,
            "queries_file": str(queries_path),
            "queries_sha256": query_digest,
            "providers": arguments.providers,
            "publication_cutoff": PUBLICATION_CUTOFF,
            "arxiv_submission_cutoff": ARXIV_SUBMISSION_CUTOFF,
            "max_records_per_provider_query": (
                arguments.max_records_per_query
            ),
            "query_count": len(queries),
            "request_count": len(manifest),
            "successful_request_count": sum(
                1 for entry in manifest if entry["http_status"]
            ),
            "failed_request_count": sum(
                1
                for entry in manifest
                if entry["error"]
                and not entry["error"].startswith("SKIPPED:")
            ),
            "skipped_request_count": sum(
                1
                for entry in manifest
                if entry["error"].startswith("SKIPPED:")
            ),
            "normalized_record_count": len(records),
            "deduplicated_record_count": len(deduplicated),
            "user_agent": USER_AGENT,
            "coverage_notes": {
                "crossref": (
                    "Exact-title DOI reconciliation only; top 20 results "
                    "per seed are retained, not exhaustive discovery."
                ),
                "dblp": "The public search API exposes at most 1000 hits.",
                "openalex": (
                    "Search is skipped unless OPENALEX_API_KEY is set."
                ),
                "semanticscholar": (
                    "Bulk search is skipped unless "
                    "SEMANTIC_SCHOLAR_API_KEY is set."
                ),
            },
        },
    )

    print(f"run: {run_dir}")
    print(f"requests: {len(manifest)}")
    failures = sum(
        1
        for entry in manifest
        if entry["error"] and not entry["error"].startswith("SKIPPED:")
    )
    skipped = sum(
        1 for entry in manifest if entry["error"].startswith("SKIPPED:")
    )
    print(f"failures: {failures}")
    print(f"skipped: {skipped}")
    print(f"records: {len(records)}")
    print(f"deduplicated: {len(deduplicated)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
