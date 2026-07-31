#!/usr/bin/env python3
"""Search public Zenodo metadata and public GitHub code for formal artifacts.

Zenodo responses are preserved verbatim. GitHub code search requires an
authenticated `gh` client; its response is filtered in memory and only records
whose repository reports `isPrivate == false` are written to disk. This avoids
placing private-repository metadata in a shareable novelty-audit corpus.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
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
from typing import Any


SCRIPT_VERSION = "1"
PUBLICATION_CUTOFF = "2026-07-31"
USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
PROVIDERS = ("zenodo", "github-code")
QUERY_FIELDS = ("query_id", "provider", "query_text", "purpose")
MANIFEST_FIELDS = (
    "provider",
    "query_id",
    "query_text",
    "provider_query",
    "requested_url",
    "retrieved_at_utc",
    "status",
    "http_status",
    "total_results",
    "returned_public_results",
    "result_cap",
    "truncated",
    "preserved_response",
    "response_sha256",
    "error",
)
RECORD_FIELDS = (
    "provider",
    "query_id",
    "provider_record_id",
    "title_or_path",
    "repository",
    "creators",
    "publication_date",
    "doi",
    "resource_type",
    "url",
    "sha",
)


@dataclass(frozen=True)
class Query:
    query_id: str
    provider: str
    query_text: str
    purpose: str


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def clean(value: Any) -> str:
    if value is None:
        return ""
    return " ".join(str(value).split())


def read_queries(path: Path) -> list[Query]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if tuple(reader.fieldnames or ()) != QUERY_FIELDS:
            raise ValueError(
                f"{path} must have exactly these columns: {QUERY_FIELDS}"
            )
        rows = [
            Query(
                query_id=clean(row["query_id"]),
                provider=clean(row["provider"]),
                query_text=clean(row["query_text"]),
                purpose=clean(row["purpose"]),
            )
            for row in reader
        ]
    identifiers = [query.query_id for query in rows]
    if not rows:
        raise ValueError("query catalogue is empty")
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("query_id values must be unique")
    for query in rows:
        if not all(
            (query.query_id, query.provider, query.query_text, query.purpose)
        ):
            raise ValueError(f"incomplete query row: {query}")
        if query.provider not in PROVIDERS:
            raise ValueError(
                f"unsupported provider {query.provider!r} in {query.query_id}"
            )
    return rows


def request_bytes(
    url: str,
    timeout: float,
    retries: int,
) -> tuple[bytes, int]:
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": USER_AGENT,
        },
    )
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read(), response.status
        except urllib.error.HTTPError as error:
            if error.code not in {429, 500, 502, 503, 504} or attempt == retries:
                raise
            retry_after = error.headers.get("Retry-After", "")
            delay = float(retry_after) if retry_after.isdigit() else 2**attempt
            time.sleep(min(delay, 60.0))
        except (urllib.error.URLError, TimeoutError):
            if attempt == retries:
                raise
            time.sleep(min(2**attempt, 30.0))
    raise AssertionError("unreachable")


def zenodo_query(
    query: Query,
    raw_dir: Path,
    timeout: float,
    retries: int,
    result_cap: int,
) -> tuple[dict[str, str], list[dict[str, str]]]:
    provider_query = (
        f"({query.query_text}) AND "
        f"publication_date:[* TO {PUBLICATION_CUTOFF}]"
    )
    url = "https://zenodo.org/api/records?" + urllib.parse.urlencode(
        {
            "q": provider_query,
            "size": min(result_cap, 25),
            "sort": "bestmatch",
            "all_versions": "false",
        }
    )
    payload, status = request_bytes(url, timeout, retries)
    parsed = json.loads(payload)
    hits = parsed.get("hits", {})
    total = hits.get("total", 0)
    if isinstance(total, dict):
        total = total.get("value", 0)
    result_hits = hits.get("hits", [])
    raw_path = raw_dir / f"{query.query_id}.json"
    raw_path.write_bytes(payload)
    records: list[dict[str, str]] = []
    for hit in result_hits:
        metadata = hit.get("metadata", {})
        creators = metadata.get("creators", [])
        names = [
            clean(creator.get("name"))
            for creator in creators
            if isinstance(creator, dict) and clean(creator.get("name"))
        ]
        records.append(
            {
                "provider": query.provider,
                "query_id": query.query_id,
                "provider_record_id": clean(hit.get("id")),
                "title_or_path": clean(metadata.get("title")),
                "repository": "",
                "creators": "; ".join(names),
                "publication_date": clean(metadata.get("publication_date")),
                "doi": clean(hit.get("doi") or metadata.get("doi")),
                "resource_type": clean(
                    (metadata.get("resource_type") or {}).get("title")
                ),
                "url": clean(
                    (hit.get("links") or {}).get("html")
                    or f"https://zenodo.org/records/{hit.get('id', '')}"
                ),
                "sha": "",
            }
        )
    manifest = {
        "provider": query.provider,
        "query_id": query.query_id,
        "query_text": query.query_text,
        "provider_query": provider_query,
        "requested_url": url,
        "retrieved_at_utc": utc_now(),
        "status": "success",
        "http_status": str(status),
        "total_results": str(total),
        "returned_public_results": str(len(records)),
        "result_cap": str(min(result_cap, 25)),
        "truncated": str(int(int(total) > len(records))),
        "preserved_response": str(raw_path.name),
        "response_sha256": sha256_bytes(payload),
        "error": "",
    }
    return manifest, records


def github_query(
    query: Query,
    raw_dir: Path,
    timeout: float,
    result_cap: int,
) -> tuple[dict[str, str], list[dict[str, str]]]:
    command = [
        "gh",
        "search",
        "code",
        query.query_text,
        "--limit",
        str(result_cap),
        "--json",
        "path,repository,sha,url",
    ]
    completed = subprocess.run(
        command,
        check=True,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    parsed = json.loads(completed.stdout)
    public_hits = [
        hit
        for hit in parsed
        if (hit.get("repository") or {}).get("isPrivate") is False
    ]
    public_payload = json.dumps(
        public_hits,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    ).encode("utf-8")
    public_path = raw_dir / f"{query.query_id}-public.json"
    public_path.write_bytes(public_payload)
    records: list[dict[str, str]] = []
    for hit in public_hits:
        repository = hit.get("repository") or {}
        repository_name = clean(repository.get("nameWithOwner"))
        path = clean(hit.get("path"))
        sha = clean(hit.get("sha"))
        records.append(
            {
                "provider": query.provider,
                "query_id": query.query_id,
                "provider_record_id": f"{repository_name}:{path}:{sha}",
                "title_or_path": path,
                "repository": repository_name,
                "creators": "",
                "publication_date": "",
                "doi": "",
                "resource_type": "public source code",
                "url": clean(hit.get("url")),
                "sha": sha,
            }
        )
    manifest = {
        "provider": query.provider,
        "query_id": query.query_id,
        "query_text": query.query_text,
        "provider_query": query.query_text,
        "requested_url": "gh search code (authenticated; public rows only)",
        "retrieved_at_utc": utc_now(),
        "status": "success",
        "http_status": "",
        "total_results": "",
        "returned_public_results": str(len(records)),
        "result_cap": str(result_cap),
        "truncated": str(int(len(parsed) >= result_cap)),
        "preserved_response": str(public_path.name),
        "response_sha256": sha256_bytes(public_payload),
        "error": "",
    }
    return manifest, records


def failure_manifest(query: Query, error: Exception) -> dict[str, str]:
    return {
        "provider": query.provider,
        "query_id": query.query_id,
        "query_text": query.query_text,
        "provider_query": query.query_text,
        "requested_url": "",
        "retrieved_at_utc": utc_now(),
        "status": "failed",
        "http_status": "",
        "total_results": "",
        "returned_public_results": "0",
        "result_cap": "",
        "truncated": "",
        "preserved_response": "",
        "response_sha256": "",
        "error": f"{type(error).__name__}: {error}",
    }


def write_csv(
    path: Path,
    fieldnames: tuple[str, ...],
    rows: list[dict[str, str]],
) -> None:
    with path.open("x", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--queries",
        type=Path,
        default=audit_dir / "artifact-index-queries.csv",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=audit_dir / "data" / "artifact-runs",
    )
    parser.add_argument("--run-id", default=default_run_id())
    parser.add_argument(
        "--providers",
        nargs="+",
        choices=PROVIDERS,
        default=list(PROVIDERS),
    )
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--retries", type=int, default=3)
    parser.add_argument("--zenodo-limit", type=int, default=25)
    parser.add_argument("--github-limit", type=int, default=100)
    parser.add_argument("--validate-only", action="store_true")
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    queries_path = arguments.queries.resolve()
    output_root = arguments.output_root.resolve()
    queries = read_queries(queries_path)
    selected = [
        query for query in queries if query.provider in arguments.providers
    ]
    if not selected:
        raise ValueError("no queries selected")
    if arguments.retries < 0:
        raise ValueError("--retries must be nonnegative")
    if not 1 <= arguments.zenodo_limit <= 25:
        raise ValueError("--zenodo-limit must be between 1 and 25")
    if not 1 <= arguments.github_limit <= 100:
        raise ValueError("--github-limit must be between 1 and 100")
    if "github-code" in arguments.providers and shutil.which("gh") is None:
        raise RuntimeError("github-code searches require the gh executable")
    print(f"validated {len(selected)} artifact-index queries")
    if arguments.validate_only:
        return 0

    run_dir = output_root / arguments.run_id
    run_dir.mkdir(parents=True, exist_ok=False)
    raw_dir = run_dir / "raw"
    raw_dir.mkdir()
    query_snapshot = run_dir / "artifact-index-queries.csv"
    shutil.copyfile(queries_path, query_snapshot)
    manifest_rows: list[dict[str, str]] = []
    record_rows: list[dict[str, str]] = []
    started_at = utc_now()
    for query in selected:
        try:
            if query.provider == "zenodo":
                manifest, records = zenodo_query(
                    query,
                    raw_dir,
                    arguments.timeout,
                    arguments.retries,
                    arguments.zenodo_limit,
                )
            else:
                manifest, records = github_query(
                    query,
                    raw_dir,
                    arguments.timeout,
                    arguments.github_limit,
                )
            manifest_rows.append(manifest)
            record_rows.extend(records)
            print(
                f"{query.query_id}: success "
                f"({manifest['returned_public_results']} public records)"
            )
        except Exception as error:
            manifest_rows.append(failure_manifest(query, error))
            print(
                f"{query.query_id}: failed: {type(error).__name__}: {error}",
                file=sys.stderr,
            )
        if query.provider == "zenodo":
            time.sleep(2.1)

    write_csv(run_dir / "manifest.csv", MANIFEST_FIELDS, manifest_rows)
    write_csv(run_dir / "records.csv", RECORD_FIELDS, record_rows)
    completed_at = utc_now()
    run_metadata = {
        "script_version": SCRIPT_VERSION,
        "publication_cutoff": PUBLICATION_CUTOFF,
        "started_at_utc": started_at,
        "completed_at_utc": completed_at,
        "providers": arguments.providers,
        "query_count": len(selected),
        "successful_queries": sum(
            row["status"] == "success" for row in manifest_rows
        ),
        "failed_queries": sum(
            row["status"] == "failed" for row in manifest_rows
        ),
        "public_record_rows": len(record_rows),
        "query_snapshot_sha256": sha256_file(query_snapshot),
        "script_sha256": sha256_file(Path(__file__).resolve()),
        "github_privacy_rule": (
            "Only hits whose repository reports isPrivate == false are "
            "preserved; the unfiltered GitHub response is never written."
        ),
    }
    (run_dir / "run.json").write_text(
        json.dumps(run_metadata, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    failures = run_metadata["failed_queries"]
    print(f"run: {run_dir}")
    print(f"public record rows: {len(record_rows)}")
    print(f"failures: {failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
