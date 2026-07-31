#!/usr/bin/env python3
"""Prepare a lossless, reproducible screening queue from a citation run."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


SCRIPT_VERSION = "1"
RUN_ID_RE = re.compile(r"^\d{8}T\d{6}Z(?:-[a-z0-9][a-z0-9._-]*)?$")

QUEUE_FIELDS = (
    "candidate_id",
    "work_key",
    "title",
    "year",
    "publication_date",
    "doi",
    "arxiv_id",
    "venue",
    "providers",
    "provider_work_ids",
    "retrieval_seed_ids",
    "retrieval_screening_record_ids",
    "reference_seed_ids",
    "citation_seed_ids",
    "cutoff_status",
    "is_existing_seed",
    "matched_categories",
    "priority_score",
    "triage_state",
    "screening_decision",
    "reviewer",
    "review_date",
    "notes",
)

CATEGORY_PATTERNS = {
    "treiber": (8, (r"\btreiber\b",)),
    "spurious_weak_cas": (
        8,
        (
            r"\bspurious\b",
            r"\bweak[- ]?(?:cas|compare(?:-| )and(?:-| )exchange)\b",
            r"\bcompare_exchange_weak\b",
        ),
    ),
    "fairness_or_justice": (
        5,
        (r"\bfair(?:ness)?\b", r"\bjustice\b"),
    ),
    "weak_or_relaxed_memory": (
        4,
        (
            r"\b(?:rc11|c11|c\+\+11)\b",
            r"\bweak memory\b",
            r"\brelaxed memory\b",
            r"\bmemory consistency\b",
        ),
    ),
    "progress": (
        3,
        (
            r"\bprogress\b",
            r"\bliveness\b",
            r"\btermination\b",
            r"\block[- ]?free(?:dom)?\b",
            r"\bnon[- ]?blocking\b",
            r"\bwait[- ]?free(?:dom)?\b",
        ),
    ),
    "concurrent_stack": (
        3,
        (r"\b(?:concurrent|non[- ]?blocking|lock[- ]?free) stack\b",),
    ),
    "formal_verification": (
        2,
        (
            r"\bformal(?:ly)?\b",
            r"\bverif(?:y|ied|ication)\b",
            r"\bmechaniz(?:e|ed|ation)\b",
            r"\bproof\b",
            r"\bmodel check(?:er|ing)?\b",
        ),
    ),
    "compare_exchange_or_cas": (
        1,
        (
            r"\bcompare(?:-| )and(?:-| )exchange\b",
            r"\bcompare_exchange\b",
            r"\bcas\b",
            r"\bll/sc\b",
        ),
    ),
    "reclamation_or_aba": (
        1,
        (
            r"\breclamation\b",
            r"\bhazard pointer\b",
            r"\baba\b",
        ),
    ),
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


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


def read_csv(
    path: Path,
    required: set[str] | None = None,
    exact: tuple[str, ...] | None = None,
) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
        fields = tuple(reader.fieldnames or ())
    if exact is not None and fields != exact:
        raise ValueError(
            f"{path} columns differ: expected={list(exact)}, "
            f"actual={list(fields)}"
        )
    if required is not None:
        missing = required - set(fields)
        if missing:
            raise ValueError(f"{path} lacks columns: {sorted(missing)}")
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
        raise ValueError(f"{path} has malformed rows: {malformed}")
    return rows


def write_csv(
    path: Path,
    fields: Iterable[str],
    rows: Iterable[dict[str, Any]],
) -> None:
    with path.open("x", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(fields),
            extrasaction="raise",
        )
        writer.writeheader()
        writer.writerows(rows)


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


def verify_source_checksums(run_dir: Path) -> tuple[int, str]:
    checksum_path = run_dir / "checksums.csv"
    rows = read_csv(
        checksum_path,
        exact=("path", "sha256", "bytes"),
    )
    if not rows:
        raise ValueError(f"{checksum_path} is empty")
    seen: set[str] = set()
    for row in rows:
        relative = row["path"]
        if relative in seen:
            raise ValueError(
                f"{checksum_path} repeats path {relative!r}"
            )
        seen.add(relative)
        path = (run_dir / relative).resolve()
        try:
            path.relative_to(run_dir.resolve())
        except ValueError as error:
            raise ValueError(
                f"checksum path escapes the run: {relative!r}"
            ) from error
        if not path.is_file():
            raise ValueError(f"checksummed file is missing: {relative}")
        if not row["bytes"].isdigit():
            raise ValueError(
                f"invalid byte count for {relative}: {row['bytes']!r}"
            )
        if path.stat().st_size != int(row["bytes"]):
            raise ValueError(f"byte-count mismatch for {relative}")
        if sha256_file(path) != row["sha256"]:
            raise ValueError(f"SHA-256 mismatch for {relative}")
    return len(rows), sha256_file(checksum_path)


def split_values(value: str) -> set[str]:
    return {item for item in value.split(";") if item}


def title_categories(title: str) -> tuple[list[str], int]:
    text = title.casefold()
    matched: list[str] = []
    score = 0
    for category, (weight, patterns) in CATEGORY_PATTERNS.items():
        if any(re.search(pattern, text) for pattern in patterns):
            matched.append(category)
            score += weight
    return matched, score


def build_queue(
    works: list[dict[str, str]],
    edges: list[dict[str, str]],
) -> list[dict[str, str]]:
    references: dict[str, set[str]] = defaultdict(set)
    citations: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        seed_ids = split_values(edge["seed_ids"])
        directions = split_values(edge["directions"])
        if "references" in directions:
            references[edge["target_work_key"]].update(seed_ids)
        if "citations" in directions:
            citations[edge["source_work_key"]].update(seed_ids)

    stable_works = sorted(works, key=lambda row: row["work_key"])
    queue: list[dict[str, str]] = []
    for index, work in enumerate(stable_works, start=1):
        categories, score = title_categories(work["title"])
        is_seed = "seed-catalog" in split_values(work["providers"])
        cutoff = work["cutoff_status"]
        if is_seed:
            state = "existing-seed"
        elif cutoff == "excluded-after-cutoff":
            state = "after-cutoff-manual-confirmation"
        elif cutoff in {"unknown-date", "conflict"}:
            state = "manual-date-check"
        elif not work["title"]:
            state = "missing-title-manual-check"
        elif score >= 5:
            state = "priority-title-screen"
        else:
            state = "title-screen"
        queue.append(
            {
                "candidate_id": f"CG{index:04d}",
                "work_key": work["work_key"],
                "title": work["title"],
                "year": work["year"],
                "publication_date": work["publication_date"],
                "doi": work["doi"],
                "arxiv_id": work["arxiv_id"],
                "venue": work["venue"],
                "providers": work["providers"],
                "provider_work_ids": work["provider_work_ids"],
                "retrieval_seed_ids": work["seed_ids"],
                "retrieval_screening_record_ids": (
                    work["screening_record_ids"]
                ),
                "reference_seed_ids": ";".join(
                    sorted(references[work["work_key"]])
                ),
                "citation_seed_ids": ";".join(
                    sorted(citations[work["work_key"]])
                ),
                "cutoff_status": cutoff,
                "is_existing_seed": "yes" if is_seed else "no",
                "matched_categories": ";".join(categories),
                "priority_score": str(score),
                "triage_state": state,
                "screening_decision": "",
                "reviewer": "",
                "review_date": "",
                "notes": (
                    "Keyword score is prioritization only; it is not an "
                    "eligibility or exclusion decision."
                ),
            }
        )
    if len(queue) != len(works):
        raise AssertionError("the screening queue lost work rows")
    return sorted(
        queue,
        key=lambda row: (
            row["triage_state"] == "existing-seed",
            -int(row["priority_score"]),
            row["work_key"],
        ),
    )


def write_checksum_manifest(run_dir: Path) -> tuple[Path, str]:
    path = run_dir / "checksums.csv"
    rows = []
    for candidate in sorted(run_dir.rglob("*")):
        if not candidate.is_file() or candidate == path:
            continue
        rows.append(
            {
                "path": str(candidate.relative_to(run_dir)),
                "sha256": sha256_file(candidate),
                "bytes": str(candidate.stat().st_size),
            }
        )
    write_csv(path, ("path", "sha256", "bytes"), rows)
    return path, sha256_file(path)


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--citation-run",
        type=Path,
        required=True,
        help="completed citation-run directory",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=audit_dir / "data" / "citation-screening-runs",
        help="root for a new immutable screening-queue run",
    )
    parser.add_argument(
        "--run-id",
        default=default_run_id(),
        help="new UTC-stamped output directory name",
    )
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="verify the source run and print queue counts without writing",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    if not RUN_ID_RE.fullmatch(arguments.run_id):
        raise ValueError(
            "--run-id must begin with YYYYMMDDTHHMMSSZ"
        )
    citation_run = arguments.citation_run.resolve()
    checksum_count, source_checksum_digest = verify_source_checksums(
        citation_run
    )
    source_run = json.loads(
        (citation_run / "run.json").read_text(encoding="utf-8")
    )
    works = read_csv(
        citation_run / "deduplicated-works.csv",
        required={
            "work_key",
            "title",
            "year",
            "publication_date",
            "doi",
            "arxiv_id",
            "venue",
            "providers",
            "provider_work_ids",
            "seed_ids",
            "screening_record_ids",
            "cutoff_status",
        },
    )
    edges = read_csv(
        citation_run / "deduplicated-edges.csv",
        required={
            "source_work_key",
            "target_work_key",
            "seed_ids",
            "directions",
        },
    )
    work_keys = [work["work_key"] for work in works]
    if len(work_keys) != len(set(work_keys)):
        raise ValueError("deduplicated-works.csv repeats work_key")
    known = set(work_keys)
    orphan_edges = [
        edge["edge_key"]
        for edge in edges
        if edge["source_work_key"] not in known
        or edge["target_work_key"] not in known
    ]
    if orphan_edges:
        raise ValueError(
            f"deduplicated edges reference missing works: "
            f"{orphan_edges[:20]}"
        )

    queue = build_queue(works, edges)
    state_counts: dict[str, int] = defaultdict(int)
    for row in queue:
        state_counts[row["triage_state"]] += 1
    if arguments.validate_only:
        print(f"source checksums verified: {checksum_count}")
        print(f"source works: {len(works)}")
        print(f"source edges: {len(edges)}")
        print(f"queue rows: {len(queue)}")
        for state in sorted(state_counts):
            print(f"{state}: {state_counts[state]}")
        return 0

    output_root = arguments.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    run_dir = output_root / arguments.run_id
    run_dir.mkdir(exist_ok=False)
    script_path = Path(__file__).resolve()
    write_csv(
        run_dir / "citation-screening-queue.csv",
        QUEUE_FIELDS,
        queue,
    )
    inputs = run_dir / "inputs"
    inputs.mkdir()
    for source, destination in (
        (citation_run / "run.json", inputs / "citation-run.json"),
        (
            citation_run / "checksums.csv",
            inputs / "citation-run-checksums.csv",
        ),
        (script_path, inputs / script_path.name),
    ):
        with destination.open("xb") as handle:
            handle.write(source.read_bytes())
    write_json(
        run_dir / "run.json",
        {
            "status": "queue-prepared-human-screening-pending",
            "script_version": SCRIPT_VERSION,
            "script_sha256": sha256_file(script_path),
            "repository_commit": git_commit(script_path.parent),
            "created_at_utc": utc_now(),
            "source_citation_run": str(citation_run),
            "source_citation_run_status": source_run.get("status", ""),
            "source_citation_run_request_status": source_run.get(
                "request_status",
                "",
            ),
            "source_citation_run_coverage_status": source_run.get(
                "coverage_status",
                "",
            ),
            "source_checksum_manifest_sha256": source_checksum_digest,
            "source_checksums_verified": checksum_count,
            "source_work_count": len(works),
            "source_edge_count": len(edges),
            "queue_row_count": len(queue),
            "triage_state_counts": dict(sorted(state_counts.items())),
            "method_note": (
                "Every deduplicated work is retained. Keyword categories "
                "only prioritize manual title/full-text screening and never "
                "constitute inclusion or exclusion."
            ),
        },
    )
    checksum_path, checksum_digest = write_checksum_manifest(run_dir)
    print(f"run: {run_dir}")
    print(f"queue rows: {len(queue)}")
    print(
        f"checksum manifest: {checksum_path} "
        f"sha256={checksum_digest}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}")
        raise SystemExit(2)
