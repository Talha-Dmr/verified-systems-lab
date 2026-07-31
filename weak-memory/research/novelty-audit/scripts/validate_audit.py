#!/usr/bin/env python3
"""Validate the canonical novelty-audit ledgers and their foreign keys."""

from __future__ import annotations

import csv
import hashlib
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def read_csv(name: str, required: set[str]) -> list[dict[str, str]]:
    path = ROOT / name
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        fields = set(reader.fieldnames or ())
        missing = required - fields
        if missing:
            raise ValueError(f"{name}: missing columns: {sorted(missing)}")
        rows = list(reader)
    malformed = [
        index + 2
        for index, row in enumerate(rows)
        if None in row or any(value is None for value in row.values())
    ]
    if malformed:
        raise ValueError(
            f"{name}: row width does not match header at CSV lines {malformed}"
        )
    return rows


def unique_index(
    name: str, rows: list[dict[str, str]], key: str
) -> dict[str, dict[str, str]]:
    values = [row[key] for row in rows]
    blank = [index + 2 for index, value in enumerate(values) if not value]
    duplicates = sorted(value for value, count in Counter(values).items() if count > 1)
    if blank:
        raise ValueError(f"{name}: blank {key} at CSV lines {blank}")
    if duplicates:
        raise ValueError(f"{name}: duplicate {key}: {duplicates}")
    return dict(zip(values, rows, strict=True))


def require_equal(label: str, left: set[str], right: set[str]) -> None:
    if left == right:
        return
    raise ValueError(
        f"{label}: left-only={sorted(left - right)}, right-only={sorted(right - left)}"
    )


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def main() -> None:
    primary = read_csv("primary-sources.csv", {"source_id", "title", "primary_url"})
    screening = read_csv(
        "screening.csv", {"record_id", "title", "decision", "reviewer"}
    )
    matrix = read_csv(
        "prior-art-matrix.csv",
        {"record_id", "short_citation", "subsumes_candidate", "confidence"},
    )
    closest_map = read_csv(
        "closest-work-map.csv",
        {"screening_record_id", "matrix_record_id", "relationship"},
    )
    seeds = read_csv(
        "citation-seeds.csv",
        {"seed_id", "screening_record_id", "title", "screening_decision"},
    )
    provider_queries = read_csv(
        "provider-queries.csv", {"query_id", "provider", "query_text"}
    )

    primary_by_id = unique_index("primary-sources.csv", primary, "source_id")
    screening_by_id = unique_index("screening.csv", screening, "record_id")
    matrix_by_id = unique_index("prior-art-matrix.csv", matrix, "record_id")
    map_by_screening = unique_index(
        "closest-work-map.csv", closest_map, "screening_record_id"
    )
    unique_index("closest-work-map.csv", closest_map, "matrix_record_id")
    unique_index("citation-seeds.csv", seeds, "seed_id")
    seed_by_screening = unique_index(
        "citation-seeds.csv", seeds, "screening_record_id"
    )
    unique_index("provider-queries.csv", provider_queries, "query_id")

    canonical_screening_ids = {
        record_id for record_id in screening_by_id if record_id.startswith("S")
    }
    require_equal(
        "primary-source/screening coverage",
        set(primary_by_id),
        canonical_screening_ids,
    )

    closest_ids = {
        row["record_id"]
        for row in screening
        if row["decision"] == "include-closest"
    }
    require_equal("closest-work map coverage", closest_ids, set(map_by_screening))
    require_equal("citation-seed coverage", closest_ids, set(seed_by_screening))

    for row in closest_map:
        if row["matrix_record_id"] not in matrix_by_id:
            raise ValueError(
                "closest-work-map.csv: unknown matrix_record_id "
                f"{row['matrix_record_id']}"
            )
        if row["relationship"] != "direct":
            raise ValueError(
                "closest-work-map.csv: unexpected relationship "
                f"{row['relationship']!r}"
            )

    for row in seeds:
        screening_row = screening_by_id[row["screening_record_id"]]
        if row["screening_decision"] != "include-closest":
            raise ValueError(
                f"citation-seeds.csv: {row['seed_id']} is not include-closest"
            )
        if row["title"] != screening_row["title"]:
            raise ValueError(
                f"citation-seeds.csv: title mismatch for {row['seed_id']}"
            )

    subsuming = [
        row["record_id"]
        for row in matrix
        if row["subsumes_candidate"].strip().lower() != "no"
    ]
    if subsuming:
        raise ValueError(
            "prior-art-matrix.csv: review non-'no' subsumption rows: "
            f"{subsuming}"
        )

    providers = Counter(row["provider"] for row in provider_queries)
    files = (
        "primary-sources.csv",
        "screening.csv",
        "prior-art-matrix.csv",
        "closest-work-map.csv",
        "citation-seeds.csv",
        "provider-queries.csv",
    )

    print("audit ledger validation: passed")
    print(f"canonical sources: {len(primary)}")
    print(f"screening records: {len(screening)}")
    print(f"closest works: {len(closest_ids)}")
    print(f"theorem-level comparisons: {len(matrix)}")
    print(f"provider queries: {len(provider_queries)} {dict(sorted(providers.items()))}")
    for name in files:
        print(f"{name}: sha256:{sha256(name)}")


if __name__ == "__main__":
    main()
