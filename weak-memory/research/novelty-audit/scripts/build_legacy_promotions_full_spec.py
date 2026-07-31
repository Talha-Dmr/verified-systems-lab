#!/usr/bin/env python3
"""Merge the reviewed legacy-promotion slices into a checksum-bound full spec."""

from __future__ import annotations

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path

from build_decision_overlay import SPEC_FIELDS


QUEUE_SHA256 = "6d3fa534af413d6280bba82e7e3ef34400dbe7d590bd604e956add8d0928257b"
REVIEW_FIELDS = (
    "line",
    "physical_line",
    "candidate_id",
    "work_key",
    "title",
    "decision",
    "canonical",
    "doi",
    "open_pdf",
)
REVIEW_SHA256 = {
    "legacy-promotions-first-review-20260731T092100Z.csv":
        "cf0b7de1d9a04f774e3e8d7d84dc1db66128a3e63af1f203ece7d51f2ed3e74b",
    "legacy-promotions-middle-review-20260731T092100Z.csv":
        "7d571494a8885d3f74eb751ce490263f6ac51ce052a0db2b0672503d01a5a0d3",
    "legacy-promotions-tail-review-20260731T092100Z.csv":
        "adcb01703d1ae9968cf9b70af88b349397384cc03944542b8b02c55c01df3907",
}
EXPECTED_COUNTS = {
    "exclude-duplicate": 102,
    "exclude-secondary": 197,
    "exclude-topic": 948,
    "include-adjacent": 413,
    "include-closest": 4,
    "include-context": 157,
    "linked-existing": 157,
}
CLOSEST_MATRIX = {
    "CG1155": "PA122",
    "CG0553": "PA119",
    "CG1057": "PA120",
    "CG1441": "PA121",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path, expected_fields: tuple[str, ...]) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != expected_fields:
            raise ValueError(
                f"{path}: expected fields {expected_fields}, got {reader.fieldnames}"
            )
        rows = list(reader)
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        raise ValueError(f"{path}: malformed row width")
    return rows


def canonical_source(value: str) -> str:
    """Strip an optional theorem-matrix annotation from a canonical source ID."""
    return value.split("/", 1)[0]


def parse_args() -> argparse.Namespace:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--queue",
        type=Path,
        default=(
            root
            / "data"
            / "citation-screening-runs"
            / "20260731T092100Z-legacy-promotions-union"
            / "citation-screening-queue.csv"
        ),
    )
    parser.add_argument(
        "--review-slices",
        nargs=3,
        type=Path,
        default=[
            root
            / "data"
            / "decision-specs"
            / "legacy-promotions-first-review-20260731T092100Z.csv",
            root
            / "data"
            / "decision-specs"
            / "legacy-promotions-middle-review-20260731T092100Z.csv",
            root
            / "data"
            / "decision-specs"
            / "legacy-promotions-tail-review-20260731T092100Z.csv",
        ],
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "citation-screening-spec-20260731T092100Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError("legacy-promotions citation queue checksum mismatch")
    for path in args.review_slices:
        expected = REVIEW_SHA256.get(path.name)
        if expected is None or sha256(path) != expected:
            raise ValueError(f"review-slice checksum mismatch: {path}")
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    with args.queue.open(newline="", encoding="utf-8") as stream:
        queue = list(csv.DictReader(stream))
    reviewed = [
        row
        for path in args.review_slices
        for row in read_csv(path, REVIEW_FIELDS)
    ]
    if len(reviewed) != len(queue):
        raise ValueError(
            f"review/queue row-count mismatch: {len(reviewed)} != {len(queue)}"
        )

    queue_ids = [row["candidate_id"] for row in queue]
    reviewed_ids = [row["candidate_id"] for row in reviewed]
    if reviewed_ids != queue_ids:
        for index, (review_id, queue_id) in enumerate(
            zip(reviewed_ids, queue_ids, strict=False), start=2
        ):
            if review_id != queue_id:
                raise ValueError(
                    f"review order mismatch at queue line {index}: "
                    f"{review_id} != {queue_id}"
                )
        raise ValueError("review order mismatch after shared prefix")

    for index, (review, queue_row) in enumerate(
        zip(reviewed, queue, strict=True), start=2
    ):
        for field in ("candidate_id", "work_key", "doi"):
            if review[field] != queue_row[field]:
                raise ValueError(
                    f"metadata mismatch at queue line {index}, field {field}"
                )
        if queue_row["title"] and review["title"] != queue_row["title"]:
            raise ValueError(
                f"title mismatch at queue line {index}: "
                f"{review['title']!r} != {queue_row['title']!r}"
            )

    counts = Counter(row["decision"] for row in reviewed)
    if counts != Counter(EXPECTED_COUNTS):
        raise ValueError(f"decision-count mismatch: {counts}")
    closest_ids = {
        row["candidate_id"]
        for row in reviewed
        if row["decision"] == "include-closest"
    }
    if set(CLOSEST_MATRIX) != closest_ids:
        raise ValueError("closest-work matrix mapping coverage mismatch")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=SPEC_FIELDS)
        writer.writeheader()
        for row in reviewed:
            linked = row["decision"] == "linked-existing"
            writer.writerow(
                {
                    "candidate_id": row["candidate_id"],
                    "decision": row["decision"],
                    "canonical_record_id": (
                        canonical_source(row["canonical"]) if linked else ""
                    ),
                    "matrix_record_id": CLOSEST_MATRIX.get(
                        row["candidate_id"], ""
                    ),
                    "screening_stage": "",
                    "full_text_checked": "",
                    "evidence_url": row["open_pdf"],
                    "evidence_location": "",
                    "reason": "",
                }
            )

    print(f"queue rows: {len(queue)}")
    print(f"review rows: {len(reviewed)}")
    print(f"counts: {dict(sorted(counts.items()))}")
    print(f"output: {args.output}")
    print(f"sha256:{sha256(args.output)}")


if __name__ == "__main__":
    main()
