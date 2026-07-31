#!/usr/bin/env python3
"""Merge the reviewed closing-queue slices into a checksum-bound full spec."""

from __future__ import annotations

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path

from build_decision_overlay import SPEC_FIELDS


QUEUE_SHA256 = "935f05748f1260a1b88e5a213f13d73cf9f545bb7e799a9512a865b76d26e1c3"
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
    "final-four-first-review-20260731T101000Z.csv":
        "432ceb6648880b627d7fba56ce3b7b042f4fbb2f4d6d97acbf676c2ea555b223",
    "final-four-middle-review-20260731T101000Z.csv":
        "ae5acff2bd4c9cc53ffb1ca5fd04841539667384f9333fd3cc3ae2f2b81671ba",
    "final-four-tail-review-20260731T101000Z.csv":
        "7b50348be8d81238576b7272b1cea28b14840a3c88fbe85cc27227657d2160cd",
}
EXPECTED_COUNTS = {
    "exclude-duplicate": 12,
    "exclude-secondary": 21,
    "exclude-topic": 42,
    "include-adjacent": 46,
    "include-context": 17,
    "linked-existing": 41,
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
            / "20260731T101000Z-final-four-union"
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
            / "final-four-first-review-20260731T101000Z.csv",
            root
            / "data"
            / "decision-specs"
            / "final-four-middle-review-20260731T101000Z.csv",
            root
            / "data"
            / "decision-specs"
            / "final-four-tail-review-20260731T101000Z.csv",
        ],
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "citation-screening-spec-20260731T101000Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError("closing citation queue checksum mismatch")
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
        if (
            queue_row["title"]
            and review["title"].casefold() != queue_row["title"].casefold()
        ):
            raise ValueError(
                f"title mismatch at queue line {index}: "
                f"{review['title']!r} != {queue_row['title']!r}"
            )

    counts = Counter(row["decision"] for row in reviewed)
    if counts != Counter(EXPECTED_COUNTS):
        raise ValueError(f"decision-count mismatch: {counts}")
    if any(row["decision"] == "include-closest" for row in reviewed):
        raise ValueError("unexpected closest-work promotion in closing queue")

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
                    "matrix_record_id": "",
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
