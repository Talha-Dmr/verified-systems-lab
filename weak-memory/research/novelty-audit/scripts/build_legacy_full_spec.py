#!/usr/bin/env python3
"""Merge the three reviewed legacy-queue slices into a validated full spec."""

from __future__ import annotations

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path

from build_decision_overlay import SPEC_FIELDS


QUEUE_SHA256 = "83ab9a60cfe14199b1b2c1896798bea5a9519fe5cd6ea085accbdffeb3c40778"
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
EXPECTED_COUNTS = {
    "exclude-duplicate": 97,
    "exclude-secondary": 91,
    "exclude-topic": 481,
    "include-adjacent": 187,
    "include-closest": 30,
    "include-context": 89,
    "linked-existing": 192,
}
CLOSEST_MATRIX = {
    "CG0020": "PA89",
    "CG0169": "PA90",
    "CG0251": "PA91",
    "CG0280": "PA92",
    "CG1018": "PA93",
    "CG0233": "PA94",
    "CG0430": "PA95",
    "CG0547": "PA96",
    "CG0610": "PA97",
    "CG0752": "PA98",
    "CG0771": "PA99",
    "CG0894": "PA100",
    "CG0972": "PA101",
    "CG1062": "PA102",
    "CG0001": "PA103",
    "CG0003": "PA104",
    "CG0007": "PA105",
    "CG0139": "PA106",
    "CG0145": "PA107",
    "CG0205": "PA108",
    "CG0209": "PA109",
    "CG0210": "PA110",
    "CG0223": "PA111",
    "CG0240": "PA112",
    "CG0241": "PA113",
    "CG0279": "PA114",
    "CG0288": "PA115",
    "CG0363": "PA116",
    "CG0381": "PA117",
    "CG0690": "PA118",
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
    """Strip optional theorem-matrix annotation from a linked source ID."""
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
            / "20260731T024138Z"
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
            / "legacy-first-review-20260731T024138Z.csv",
            root
            / "data"
            / "decision-specs"
            / "legacy-middle-review-20260731T024138Z.csv",
            root
            / "data"
            / "decision-specs"
            / "legacy-tail-review-20260731T024138Z.csv",
        ],
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "citation-screening-spec-20260731T024138Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError("legacy citation queue checksum mismatch")
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
