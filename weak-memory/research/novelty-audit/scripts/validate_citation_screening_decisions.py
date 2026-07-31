#!/usr/bin/env python3
"""Validate a citation-screening decision overlay against an immutable queue."""

from __future__ import annotations

import argparse
import csv
import hashlib
import sys
from collections import Counter
from pathlib import Path


SCRIPT_VERSION = "1"

DECISION_FIELDS = (
    "source_queue_run_id",
    "source_queue_checksums_sha256",
    "candidate_id",
    "work_key",
    "title",
    "screening_stage",
    "decision",
    "canonical_record_id",
    "canonical_decision",
    "matrix_record_id",
    "full_text_checked",
    "evidence_url",
    "evidence_location",
    "reviewer",
    "review_date",
    "human_confirmation",
    "reason",
)

ALLOWED_STAGES = {"metadata", "full-text", "source-audit"}
ALLOWED_DECISIONS = {
    "linked-existing",
    "exclude-topic",
    "exclude-secondary",
    "exclude-duplicate",
    "include-context",
    "include-adjacent",
    "include-closest",
    "pending-full-text",
    "pending-metadata",
    "excluded-after-cutoff",
}
ALLOWED_FULL_TEXT = {"yes", "no", "partial", "not-applicable"}
ALLOWED_HUMAN_CONFIRMATION = {"pending", "confirmed"}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_rows(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8-sig") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise ValueError(f"{path}: missing CSV header")
        return reader.fieldnames, list(reader)


def verify_checksum_manifest(run_dir: Path) -> tuple[str, int]:
    manifest = run_dir / "checksums.csv"
    if not manifest.is_file():
        raise ValueError(f"missing queue checksum manifest: {manifest}")
    fields, rows = read_rows(manifest)
    if fields != ["path", "sha256", "bytes"]:
        raise ValueError(f"{manifest}: unexpected fields {fields}")
    for row in rows:
        target = run_dir / row["path"]
        if not target.is_file():
            raise ValueError(f"{manifest}: missing target {row['path']}")
        if sha256_file(target) != row["sha256"]:
            raise ValueError(f"{manifest}: SHA-256 mismatch for {row['path']}")
        if target.stat().st_size != int(row["bytes"]):
            raise ValueError(f"{manifest}: byte-count mismatch for {row['path']}")
    return sha256_file(manifest), len(rows)


def parse_args() -> argparse.Namespace:
    audit_dir = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--decisions",
        type=Path,
        default=audit_dir / "citation-screening-decisions.csv",
    )
    parser.add_argument(
        "--queue-run",
        type=Path,
        default=(
            audit_dir
            / "data"
            / "citation-screening-runs"
            / "20260731T024138Z"
        ),
    )
    parser.add_argument(
        "--screening",
        type=Path,
        default=audit_dir / "screening.csv",
    )
    parser.add_argument(
        "--matrix",
        type=Path,
        default=audit_dir / "prior-art-matrix.csv",
    )
    parser.add_argument(
        "--require-triage-state",
        action="append",
        default=[],
        help="Require decisions for every queue row in this triage state.",
    )
    parser.add_argument(
        "--require-all",
        action="store_true",
        help="Require a decision for every queue row.",
    )
    return parser.parse_args()


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    args = parse_args()
    try:
        checksum_sha256, checksum_count = verify_checksum_manifest(args.queue_run)
        queue_fields, queue_rows = read_rows(
            args.queue_run / "citation-screening-queue.csv"
        )
        decision_fields, decision_rows = read_rows(args.decisions)
        _, screening_rows = read_rows(args.screening)
        _, matrix_rows = read_rows(args.matrix)
    except (OSError, ValueError) as error:
        fail(str(error))

    if "candidate_id" not in queue_fields:
        fail("queue is missing candidate_id")
    if decision_fields != list(DECISION_FIELDS):
        fail(
            "decision fields differ from the version-1 schema: "
            f"{decision_fields}"
        )

    queue_run_id = args.queue_run.name
    queue_by_id = {row["candidate_id"]: row for row in queue_rows}
    if len(queue_by_id) != len(queue_rows):
        fail("queue contains duplicate candidate_id values")

    screening_by_id = {row["record_id"]: row for row in screening_rows}
    matrix_ids = {row["record_id"] for row in matrix_rows}
    seen_candidate_ids: set[str] = set()
    seen_work_keys: set[str] = set()

    for line_number, row in enumerate(decision_rows, start=2):
        where = f"{args.decisions}:{line_number}"
        candidate_id = row["candidate_id"]
        if candidate_id in seen_candidate_ids:
            fail(f"{where}: duplicate candidate_id {candidate_id}")
        seen_candidate_ids.add(candidate_id)
        if row["work_key"] in seen_work_keys:
            fail(f"{where}: duplicate work_key {row['work_key']}")
        seen_work_keys.add(row["work_key"])

        queue_row = queue_by_id.get(candidate_id)
        if queue_row is None:
            fail(f"{where}: candidate is absent from the source queue")
        if row["source_queue_run_id"] != queue_run_id:
            fail(f"{where}: source_queue_run_id does not match {queue_run_id}")
        if row["source_queue_checksums_sha256"] != checksum_sha256:
            fail(f"{where}: source queue checksum root does not match")
        for field in ("work_key", "title"):
            if row[field] != queue_row[field]:
                fail(f"{where}: {field} differs from the immutable queue")

        if row["screening_stage"] not in ALLOWED_STAGES:
            fail(f"{where}: invalid screening_stage {row['screening_stage']!r}")
        if row["decision"] not in ALLOWED_DECISIONS:
            fail(f"{where}: invalid decision {row['decision']!r}")
        if row["full_text_checked"] not in ALLOWED_FULL_TEXT:
            fail(
                f"{where}: invalid full_text_checked "
                f"{row['full_text_checked']!r}"
            )
        if row["human_confirmation"] not in ALLOWED_HUMAN_CONFIRMATION:
            fail(
                f"{where}: invalid human_confirmation "
                f"{row['human_confirmation']!r}"
            )
        if not row["reviewer"] or not row["review_date"] or not row["reason"]:
            fail(f"{where}: reviewer, review_date, and reason are required")

        canonical_id = row["canonical_record_id"]
        canonical_decision = row["canonical_decision"]
        if row["decision"] == "linked-existing":
            if not canonical_id:
                fail(f"{where}: linked-existing requires canonical_record_id")
            canonical = screening_by_id.get(canonical_id)
            if canonical is None:
                fail(f"{where}: unknown canonical_record_id {canonical_id}")
            if canonical_decision != canonical["decision"]:
                fail(
                    f"{where}: canonical_decision differs from "
                    f"{canonical_id}"
                )
        elif canonical_id or canonical_decision:
            fail(
                f"{where}: canonical fields are reserved for linked-existing"
            )

        matrix_id = row["matrix_record_id"]
        if matrix_id and matrix_id not in matrix_ids:
            fail(f"{where}: unknown matrix_record_id {matrix_id}")
        if row["decision"] == "include-closest" and not matrix_id:
            fail(f"{where}: include-closest requires a matrix_record_id")

    required_ids: set[str] = set()
    if args.require_all:
        required_ids.update(queue_by_id)
    for state in args.require_triage_state:
        state_ids = {
            row["candidate_id"]
            for row in queue_rows
            if row["triage_state"] == state
        }
        if not state_ids:
            fail(f"queue has no rows with triage_state {state!r}")
        required_ids.update(state_ids)
    missing = sorted(required_ids - seen_candidate_ids)
    if missing:
        fail(
            f"{len(missing)} required candidates lack decisions; "
            f"first: {', '.join(missing[:10])}"
        )

    counts = Counter(row["decision"] for row in decision_rows)
    confirmations = Counter(
        row["human_confirmation"] for row in decision_rows
    )
    print(f"script version: {SCRIPT_VERSION}")
    print(f"queue run: {queue_run_id}")
    print(f"queue checksum entries verified: {checksum_count}")
    print(f"queue checksum manifest SHA-256: {checksum_sha256}")
    print(f"queue rows: {len(queue_rows)}")
    print(f"decision rows: {len(decision_rows)}")
    for decision, count in sorted(counts.items()):
        print(f"{decision}: {count}")
    for status, count in sorted(confirmations.items()):
        print(f"human-confirmation-{status}: {count}")


if __name__ == "__main__":
    main()
