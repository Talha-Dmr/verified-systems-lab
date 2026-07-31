#!/usr/bin/env python3
"""Build a checksum-bound decision overlay from a compact reviewed specification."""

from __future__ import annotations

import argparse
import csv
import hashlib
from pathlib import Path

from validate_citation_screening_decisions import (
    ALLOWED_DECISIONS,
    ALLOWED_FULL_TEXT,
    ALLOWED_STAGES,
    DECISION_FIELDS,
    verify_checksum_manifest,
)


SPEC_FIELDS = (
    "candidate_id",
    "decision",
    "canonical_record_id",
    "matrix_record_id",
    "screening_stage",
    "full_text_checked",
    "evidence_url",
    "evidence_location",
    "reason",
)

DEFAULT_STAGE = {
    "linked-existing": "source-audit",
    "exclude-topic": "metadata",
    "exclude-secondary": "metadata",
    "exclude-duplicate": "metadata",
    "include-context": "full-text",
    "include-adjacent": "full-text",
    "include-closest": "full-text",
    "pending-full-text": "metadata",
    "pending-metadata": "metadata",
    "excluded-after-cutoff": "metadata",
}

DEFAULT_FULL_TEXT = {
    "linked-existing": "yes",
    "exclude-topic": "partial",
    "exclude-secondary": "partial",
    "exclude-duplicate": "partial",
    "include-context": "partial",
    "include-adjacent": "partial",
    "include-closest": "yes",
    "pending-full-text": "partial",
    "pending-metadata": "no",
    "excluded-after-cutoff": "not-applicable",
}

DEFAULT_REASON = {
    "linked-existing": (
        "Exact bibliographic or version identity with a canonical screened "
        "record; no independent theorem family is counted."
    ),
    "exclude-topic": (
        "Title, abstract, venue, and citation-lineage evidence place the work "
        "outside the target conjunction; no inaccessible-text absence claim "
        "is made."
    ),
    "exclude-secondary": (
        "Secondary, survey, editorial, proposal, or proceedings-level record; "
        "the relevant primary research is retained separately."
    ),
    "exclude-duplicate": (
        "Duplicate, preprint, metadata alias, or superseded version of a "
        "retained work, with no material theorem difference for this audit."
    ),
    "include-context": (
        "Retained as contextual semantic, historical, or verification "
        "evidence; no theorem matching the target conjunction was found."
    ),
    "include-adjacent": (
        "Retained as an adjacent result covering at least one target "
        "dimension; it does not establish the six-part conjunction."
    ),
    "include-closest": (
        "Retained for theorem-level comparison as a direct boundary on one or "
        "more central target dimensions."
    ),
    "pending-full-text": "Primary full-text review remains unresolved.",
    "pending-metadata": "Bibliographic identity remains unresolved.",
    "excluded-after-cutoff": "Publication falls after the declared cutoff.",
}

DEFAULT_EVIDENCE_LOCATION = {
    "linked-existing": "Exact DOI, title, and version-lineage reconciliation",
    "exclude-topic": "Title, abstract, venue, and citation-lineage screen",
    "exclude-secondary": "Document type, abstract, and primary-work lineage",
    "exclude-duplicate": "DOI, title, author, and version-lineage reconciliation",
    "include-context": "Primary-source scope and limitations screen",
    "include-adjacent": "Primary-source scope and theorem screen",
    "include-closest": "Primary theorem, model, primitive, and limitations screen",
    "pending-full-text": "Available metadata and partial source evidence",
    "pending-metadata": "Conflicting or incomplete provider metadata",
    "excluded-after-cutoff": "Provider publication-date metadata",
}


def read_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8-sig") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames is None:
            raise ValueError(f"{path}: missing CSV header")
        return reader.fieldnames, list(reader)


def unique_index(
    path: Path, rows: list[dict[str, str]], key: str
) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    for line_number, row in enumerate(rows, start=2):
        value = row[key]
        if not value:
            raise ValueError(f"{path}:{line_number}: blank {key}")
        if value in index:
            raise ValueError(f"{path}:{line_number}: duplicate {key} {value}")
        index[value] = row
    return index


def default_evidence_url(queue_row: dict[str, str]) -> str:
    if queue_row.get("doi"):
        return f"https://doi.org/{queue_row['doi']}"
    if queue_row.get("arxiv_id"):
        return f"https://arxiv.org/abs/{queue_row['arxiv_id']}"
    return ""


def parse_args() -> argparse.Namespace:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue-run", type=Path, required=True)
    parser.add_argument("--spec", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--screening", type=Path, default=root / "screening.csv")
    parser.add_argument(
        "--closest-map", type=Path, default=root / "closest-work-map.csv"
    )
    parser.add_argument("--review-date", default="2026-07-31")
    parser.add_argument("--require-all", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    checksum_sha256, _ = verify_checksum_manifest(args.queue_run)
    queue_fields, queue_rows = read_csv(
        args.queue_run / "citation-screening-queue.csv"
    )
    spec_fields, spec_rows = read_csv(args.spec)
    _, screening_rows = read_csv(args.screening)
    _, map_rows = read_csv(args.closest_map)

    if "candidate_id" not in queue_fields:
        raise ValueError("queue is missing candidate_id")
    if spec_fields != list(SPEC_FIELDS):
        raise ValueError(
            f"{args.spec}: expected fields {list(SPEC_FIELDS)}, got {spec_fields}"
        )

    queue_by_id = unique_index(
        args.queue_run / "citation-screening-queue.csv",
        queue_rows,
        "candidate_id",
    )
    spec_by_id = unique_index(args.spec, spec_rows, "candidate_id")
    screening_by_id = unique_index(args.screening, screening_rows, "record_id")
    matrix_by_screening = {
        row["screening_record_id"]: row["matrix_record_id"] for row in map_rows
    }

    unknown = sorted(set(spec_by_id) - set(queue_by_id))
    missing = sorted(set(queue_by_id) - set(spec_by_id))
    if unknown:
        raise ValueError(f"spec contains candidates absent from queue: {unknown}")
    if args.require_all and missing:
        raise ValueError(f"spec omits {len(missing)} queue candidates: {missing}")

    output_rows: list[dict[str, str]] = []
    for queue_row in queue_rows:
        spec = spec_by_id.get(queue_row["candidate_id"])
        if spec is None:
            continue

        decision = spec["decision"]
        if decision not in ALLOWED_DECISIONS:
            raise ValueError(
                f"{args.spec}: invalid decision {decision!r} for "
                f"{queue_row['candidate_id']}"
            )
        stage = spec["screening_stage"] or DEFAULT_STAGE[decision]
        full_text = spec["full_text_checked"] or DEFAULT_FULL_TEXT[decision]
        if stage not in ALLOWED_STAGES:
            raise ValueError(
                f"{args.spec}: invalid stage {stage!r} for "
                f"{queue_row['candidate_id']}"
            )
        if full_text not in ALLOWED_FULL_TEXT:
            raise ValueError(
                f"{args.spec}: invalid full-text state {full_text!r} for "
                f"{queue_row['candidate_id']}"
            )
        canonical_id = spec["canonical_record_id"]
        canonical_decision = ""
        matrix_id = spec["matrix_record_id"]
        if decision == "linked-existing":
            canonical = screening_by_id.get(canonical_id)
            if canonical is None:
                raise ValueError(
                    f"{args.spec}: unknown canonical record {canonical_id!r} "
                    f"for {queue_row['candidate_id']}"
                )
            canonical_decision = canonical["decision"]
            expected_matrix = matrix_by_screening.get(canonical_id, "")
            if matrix_id and matrix_id != expected_matrix:
                raise ValueError(
                    f"{args.spec}: matrix mismatch for {queue_row['candidate_id']}"
                )
            matrix_id = expected_matrix
        elif canonical_id:
            raise ValueError(
                f"{args.spec}: canonical ID is only valid for linked-existing "
                f"({queue_row['candidate_id']})"
            )

        output_rows.append(
            {
                "source_queue_run_id": args.queue_run.name,
                "source_queue_checksums_sha256": checksum_sha256,
                "candidate_id": queue_row["candidate_id"],
                "work_key": queue_row["work_key"],
                "title": queue_row["title"],
                "screening_stage": stage,
                "decision": decision,
                "canonical_record_id": canonical_id,
                "canonical_decision": canonical_decision,
                "matrix_record_id": matrix_id,
                "full_text_checked": full_text,
                "evidence_url": (
                    spec["evidence_url"] or default_evidence_url(queue_row)
                ),
                "evidence_location": (
                    spec["evidence_location"]
                    or DEFAULT_EVIDENCE_LOCATION[decision]
                ),
                "reviewer": "Codex-assisted triage; human confirmation pending",
                "review_date": args.review_date,
                "human_confirmation": "pending",
                "reason": spec["reason"] or DEFAULT_REASON[decision],
            }
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=DECISION_FIELDS, quoting=csv.QUOTE_ALL
        )
        writer.writeheader()
        writer.writerows(output_rows)

    digest = hashlib.sha256(args.output.read_bytes()).hexdigest()
    print(f"queue rows: {len(queue_rows)}")
    print(f"spec rows: {len(spec_rows)}")
    print(f"overlay rows: {len(output_rows)}")
    print(f"output: {args.output}")
    print(f"sha256:{digest}")


if __name__ == "__main__":
    main()
