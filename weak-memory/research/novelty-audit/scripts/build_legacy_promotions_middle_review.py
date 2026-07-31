#!/usr/bin/env python3
"""Materialize the reviewed middle slice of the legacy-promotions queue.

The slice is data rows 661--1319 of the immutable
20260731T092100Z-legacy-promotions-union queue.  Exact identities already
classified in the checksum-pinned legacy overlay are reused; all newly exposed
works are classified by the explicit sets below, with the remaining works
explicitly materialized as ``exclude-topic`` in the output.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import unicodedata
from collections import Counter
from pathlib import Path


QUEUE_SHA256 = "6d3fa534af413d6280bba82e7e3ef34400dbe7d590bd604e956add8d0928257b"
LEGACY_SHA256 = "874f126636c72a2c731e37ee7946608c6e3f9e42b79c06f1aad30d4f897b53a1"
START = 660
STOP = 1319
FIELDS = (
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
VOCABULARY = {
    "linked-existing",
    "exclude-duplicate",
    "exclude-secondary",
    "exclude-topic",
    "include-context",
    "include-adjacent",
    "include-closest",
}


def identifiers(value: str) -> set[str]:
    return set(value.split())


# Exact DOI/title or publication-lineage reconciliation against screening.csv.
LINKED = {
    "CG0240": "A26",
    "CG0251": "S31",
    "CG0285": "S180",
    "CG0332": "S181",
    "CG0347": "S182",
    "CG0386": "S156",
    "CG0483": "S170",
    "CG0540": "S142",
    "CG0574": "S119",
    "CG0600": "S40",
    "CG0637": "A32",
    "CG0640": "S94",
    "CG0662": "S159",
    "CG0689": "S143",
    "CG0827": "S129",
    "CG0848": "S95",
    "CG0907": "S42",
    "CG0909": "S10",
    "CG0922": "S147",
    "CG0942": "S131",
    "CG0991": "S172",
    "CG0997": "S176",
    "CG1000": "S172",
    "CG1030": "S116",
    "CG1042": "S183",
    "CG1046": "S184",
    "CG1049": "S186",
    "CG1058": "S183",
    "CG1061": "S185",
    "CG1069": "S186",
    "CG1077": "S205",
    "CG1078": "S185",
    "CG1082": "S132",
    "CG1083": "S191",
    "CG1086": "S192",
    "CG1099": "S19",
    "CG1100": "S192",
}


GROUPS = {
    "include-closest": identifiers(
        """
        CG0553 CG1057
        """
    ),
    "include-adjacent": identifiers(
        """
        CG0223 CG0224 CG0231 CG0232 CG0239 CG0242 CG0243 CG0250 CG0254
        CG0256 CG0278 CG0280 CG0286 CG0287 CG0292 CG0294 CG0304 CG0314
        CG0318 CG0325 CG0329 CG0336 CG0346 CG0361 CG0365 CG0366 CG0371
        CG0376 CG0379 CG0392 CG0396 CG0401 CG0402 CG0404 CG0409 CG0411
        CG0418 CG0422 CG0445 CG0449 CG0459 CG0472 CG0486 CG0490 CG0491
        CG0492 CG0503 CG0504 CG0506 CG0512 CG0519 CG0521 CG0522 CG0525
        CG0528 CG0539 CG0555 CG0558 CG0563 CG0565 CG0572 CG0575 CG0576
        CG0578 CG0589 CG0594 CG0597 CG0598 CG0608 CG0615 CG0646 CG0668
        CG0671 CG0691 CG0703 CG0721 CG0736 CG0767 CG0805 CG0819 CG0820
        CG0832 CG0835 CG0853 CG0916 CG0930 CG0945 CG0947 CG0950 CG0951
        CG0952 CG0969 CG0970 CG0973 CG0977 CG0993 CG0994 CG0996 CG1009
        CG1018 CG1032 CG1038 CG1041 CG1051 CG1060 CG1076 CG1080 CG1090
        CG1091 CG1097 CG1104
        """
    ),
    "include-context": identifiers(
        """
        CG0236 CG0241 CG0249 CG0293 CG0315 CG0326 CG0357 CG0359 CG0360
        CG0390 CG0432 CG0439 CG0494 CG0543 CG0548 CG0562 CG0601 CG0624
        CG0626 CG0629 CG0631 CG0644 CG0648 CG0685 CG0694 CG0761 CG0770
        CG0776 CG0784 CG0808 CG0810 CG0840 CG0843 CG0884 CG0894 CG0896
        CG0902 CG0917 CG0963 CG1081
        """
    ),
    "exclude-secondary": identifiers(
        """
        CG0228 CG0316 CG0319 CG0333 CG0345 CG0382 CG0393 CG0407 CG0430
        CG0435 CG0507 CG0509 CG0510 CG0538 CG0587 CG0595 CG0630 CG0683
        CG0686 CG0687 CG0692 CG0697 CG0716 CG0747 CG0748 CG0831 CG0937
        CG1014
        """
    ),
    "exclude-duplicate": identifiers(
        """
        CG0226 CG0609 CG0891 CG0895 CG0928 CG0940 CG0948 CG0957 CG0958
        CG0967 CG0972 CG0999 CG1001 CG1026 CG1050 CG1079 CG1098 CG1101
        """
    ),
}


OPEN_PDF = {
    "CG1057": "https://www.cs.tau.ac.il/~mad/publications/asplos2015-tbtso.pdf",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_title(value: str) -> str:
    value = unicodedata.normalize("NFKD", value)
    value = value.encode("ascii", "ignore").decode("ascii").lower()
    return re.sub(r"[^a-z0-9]+", " ", value).strip()


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
        "--legacy-overlay",
        type=Path,
        default=root / "citation-screening-decisions-20260731T024138Z.csv",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "legacy-promotions-middle-review-20260731T092100Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError("legacy-promotions citation queue checksum mismatch")
    if sha256(args.legacy_overlay) != LEGACY_SHA256:
        raise ValueError("legacy decision overlay checksum mismatch")
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    with args.queue.open(newline="", encoding="utf-8") as stream:
        queue = list(csv.DictReader(stream))
    reviewed = queue[START:STOP]
    if len(reviewed) != 659:
        raise ValueError(f"expected 659 reviewed rows, found {len(reviewed)}")
    if reviewed[0]["candidate_id"] != "CG0220":
        raise ValueError("unexpected first candidate in reviewed slice")
    if reviewed[-1]["candidate_id"] != "CG1104":
        raise ValueError("unexpected final candidate in reviewed slice")

    with args.legacy_overlay.open(newline="", encoding="utf-8") as stream:
        legacy = list(csv.DictReader(stream))
    legacy_by_work_key = {
        row["work_key"].lower(): row for row in legacy if row["work_key"].strip()
    }
    legacy_by_title = {
        normalize_title(row["title"]): row
        for row in legacy
        if row["title"].strip()
    }

    explicit_membership: dict[str, str] = {}
    for decision, candidate_ids in GROUPS.items():
        if decision not in VOCABULARY:
            raise ValueError(f"invalid decision group: {decision}")
        for candidate_id in candidate_ids:
            if candidate_id in explicit_membership:
                raise ValueError(
                    f"{candidate_id} appears in both "
                    f"{explicit_membership[candidate_id]} and {decision}"
                )
            explicit_membership[candidate_id] = decision

    queue_ids = {row["candidate_id"] for row in reviewed}
    unknown_explicit = set(explicit_membership).difference(queue_ids)
    if unknown_explicit:
        raise ValueError(f"explicit IDs outside reviewed slice: {unknown_explicit}")
    unknown_linked = set(LINKED).difference(queue_ids)
    if unknown_linked:
        raise ValueError(f"linked IDs outside reviewed slice: {unknown_linked}")
    overlap = set(LINKED).intersection(explicit_membership)
    if overlap:
        raise ValueError(f"linked IDs also explicitly classified: {overlap}")

    output_rows: list[dict[str, str | int]] = []
    reused = Counter()
    for line, row in enumerate(reviewed, START + 1):
        candidate_id = row["candidate_id"]
        canonical = LINKED.get(candidate_id, "")
        if canonical:
            decision = "linked-existing"
        else:
            prior = legacy_by_work_key.get(row["work_key"].lower())
            if prior is None and row["title"].strip():
                prior = legacy_by_title.get(normalize_title(row["title"]))
            if prior is not None:
                decision = prior["decision"]
                reused[decision] += 1
            else:
                decision = explicit_membership.get(candidate_id, "exclude-topic")

        if decision not in VOCABULARY:
            raise ValueError(f"invalid decision {decision!r} for {candidate_id}")
        output_rows.append(
            {
                "line": line,
                "physical_line": line + 1,
                "candidate_id": candidate_id,
                "work_key": row["work_key"],
                "title": row["title"],
                "decision": decision,
                "canonical": canonical,
                "doi": row["doi"],
                "open_pdf": OPEN_PDF.get(candidate_id, ""),
            }
        )

    if len(output_rows) != len(reviewed):
        raise ValueError("output row-count mismatch")
    if [row["candidate_id"] for row in output_rows] != [
        row["candidate_id"] for row in reviewed
    ]:
        raise ValueError("candidate order changed")
    for offset, row in enumerate(output_rows, START + 1):
        if row["line"] != offset or row["physical_line"] != offset + 1:
            raise ValueError("line metadata mismatch")
        source = reviewed[offset - START - 1]
        for field in ("candidate_id", "work_key", "title", "doi"):
            if row[field] != source[field]:
                raise ValueError(f"{field} metadata mismatch at line {offset}")
        if row["decision"] == "linked-existing" and not row["canonical"]:
            raise ValueError(f"missing canonical ID for linked row {row['candidate_id']}")
        if row["decision"] != "linked-existing" and row["canonical"]:
            raise ValueError(f"unexpected canonical ID for {row['candidate_id']}")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(output_rows)

    counts = Counter(str(row["decision"]) for row in output_rows)
    print(f"wrote {len(output_rows)} rows to {args.output}")
    print(f"decision counts: {dict(sorted(counts.items()))}")
    print(f"legacy decisions reused before linked overrides: {dict(sorted(reused.items()))}")
    print(f"sha256: {sha256(args.output)}")


if __name__ == "__main__":
    main()
