#!/usr/bin/env python3
"""Materialize the reviewed tail of the final-four citation queue.

The reviewed slice is data rows 121--179 (physical CSV lines 122--180)
of the checksum-bound 20260731T101000Z union queue.  Decisions combine
exact-identity reconciliation with targeted primary-source inspection of
plausible weak-memory, liveness, linearizability, and mechanization leads.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path


QUEUE_SHA256 = "935f05748f1260a1b88e5a213f13d73cf9f545bb7e799a9512a865b76d26e1c3"
START_DATA_ROW = 121
END_DATA_ROW = 179
EXPECTED_ROWS = 59
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
DECISIONS = {
    "linked-existing",
    "exclude-duplicate",
    "exclude-secondary",
    "exclude-topic",
    "include-context",
    "include-adjacent",
    "include-closest",
}

# Each target data row is explicitly adjudicated.  Blank canonical values are
# intentional; candidate-ID canonicals name exact aliases in this queue, while
# S-identifiers name already-established canonical ledger records.
REVIEW = {
    121: ("exclude-secondary", ""),
    122: ("include-adjacent", ""),
    123: ("include-adjacent", ""),
    124: ("include-adjacent", ""),
    125: ("exclude-topic", ""),
    126: ("include-adjacent", ""),
    127: ("include-adjacent", ""),
    128: ("linked-existing", "S53"),
    129: ("exclude-duplicate", ""),
    130: ("exclude-secondary", ""),
    131: ("linked-existing", "S19"),
    132: ("exclude-duplicate", "CG0106"),
    133: ("exclude-topic", ""),
    134: ("exclude-topic", ""),
    135: ("exclude-duplicate", "CG0114"),
    136: ("exclude-topic", ""),
    137: ("exclude-secondary", ""),
    138: ("exclude-duplicate", "CG0107"),
    139: ("include-adjacent", ""),
    140: ("exclude-topic", ""),
    141: ("include-context", ""),
    142: ("exclude-topic", ""),
    143: ("exclude-topic", ""),
    144: ("linked-existing", "S22"),
    145: ("include-adjacent", ""),
    146: ("exclude-topic", ""),
    147: ("include-adjacent", ""),
    148: ("exclude-topic", ""),
    149: ("include-context", ""),
    150: ("include-adjacent", ""),
    151: ("exclude-duplicate", "CG0139"),
    152: ("exclude-topic", ""),
    153: ("exclude-topic", ""),
    154: ("exclude-duplicate", "CG0144"),
    155: ("exclude-topic", ""),
    156: ("exclude-topic", ""),
    157: ("exclude-topic", ""),
    158: ("exclude-secondary", ""),
    159: ("include-context", ""),
    160: ("linked-existing", "S104"),
    161: ("exclude-topic", ""),
    162: ("exclude-secondary", ""),
    163: ("include-adjacent", ""),
    164: ("include-adjacent", ""),
    165: ("include-context", ""),
    166: ("exclude-secondary", ""),
    167: ("exclude-topic", ""),
    168: ("exclude-secondary", ""),
    169: ("exclude-secondary", ""),
    170: ("exclude-secondary", ""),
    171: ("include-adjacent", ""),
    172: ("linked-existing", "S22"),
    173: ("exclude-secondary", ""),
    174: ("exclude-secondary", ""),
    175: ("linked-existing", "S210"),
    176: ("linked-existing", "S227"),
    177: ("linked-existing", "S230"),
    178: ("linked-existing", "S229"),
    179: ("linked-existing", "S228"),
}

OPEN_PDF = {
    122: "https://iacoma.cs.uiuc.edu/iacoma-papers/isca13_2.pdf",
    123: "https://csaws.cs.technion.ac.il/~anastas/anchor-spaa13.pdf",
    126: "https://www.cs.tau.ac.il/~mad/publications/asplos2014-ffwsq.pdf",
    128: "https://flint.cs.yale.edu/flint/publications/rgsimt-tr.pdf",
    131: "https://cs.nju.edu.cn/xyfeng/research/publications/POPL2016.pdf",
    139: "https://arxiv.org/pdf/1904.07136",
    141: "https://arxiv.org/pdf/2011.11763",
    144: "https://iris-project.org/pdfs/2024-popl-trillium.pdf",
    159: "https://arxiv.org/pdf/1810.09611",
    160: "https://drops.dagstuhl.de/storage/00lipics/lipics-vol134-ecoop2019/LIPIcs.ECOOP.2019.19/LIPIcs.ECOOP.2019.19.pdf",
    163: "https://bfischer.pages.cs.sun.ac.za/pdfs/fmcad-16.preprint.pdf",
    164: "https://www.cs.ncl.ac.uk/publications/trs/papers/1425.pdf",
    172: "https://iris-project.org/pdfs/2024-popl-trillium.pdf",
    175: "https://opus.bibliothek.uni-augsburg.de/opus4/files/38931/38931.pdf",
    177: "https://hongjin-liang.github.io/papers/popl18-partial.pdf",
    178: "https://plax-lab.github.io/publications/fntpl20/fntpl20-progress.pdf",
    179: "https://www.cs.tau.ac.il/~mad/publications/asplos2015-tbtso.pdf",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "final-four-tail-review-20260731T101000Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError(f"queue checksum mismatch: {args.queue}")

    with args.queue.open(newline="", encoding="utf-8") as stream:
        queue = list(csv.DictReader(stream))
    if len(queue) < END_DATA_ROW:
        raise ValueError(f"queue has only {len(queue)} data rows")
    if set(REVIEW) != set(range(START_DATA_ROW, END_DATA_ROW + 1)):
        raise ValueError("review map does not exactly cover the requested slice")
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    output_rows: list[dict[str, str | int]] = []
    for data_row in range(START_DATA_ROW, END_DATA_ROW + 1):
        source = queue[data_row - 1]
        decision, canonical = REVIEW[data_row]
        if decision not in DECISIONS:
            raise ValueError(f"row {data_row}: invalid decision {decision}")
        if decision == "linked-existing" and not canonical.startswith("S"):
            raise ValueError(f"row {data_row}: linked record lacks S canonical")
        output_rows.append(
            {
                "line": data_row,
                "physical_line": data_row + 1,
                "candidate_id": source["candidate_id"],
                "work_key": source["work_key"],
                "title": source["title"],
                "decision": decision,
                "canonical": canonical,
                "doi": source["doi"],
                "open_pdf": OPEN_PDF.get(data_row, ""),
            }
        )

    if len(output_rows) != EXPECTED_ROWS:
        raise ValueError(f"expected {EXPECTED_ROWS} rows, got {len(output_rows)}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(output_rows)

    counts = Counter(row["decision"] for row in output_rows)
    print(f"wrote {len(output_rows)} rows to {args.output}")
    print("counts: " + ", ".join(f"{key}={counts[key]}" for key in sorted(counts)))
    print(f"sha256: {sha256(args.output)}")


if __name__ == "__main__":
    main()
