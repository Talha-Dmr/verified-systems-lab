#!/usr/bin/env python3
"""Build the reviewed first slice of the legacy-promotions citation queue.

The queue is immutable and checksum-bound.  Previously screened work is
reconciled against frozen canonical and decision snapshots; all remaining
records have explicit reviewer dispositions below.  The output contains data
rows 1--660 (physical CSV lines 2--661), in queue order.
"""

from __future__ import annotations

import csv
import hashlib
import re
import unicodedata
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
QUEUE = (
    ROOT
    / "data"
    / "citation-screening-runs"
    / "20260731T092100Z-legacy-promotions-union"
    / "citation-screening-queue.csv"
)
CANONICAL = (
    ROOT
    / "data"
    / "citation-runs"
    / "20260731T091700Z-legacy-promotions-semanticscholar"
    / "inputs"
    / "screening.csv"
)
OVERLAYS = (
    ROOT / "citation-screening-decisions-20260731T024138Z.csv",
    ROOT / "citation-screening-decisions-20260731T033000Z.csv",
    ROOT / "citation-screening-decisions-20260731T035500Z.csv",
    ROOT / "citation-screening-decisions-20260731T052500Z.csv",
    ROOT / "citation-screening-decisions-20260731T054900Z.csv",
    ROOT / "citation-screening-decisions-20260731T061500Z.csv",
    ROOT / "citation-screening-decisions-20260731T073200Z.csv",
    ROOT / "citation-screening-decisions.csv",
)
OUTPUT = (
    ROOT
    / "data"
    / "decision-specs"
    / "legacy-promotions-first-review-20260731T092100Z.csv"
)

EXPECTED_SHA256 = {
    QUEUE: "6d3fa534af413d6280bba82e7e3ef34400dbe7d590bd604e956add8d0928257b",
    CANONICAL: "c80d35d046e322eebb677934af57c63d3181cc35f9eef15cd93671443599bb33",
    OVERLAYS[0]: "874f126636c72a2c731e37ee7946608c6e3f9e42b79c06f1aad30d4f897b53a1",
    OVERLAYS[1]: "69a6e37b052450df4cc1e7bc2edf6b422eeb0b61e21de7e3830f6dcfd8ab0843",
    OVERLAYS[2]: "58376eadf41976e47d5383dbaedc9794895f811cb541b86e78c17291fc4c3e8d",
    OVERLAYS[3]: "2bb48e3f29b195b506f0ee11236329a6e8079ca0e66ab6615bd1c8755e90adc1",
    OVERLAYS[4]: "a3617fe924581b21cfdb192f848609dafa1bf1859d00f115f96eeca25942dce2",
    OVERLAYS[5]: "4a83c995e6007798db33b1a0a72d897dd2b3831fffaed489b438fab69d435025",
    OVERLAYS[6]: "74103ab6cb7f99d7e68ce2d623921b5b7888301cb1802ee23b9a77e8e6fcaab1",
    OVERLAYS[7]: "2b80636ccf4cf8d8e8e127792b31071b5735c38b62910d0e9502dbdd5d66eeb9",
}

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

ALLOWED = {
    "linked-existing",
    "exclude-duplicate",
    "exclude-secondary",
    "exclude-topic",
    "include-context",
    "include-adjacent",
    "include-closest",
}


def ids(raw: str) -> set[str]:
    return set(raw.split())


# These are records not already resolved by the frozen canonical/decision
# snapshots.  Every omitted unresolved record is an explicit exclude-topic.
MANUAL = {
    "include-adjacent": ids(
        """
        CG0087 CG1264 CG0737 CG1380 CG0032 CG0054 CG0063 CG0259 CG0282
        CG0311 CG0700 CG0801 CG1188 CG1202 CG1243 CG1254 CG1385 CG1488
        CG0042 CG0058 CG0279 CG0307 CG0556 CG0730 CG0768 CG0914 CG0923
        CG1028 CG1107 CG1135 CG1138 CG1294 CG1482 CG1593 CG1865 CG1908
        CG1961 CG0040 CG0056 CG0200 CG0244 CG0290 CG0297 CG0305 CG0313
        CG0387 CG0440 CG0532 CG0557 CG0564 CG0588 CG0702 CG0731 CG0941
        CG0971 CG1006 CG1025 CG1071 CG1124 CG1162 CG1208 CG1329 CG1361
        CG1457 CG1514 CG1521 CG1592 CG1614 CG1649 CG1707 CG1708 CG1746
        CG1774 CG1792 CG1822 CG1860 CG1942 CG0029 CG0033 CG0051 CG0190
        CG0754 CG0817 CG0818 CG1029 CG1064 CG1103 CG1109 CG1134 CG1164
        CG1226 CG1234 CG1247 CG1287 CG1315 CG1485 CG0025 CG0068 CG0069
        CG0080 CG0089 CG0142 CG0198 CG0213 CG0215
        """
    ),
    "include-context": ids(
        """
        CG0076 CG0111 CG0036 CG0234 CG0064 CG0654 CG1557 CG1886 CG0028
        CG0581 CG0656 CG0760 CG0984 CG1065 CG1092 CG1241 CG1279 CG0007
        CG0044 CG0084 CG0116 CG0147 CG0150 CG0160 CG0174 CG0175 CG0225
        CG0263 CG0264 CG0322 CG0468 CG1261 CG1568 CG1578 CG1922 CG0024
        CG0026 CG0027 CG0031 CG0037 CG0049 CG0053 CG0059 CG0065 CG0077
        CG0078 CG0097 CG0098 CG0101 CG0117 CG0118 CG0119 CG0131 CG0134
        CG0135 CG0140 CG0152 CG0164 CG0166 CG0171 CG0172 CG0173 CG0178
        CG0179 CG0180 CG0182 CG0184 CG0185 CG0202 CG0204 CG0212 CG0216
        """
    ),
    "exclude-secondary": ids(
        """
        CG0095 CG0103 CG1003 CG1066 CG1589 CG1658 CG1851 CG1888 CG1911
        CG0342 CG0742 CG1442 CG1476 CG1550 CG1570 CG1711 CG1950 CG1951
        CG1954 CG1955 CG1372 CG1612 CG1804 CG0022 CG0071 CG0075 CG0183
        CG0186 CG0208 CG0217 CG0102 CG0219 CG0479 CG1266 CG1699
        """
    ),
    "exclude-duplicate": ids(
        """
        CG1912 CG0052 CG1035 CG1095 CG1677 CG1715 CG1806 CG1890
        CG1491 CG1590 CG1862 CG1642 CG1744 CG1771 CG1758 CG1900 CG1914
        CG1176 CG0019 CG0066
        """
    ),
}

MANUAL_LINKED = {
    "CG1682": "S137",
    "CG1889": "S210",
}

MANUAL_OVERRIDES = {
    # Full-text theorem audit: the POPL 2018 paper jointly verifies
    # linearizability and PSF/PDF for exact-CAS partial Treiber stacks.
    "CG1155": "include-closest",
}

PRIORITY = {
    "linked-existing": 7,
    "include-closest": 6,
    "include-adjacent": 5,
    "include-context": 4,
    "exclude-secondary": 3,
    "exclude-duplicate": 2,
    "exclude-topic": 1,
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_title(value: str) -> str:
    ascii_value = (
        unicodedata.normalize("NFKD", value or "")
        .encode("ascii", "ignore")
        .decode("ascii")
        .lower()
    )
    return re.sub(r"[^a-z0-9]+", "", ascii_value)


def keys(row: dict[str, str]) -> tuple[tuple[str, str], ...]:
    values = (
        ("work", (row.get("work_key") or "").strip().lower()),
        ("doi", (row.get("doi") or "").strip().lower()),
        ("title", normalize_title(row.get("title") or "")),
    )
    return tuple(item for item in values if item[1])


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def main() -> None:
    for path, expected in EXPECTED_SHA256.items():
        actual = sha256(path)
        if actual != expected:
            raise ValueError(f"checksum mismatch for {path}: {actual} != {expected}")
    if OUTPUT.exists():
        raise ValueError(f"refusing to overwrite existing output: {OUTPUT}")

    manual_owner: dict[str, str] = {}
    for decision, members in MANUAL.items():
        if decision not in ALLOWED:
            raise ValueError(f"invalid manual decision: {decision}")
        for candidate_id in members:
            previous = manual_owner.setdefault(candidate_id, decision)
            if previous != decision:
                raise ValueError(
                    f"manual classification conflict for {candidate_id}: "
                    f"{previous} / {decision}"
                )

    canonical_index: dict[tuple[str, str], list[dict[str, str]]] = {}
    for row in read_csv(CANONICAL):
        for key in keys(row):
            canonical_index.setdefault(key, []).append(row)

    prior_index: dict[tuple[str, str], list[dict[str, str]]] = {}
    for path in OVERLAYS:
        for row in read_csv(path):
            for key in keys(row):
                prior_index.setdefault(key, []).append(row)

    queue = read_csv(QUEUE)
    reviewed = queue[:660]
    if len(reviewed) != 660:
        raise ValueError(f"expected 660 reviewed rows, got {len(reviewed)}")

    output: list[dict[str, str]] = []
    resolved_by_snapshot: set[str] = set()
    for index, row in enumerate(reviewed, start=1):
        candidate_id = row["candidate_id"]
        canonical_matches: dict[str, dict[str, str]] = {}
        for key in keys(row):
            for match in canonical_index.get(key, []):
                canonical_matches[match["record_id"]] = match

        decision = ""
        canonical = ""
        if canonical_matches:
            canonical = sorted(canonical_matches)[0]
            decision = "linked-existing"
            resolved_by_snapshot.add(candidate_id)
        else:
            prior_matches: dict[
                tuple[str, str, str], dict[str, str]
            ] = {}
            for key in keys(row):
                for match in prior_index.get(key, []):
                    identity = (
                        match["candidate_id"],
                        match["decision"],
                        match["canonical_record_id"],
                    )
                    prior_matches[identity] = match
            if prior_matches:
                best = max(
                    prior_matches.values(),
                    key=lambda match: PRIORITY[match["decision"]],
                )
                decision = best["decision"]
                canonical = best["canonical_record_id"]
                if (
                    decision == "include-closest"
                    and candidate_id not in MANUAL_LINKED
                ):
                    raise ValueError(
                        f"unreconciled prior closest record: {candidate_id}"
                    )
                resolved_by_snapshot.add(candidate_id)

        if candidate_id in MANUAL_OVERRIDES:
            decision = MANUAL_OVERRIDES[candidate_id]
            canonical = ""
        elif candidate_id in MANUAL_LINKED:
            decision = "linked-existing"
            canonical = MANUAL_LINKED[candidate_id]
        elif candidate_id in manual_owner:
            if candidate_id in resolved_by_snapshot:
                raise ValueError(
                    f"manual/snapshot overlap for {candidate_id}: "
                    f"{manual_owner[candidate_id]} / {decision}"
                )
            decision = manual_owner[candidate_id]
            canonical = ""
        elif not decision:
            decision = "exclude-topic"

        if decision not in ALLOWED:
            raise ValueError(f"invalid decision for {candidate_id}: {decision}")
        if (decision == "linked-existing") != bool(canonical):
            raise ValueError(
                f"canonical-link invariant failed for {candidate_id}: "
                f"{decision} / {canonical}"
            )

        open_pdf = ""
        if (
            decision.startswith("include-") or decision == "linked-existing"
        ) and row["work_key"].startswith("arxiv:"):
            open_pdf = (
                "https://arxiv.org/pdf/" + row["work_key"].split(":", 1)[1]
            )

        output.append(
            {
                "line": str(int(candidate_id[2:])),
                "physical_line": str(index + 1),
                "candidate_id": candidate_id,
                "work_key": row["work_key"],
                "title": row["title"],
                "decision": decision,
                "canonical": canonical,
                "doi": row["doi"],
                "open_pdf": open_pdf,
            }
        )

    if [row["candidate_id"] for row in output] != [
        row["candidate_id"] for row in reviewed
    ]:
        raise ValueError("output order differs from queue order")
    if [int(row["physical_line"]) for row in output] != list(range(2, 662)):
        raise ValueError("physical-line sequence mismatch")
    if any(set(row) != set(FIELDS) for row in output):
        raise ValueError("output field mismatch")

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(output)

    print(f"wrote {len(output)} rows to {OUTPUT}")
    print(f"counts: {dict(sorted(Counter(r['decision'] for r in output).items()))}")
    print(f"sha256: {sha256(OUTPUT)}")


if __name__ == "__main__":
    main()
