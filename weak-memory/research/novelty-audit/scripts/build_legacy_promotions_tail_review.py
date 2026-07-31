#!/usr/bin/env python3
"""Materialize the reviewed tail of the legacy-promotions citation queue.

The reviewed slice is data rows 1320--1978 (physical CSV lines 1321--1979)
of the checksum-bound 20260731T092100Z union queue.  Exact identities already
screened in the immutable legacy queue inherit that decision unless a manual
override below records a later canonical link, duplicate identity, or a
decision made from primary-source inspection.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path


QUEUE_SHA256 = "6d3fa534af413d6280bba82e7e3ef34400dbe7d590bd604e956add8d0928257b"
START_DATA_ROW = 1320
END_DATA_ROW = 1978
EXPECTED_ROWS = 659
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
REVIEW_FIELDS = FIELDS
DECISIONS = {
    "linked-existing",
    "exclude-duplicate",
    "exclude-secondary",
    "exclude-topic",
    "include-context",
    "include-adjacent",
    "include-closest",
}

# Manual decisions made after title/metadata screening and targeted primary-
# source inspection.  Everything not inherited or listed here is an explicit
# exclude-topic decision in the output.
GROUPS = {
    "exclude-duplicate": """
        CG1127 CG1128 CG1139 CG1140 CG1193 CG1203 CG1230 CG1349 CG1369
        CG1378 CG1528 CG1529 CG1573 CG1602 CG1625 CG1629 CG1650 CG1672
        CG1674 CG1675 CG1688 CG1697 CG1729 CG1818 CG1832 CG1835 CG1848
        CG1855 CG1903 CG1926 CG1927
        CG1928 CG1934 CG1935 CG1936 CG1937 CG1938 CG1939 CG1940 CG1941
        CG1943 CG1959 CG1972 CG1973 CG1974 CG1975 CG1976
    """,
    "exclude-secondary": """
        CG1420 CG1440 CG1443 CG1447 CG1449 CG1455 CG1456 CG1458 CG1459
        CG1462 CG1463 CG1466 CG1467 CG1473 CG1483 CG1489 CG1511 CG1523 CG1524
        CG1525 CG1526 CG1527 CG1531 CG1532 CG1533 CG1534 CG1536 CG1538
        CG1540 CG1544 CG1547 CG1549 CG1553 CG1555 CG1560 CG1561 CG1562
        CG1563 CG1564 CG1569 CG1579 CG1580 CG1584 CG1587 CG1588 CG1601
        CG1619 CG1630 CG1632 CG1633 CG1635 CG1638 CG1639 CG1643 CG1647
        CG1654 CG1660 CG1673 CG1679 CG1681 CG1687 CG1698 CG1701 CG1713
        CG1732 CG1736 CG1740 CG1743 CG1748 CG1760 CG1763 CG1767 CG1788
        CG1793 CG1798 CG1799 CG1800 CG1808 CG1820 CG1824
        CG1837 CG1844 CG1845 CG1846 CG1861 CG1869 CG1872 CG1875 CG1879
        CG1880 CG1902 CG1907 CG1920 CG1921 CG1924 CG1944 CG1946
        CG1952 CG1953 CG1956 CG1957 CG1960 CG1963 CG1964 CG1966 CG1968
        CG1969 CG1970 CG1977
    """,
    "include-context": """
        CG1106 CG1118 CG1187 CG1256 CG1269 CG1360 CG1362 CG1386 CG1394
        CG1508 CG1575 CG1583 CG1605 CG1651 CG1809 CG1849 CG1882
    """,
    "include-adjacent": """
        CG1123 CG1141 CG1144 CG1151 CG1154 CG1156 CG1173 CG1181 CG1183
        CG1191 CG1211 CG1215 CG1224 CG1227 CG1231 CG1233 CG1242 CG1244
        CG1245 CG1253 CG1268 CG1278 CG1296 CG1298 CG1305 CG1314 CG1322
        CG1326 CG1338 CG1340 CG1345 CG1355 CG1376 CG1379 CG1392 CG1396
        CG1404 CG1405 CG1409 CG1410 CG1415 CG1425 CG1454 CG1471 CG1477
        CG1479 CG1481 CG1486 CG1487 CG1492 CG1494 CG1496 CG1497 CG1501
        CG1506 CG1510 CG1515 CG1518 CG1537 CG1541 CG1543 CG1572 CG1596
        CG1610 CG1622 CG1644 CG1667 CG1668 CG1680 CG1683 CG1689 CG1690
        CG1705 CG1706 CG1709 CG1720 CG1723 CG1725 CG1727 CG1728 CG1734
        CG1738 CG1754 CG1756 CG1776 CG1779 CG1789 CG1827 CG1831
        CG1836 CG1838 CG1864 CG1868 CG1876 CG1905 CG1906 CG1910 CG1930
    """,
    "include-closest": """
        CG1441
    """,
}

# Current canonical records.  These take precedence over inherited decisions,
# including the 30 seeds that constitute the queue's final rows.
LINKED = {
    "CG0003": "S211",
    "CG0016": "S212",
    "CG0023": "S213",
    "CG0246": "S214",
    "CG0248": "S215",
    "CG0303": "S198",
    "CG0368": "S216",
    "CG0375": "S217",
    "CG0384": "S218",
    "CG0399": "S219",
    "CG0415": "S202",
    "CG0425": "S220",
    "CG0431": "S221",
    "CG0444": "S199",
    "CG0495": "S222",
    "CG0498": "S200",
    "CG0520": "S223",
    "CG0554": "S210",
    "CG0619": "S224",
    "CG0635": "S225",
    "CG0711": "S203",
    "CG0938": "S204",
    "CG1059": "S205",
    "CG1119": "S133",
    "CG1153": "S120",
    "CG1161": "S149",
    "CG1163": "S150",
    "CG1196": "S226",
    "CG1284": "S206",
    "CG1316": "S207",
    "CG1370": "S29",
    "CG1448": "S208",
    "CG1503": "S197",
    "CG1504": "S190",
    "CG1505": "S92",
    "CG1655": "S105",
    "CG1685": "S172",
    "CG1847": "S28",
    "CG1915": "S201",
    "CG1916": "S209",
    "CG1917": "S196",
    "CG1925": "S196",
    "CG1933": "S196",
    "CG1949": "S196",
    "CG1958": "S196",
    "CG1962": "S196",
    "CG1965": "S210",
    "CG1967": "S210",
    "CG1971": "S196",
    "CG1978": "S210",
}

OPEN_PDF = {
    "CG1441": "https://cs.nju.edu.cn/hongjin/papers/journal/fntpl20-progress.pdf",
}


def identifiers(value: str) -> list[str]:
    return value.split()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_title(value: str) -> str:
    value = unicodedata.normalize("NFKD", value or "")
    value = value.encode("ascii", "ignore").decode("ascii").lower()
    return re.sub(r"[^a-z0-9]+", " ", value).strip()


def read_csv(path: Path, expected_fields: tuple[str, ...] | None = None) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if expected_fields is not None and tuple(reader.fieldnames or ()) != expected_fields:
            raise ValueError(
                f"{path}: expected fields {expected_fields}, got {reader.fieldnames}"
            )
        rows = list(reader)
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        raise ValueError(f"{path}: malformed row width")
    return rows


def inherited_decisions(
    legacy_queue: list[dict[str, str]],
    legacy_reviews: list[dict[str, str]],
    reviewed: list[dict[str, str]],
) -> dict[str, tuple[str, str]]:
    """Return decisions for unambiguous exact identities in the old review."""
    by_candidate = {row["candidate_id"]: row for row in legacy_reviews}
    if set(by_candidate) != {row["candidate_id"] for row in legacy_queue}:
        raise ValueError("legacy queue/review candidate coverage mismatch")

    indexes: dict[str, defaultdict[str, list[dict[str, str]]]] = {
        "work_key": defaultdict(list),
        "doi": defaultdict(list),
        "title": defaultdict(list),
    }
    for row in legacy_queue:
        indexes["work_key"][row["work_key"].lower()].append(row)
        if row["doi"]:
            indexes["doi"][row["doi"].lower()].append(row)
        if row["title"]:
            indexes["title"][normalized_title(row["title"])].append(row)

    inherited: dict[str, tuple[str, str]] = {}
    for row in reviewed:
        matches: list[dict[str, str]] = []
        keys = (
            ("work_key", row["work_key"].lower()),
            ("doi", row["doi"].lower()),
            ("title", normalized_title(row["title"])),
        )
        for field, value in keys:
            if value:
                matches.extend(indexes[field].get(value, []))
        unique_ids = list(dict.fromkeys(match["candidate_id"] for match in matches))
        if len(unique_ids) == 1:
            old = by_candidate[unique_ids[0]]
            inherited[row["candidate_id"]] = (
                old["decision"],
                old["canonical"].split("/", 1)[0],
            )
    return inherited


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
        "--legacy-queue",
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
        "--legacy-reviews",
        nargs=3,
        type=Path,
        default=[
            root / "data" / "decision-specs" / "legacy-first-review-20260731T024138Z.csv",
            root / "data" / "decision-specs" / "legacy-middle-review-20260731T024138Z.csv",
            root / "data" / "decision-specs" / "legacy-tail-review-20260731T024138Z.csv",
        ],
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            root
            / "data"
            / "decision-specs"
            / "legacy-promotions-tail-review-20260731T092100Z.csv"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if sha256(args.queue) != QUEUE_SHA256:
        raise ValueError("legacy-promotions citation queue checksum mismatch")
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    queue = read_csv(args.queue)
    reviewed = queue[START_DATA_ROW - 1 : END_DATA_ROW]
    if len(reviewed) != EXPECTED_ROWS:
        raise ValueError(f"review slice row-count mismatch: {len(reviewed)}")

    legacy_queue = read_csv(args.legacy_queue)
    legacy_reviews = [
        row
        for path in args.legacy_reviews
        for row in read_csv(path, REVIEW_FIELDS)
    ]
    inherited = inherited_decisions(legacy_queue, legacy_reviews, reviewed)

    decisions = {
        row["candidate_id"]: inherited.get(
            row["candidate_id"], ("exclude-topic", "")
        )[0]
        for row in reviewed
    }
    canonicals = {
        candidate_id: canonical
        for candidate_id, (decision, canonical) in inherited.items()
        if decision == "linked-existing" and canonical
    }

    manual_ids: set[str] = set()
    for decision, raw_ids in GROUPS.items():
        if decision not in DECISIONS:
            raise ValueError(f"invalid decision group: {decision}")
        for candidate_id in identifiers(raw_ids):
            if candidate_id in manual_ids:
                raise ValueError(f"duplicate manual classification: {candidate_id}")
            manual_ids.add(candidate_id)
            decisions[candidate_id] = decision
            canonicals.pop(candidate_id, None)

    reviewed_ids = {row["candidate_id"] for row in reviewed}
    if not manual_ids <= reviewed_ids:
        raise ValueError(f"manual IDs outside slice: {sorted(manual_ids - reviewed_ids)}")
    if not set(LINKED) <= reviewed_ids:
        raise ValueError(f"linked IDs outside slice: {sorted(set(LINKED) - reviewed_ids)}")
    for candidate_id, canonical in LINKED.items():
        decisions[candidate_id] = "linked-existing"
        canonicals[candidate_id] = canonical

    if set(decisions) != reviewed_ids:
        raise ValueError("decision coverage mismatch")
    if any(decision not in DECISIONS for decision in decisions.values()):
        raise ValueError("invalid decision in final partition")
    linked_ids = {
        candidate_id
        for candidate_id, decision in decisions.items()
        if decision == "linked-existing"
    }
    if set(canonicals) != linked_ids:
        raise ValueError(
            "canonical mapping mismatch: "
            f"missing={sorted(linked_ids - set(canonicals))}, "
            f"extra={sorted(set(canonicals) - linked_ids)}"
        )
    if {
        row["candidate_id"] for row in reviewed if row["is_existing_seed"] == "yes"
    } - linked_ids:
        raise ValueError("an existing seed is not linked to its canonical record")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        for data_row, row in enumerate(reviewed, start=START_DATA_ROW):
            writer.writerow(
                {
                    "line": int(row["candidate_id"][2:]),
                    "physical_line": data_row + 1,
                    "candidate_id": row["candidate_id"],
                    "work_key": row["work_key"],
                    "title": row["title"],
                    "decision": decisions[row["candidate_id"]],
                    "canonical": canonicals.get(row["candidate_id"], ""),
                    "doi": row["doi"],
                    "open_pdf": OPEN_PDF.get(row["candidate_id"], ""),
                }
            )

    output = read_csv(args.output, FIELDS)
    if len(output) != EXPECTED_ROWS:
        raise ValueError("written review row-count mismatch")
    for expected_data_row, (review, source) in enumerate(
        zip(output, reviewed, strict=True), start=START_DATA_ROW
    ):
        if review["physical_line"] != str(expected_data_row + 1):
            raise ValueError("written physical-line mismatch")
        for field in ("candidate_id", "work_key", "title", "doi"):
            if review[field] != source[field]:
                raise ValueError(
                    f"written metadata mismatch at {expected_data_row}: {field}"
                )

    counts = Counter(row["decision"] for row in output)
    print(f"rows: {len(output)}")
    print(f"inherited exact identities: {len(inherited)}")
    print(f"counts: {dict(sorted(counts.items()))}")
    print(f"output: {args.output}")
    print(f"sha256:{sha256(args.output)}")


if __name__ == "__main__":
    main()
