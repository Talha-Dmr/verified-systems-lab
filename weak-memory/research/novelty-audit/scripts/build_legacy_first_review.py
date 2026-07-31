#!/usr/bin/env python3
"""Materialize the independently reviewed first legacy-queue slice.

The constants below are the final human-assisted classifications for physical
CSV lines 2--390 of the immutable 20260731T024138Z citation queue.  The script
binds them back to the queue metadata, validates the complete partition and
declared category counts, and refuses to overwrite an existing output.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
from collections import Counter
from pathlib import Path


QUEUE_SHA256 = "83ab9a60cfe14199b1b2c1896798bea5a9519fe5cd6ea085accbdffeb3c40778"
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

GROUPS = {
    "linked-existing": """
        CG1163 CG0014 CG0064 CG0263 CG0456 CG0496 CG1028 CG0026 CG0075
        CG0228 CG0773 CG0826 CG0057 CG0119 CG0125 CG0208 CG0473 CG0537
        CG0687 CG0729 CG0736 CG0815 CG0028 CG0062 CG0104 CG0160 CG0195
        CG0199 CG0238 CG0291 CG0353 CG0427 CG0434 CG0451 CG0593 CG0672
        CG0715 CG0812 CG0825 CG0828 CG0910 CG0912 CG0915 CG0927 CG0958
        CG0974 CG0985 CG0986 CG1004 CG1010 CG1051 CG1056 CG1058 CG0112
        CG0465 CG0498 CG0575 CG0681 CG0703 CG0719 CG0819 CG0923 CG1111
        CG0010 CG0070 CG0126 CG0133 CG0387 CG0535 CG0579 CG0590 CG0739
        CG0791 CG0827 CG0907 CG0961 CG0982 CG0989 CG0257 CG0331 CG0341
        CG0654 CG0689 CG0727 CG0840 CG1041
    """,
    "exclude-duplicate": """
        CG1097 CG1077 CG1031 CG1023 CG1081 CG0924 CG1100 CG1102 CG1113
        CG1130 CG0850 CG0957 CG0975 CG0976 CG0998 CG1030 CG1045 CG1063
        CG1069 CG1114 CG1115 CG1117 CG1120 CG1154 CG1075 CG1142 CG0006
        CG0012
    """,
    "exclude-topic": """
        CG0021 CG0921 CG0617 CG0623 CG0647 CG0682 CG0710 CG0711 CG0754
        CG0769 CG0778 CG0780 CG0142 CG0211 CG0242 CG0243 CG0244 CG0269
        CG0357 CG0504 CG0553 CG0555 CG0644 CG0666 CG0779 CG0801 CG0811
        CG0997 CG1006 CG1011 CG1036 CG1043 CG0008 CG0027 CG0043 CG0045
        CG0052 CG0080 CG0081 CG0084 CG0088 CG0092 CG0097 CG0098 CG0130
        CG0165 CG0173 CG0182 CG0188 CG0202 CG0221 CG0310 CG0311 CG0312
        CG0320 CG0337 CG0343 CG0347 CG0361 CG0364 CG0369 CG0370 CG0379
        CG0390 CG0428 CG0464 CG0468 CG0475 CG0488 CG0514 CG0586 CG0591
        CG0651 CG0694 CG0720 CG0735 CG0744 CG0757 CG0813 CG0853 CG0856
        CG0859 CG0877 CG0891 CG0892 CG0914 CG0939 CG0940 CG0965 CG0978
        CG1022 CG1029 CG1046 CG1053 CG1141 CG0011 CG0018
    """,
    "exclude-secondary": """
        CG0033 CG0424 CG0580 CG0973 CG0999 CG1093 CG0042 CG0106 CG0132
        CG0150 CG0161 CG0267 CG0304 CG0339 CG0409 CG0450 CG0835 CG0842
        CG0979 CG0981 CG0984 CG1002 CG1066 CG1128 CG1155 CG1156 CG0002
    """,
    "include-closest": """
        CG0020 CG0169 CG0251 CG0280 CG1018 CG0233 CG0430 CG0547 CG0610
        CG0752 CG0771 CG0894 CG0972 CG1062 CG0001 CG0003 CG0007
    """,
    "include-context": """
        CG0005 CG0118 CG0174 CG0477 CG0562 CG0585 CG0721 CG0059 CG0085
        CG0258 CG0367 CG0492 CG0500 CG0506 CG0516 CG0657 CG0723 CG0741
        CG0768 CG0897 CG0991 CG1003 CG0031 CG0060 CG0065 CG0074 CG0082
        CG0093 CG0262 CG0308 CG0315 CG0322 CG0325 CG0346 CG0368 CG0397
        CG0398 CG0425 CG0517 CG0643 CG0691 CG0899 CG0962 CG0970 CG0993
        CG1007 CG1013 CG1025 CG1027 CG1059
    """,
    "include-adjacent": """
        CG1055 CG0009 CG0276 CG0292 CG0295 CG0326 CG0611 CG0645 CG0678
        CG0685 CG0706 CG0722 CG0762 CG0767 CG0805 CG0864 CG0937 CG1032
        CG0079 CG0136 CG0177 CG0231 CG0255 CG0260 CG0302 CG0334 CG0335
        CG0358 CG0384 CG0429 CG0435 CG0474 CG0476 CG0485 CG0491 CG0508
        CG0566 CG0568 CG0631 CG0653 CG0656 CG0663 CG0718 CG0755 CG0843
        CG0862 CG0865 CG0916 CG0931 CG0934 CG0990 CG0995 CG1021 CG1033
        CG1035 CG1158 CG1160 CG0016 CG0022 CG0163 CG0167 CG0227 CG0293
        CG0342 CG0352 CG0354 CG0396 CG0459 CG0582 CG0596 CG0619 CG0804
        CG0831 CG0838 CG0848 CG0887 CG0932 CG0951 CG1042 CG0017 CG0275
        CG0876 CG0004 CG0015
    """,
}

LINKED = {
    "CG1163": "S03",
    "CG0014": "S04",
    "CG0064": "S64",
    "CG0263": "S52",
    "CG0456": "A32",
    "CG0496": "S39",
    "CG1028": "S20",
    "CG0026": "S06",
    "CG0075": "S65",
    "CG0228": "S66",
    "CG0773": "S67",
    "CG0826": "S37",
    "CG0057": "S68",
    "CG0119": "S69",
    "CG0125": "S70",
    "CG0208": "S62",
    "CG0473": "S50",
    "CG0537": "S71",
    "CG0687": "S72",
    "CG0729": "S21",
    "CG0736": "S58",
    "CG0815": "S55",
    "CG0028": "S73",
    "CG0062": "S74",
    "CG0104": "A33",
    "CG0160": "S75",
    "CG0195": "S76",
    "CG0199": "S54",
    "CG0238": "S49",
    "CG0291": "S77",
    "CG0353": "S51",
    "CG0427": "S41",
    "CG0434": "A30",
    "CG0451": "A31",
    "CG0593": "S53",
    "CG0672": "S78",
    "CG0715": "S79",
    "CG0812": "S80",
    "CG0825": "S56",
    "CG0828": "S81",
    "CG0910": "S54",
    "CG0912": "S47",
    "CG0915": "S82",
    "CG0927": "S83",
    "CG0958": "S36",
    "CG0974": "S84",
    "CG0985": "S36",
    "CG0986": "S48",
    "CG1004": "S19",
    "CG1010": "S46",
    "CG1051": "S41",
    "CG1056": "S85",
    "CG1058": "S17",
    "CG0112": "S109",
    "CG0465": "S154",
    "CG0498": "S90",
    "CG0575": "S176",
    "CG0681": "S177",
    "CG0703": "S91",
    "CG0719": "S110",
    "CG0819": "S114",
    "CG0923": "S92",
    "CG1111": "S183",
    "CG0010": "S93",
    "CG0070": "S140",
    "CG0126": "S93",
    "CG0133": "A26",
    "CG0387": "S94",
    "CG0535": "S146",
    "CG0579": "S161",
    "CG0590": "S148",
    "CG0739": "A24",
    "CG0791": "S34",
    "CG0827": "S24",
    "CG0907": "S40",
    "CG0961": "S23",
    "CG0982": "S20/PA16",
    "CG0989": "S42",
    "CG0257": "S84",
    "CG0331": "S119",
    "CG0341": "S170",
    "CG0654": "S120",
    "CG0689": "S99",
    "CG0727": "S100",
    "CG0840": "S138",
    "CG1041": "S44/PA36",
}

EXPECTED_COUNTS = {
    "linked-existing": 86,
    "exclude-duplicate": 28,
    "exclude-topic": 97,
    "exclude-secondary": 27,
    "include-closest": 17,
    "include-context": 50,
    "include-adjacent": 84,
}


def identifiers(value: str) -> list[str]:
    return value.split()


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
            / "20260731T024138Z"
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
            / "legacy-first-review-20260731T024138Z.csv"
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
    reviewed = queue[:389]

    decisions: dict[str, str] = {}
    for decision, raw_ids in GROUPS.items():
        for candidate_id in identifiers(raw_ids):
            if candidate_id in decisions:
                raise ValueError(f"duplicate classification: {candidate_id}")
            decisions[candidate_id] = decision

    reviewed_ids = {row["candidate_id"] for row in reviewed}
    if set(decisions) != reviewed_ids:
        raise ValueError(
            "classification partition mismatch: "
            f"missing={sorted(reviewed_ids - set(decisions))}, "
            f"extra={sorted(set(decisions) - reviewed_ids)}"
        )
    if Counter(decisions.values()) != Counter(EXPECTED_COUNTS):
        raise ValueError(
            f"classification counts mismatch: {Counter(decisions.values())}"
        )
    if set(LINKED) != {
        candidate_id
        for candidate_id, decision in decisions.items()
        if decision == "linked-existing"
    }:
        raise ValueError("linked-existing mapping coverage mismatch")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        for index, row in enumerate(reviewed, start=2):
            writer.writerow(
                {
                    "line": int(row["candidate_id"][2:]),
                    "physical_line": index,
                    "candidate_id": row["candidate_id"],
                    "work_key": row["work_key"],
                    "title": row["title"],
                    "decision": decisions[row["candidate_id"]],
                    "canonical": LINKED.get(row["candidate_id"], ""),
                    "doi": row["doi"],
                    "open_pdf": "",
                }
            )

    print(f"rows: {len(reviewed)}")
    print(f"counts: {dict(sorted(Counter(decisions.values()).items()))}")
    print(f"output: {args.output}")
    print(f"sha256:{sha256(args.output)}")


if __name__ == "__main__":
    main()
