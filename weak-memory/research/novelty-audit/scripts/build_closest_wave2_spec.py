#!/usr/bin/env python3
"""Materialize the fully reviewed closest-wave-2 decision specification."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path


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


GROUPS = {
    "linked-existing": """
        CG0018 CG0028 CG0051 CG0053 CG0055 CG0060 CG0072 CG0078 CG0088
        CG0093 CG0098 CG0099 CG0118 CG0122 CG0128 CG0141 CG0148 CG0149
        CG0151 CG0152 CG0161 CG0163 CG0176 CG0177 CG0179 CG0184 CG0198
        CG0202 CG0207 CG0210 CG0221 CG0222 CG0225 CG0226 CG0237 CG0238
        CG0239 CG0240 CG0241 CG0242 CG0243 CG0248 CG0257 CG0261 CG0272
        CG0274 CG0307
    """,
    "include-closest": """
        CG0029 CG0039 CG0048 CG0082 CG0095 CG0167 CG0172 CG0206
    """,
    "include-adjacent": """
        CG0007 CG0008 CG0013 CG0015 CG0027 CG0031 CG0032 CG0034 CG0036
        CG0040 CG0054 CG0056 CG0057 CG0059 CG0062 CG0063 CG0064 CG0065
        CG0066 CG0069 CG0070 CG0073 CG0076 CG0079 CG0080 CG0081 CG0083 CG0086
        CG0089 CG0102 CG0109 CG0119 CG0131 CG0132 CG0134 CG0135 CG0144
        CG0145 CG0146 CG0147 CG0153 CG0170 CG0171 CG0175 CG0178 CG0187
        CG0188 CG0192 CG0204 CG0208 CG0216 CG0223 CG0228 CG0229 CG0232
        CG0233 CG0234 CG0236 CG0269 CG0275
    """,
    "include-context": """
        CG0002 CG0003 CG0005 CG0006 CG0011 CG0014 CG0016 CG0024 CG0030
        CG0033 CG0041 CG0047 CG0050 CG0058 CG0061 CG0067 CG0087 CG0092
        CG0104 CG0106 CG0108 CG0110 CG0112 CG0113 CG0114 CG0116 CG0124
        CG0126 CG0138 CG0142 CG0143 CG0150 CG0173 CG0180 CG0182
        CG0189 CG0190 CG0201 CG0213 CG0235 CG0268 CG0292 CG0301 CG0308
        CG0309
    """,
    "exclude-duplicate": """
        CG0001 CG0004 CG0020 CG0023 CG0044 CG0117 CG0123 CG0133 CG0139
        CG0157 CG0158 CG0159 CG0160 CG0168 CG0169 CG0185 CG0186 CG0193
        CG0196 CG0197 CG0209 CG0211 CG0276 CG0277 CG0279 CG0280 CG0282
        CG0283 CG0286 CG0287 CG0288 CG0289 CG0290 CG0294 CG0295 CG0296
        CG0298 CG0300 CG0310 CG0311 CG0312 CG0313
    """,
    "exclude-secondary": """
        CG0010 CG0021 CG0035 CG0037 CG0075 CG0094 CG0219 CG0253 CG0255
        CG0259 CG0260 CG0270 CG0273 CG0278 CG0281 CG0284 CG0285 CG0293
        CG0297 CG0299 CG0303 CG0304 CG0305
    """,
    "exclude-topic": """
        CG0009 CG0012 CG0017 CG0019 CG0022 CG0025 CG0026 CG0038 CG0042
        CG0043 CG0045 CG0046 CG0049 CG0052 CG0068 CG0071 CG0074 CG0077
        CG0084 CG0085 CG0090 CG0091 CG0096 CG0097 CG0100 CG0101 CG0103
        CG0105 CG0107 CG0111 CG0115 CG0120 CG0121 CG0125 CG0127 CG0129
        CG0130 CG0136 CG0137 CG0140 CG0154 CG0155 CG0156 CG0162 CG0164
        CG0165 CG0166 CG0174 CG0181 CG0183 CG0191 CG0194
        CG0195 CG0199 CG0200 CG0203 CG0205 CG0212 CG0214 CG0215 CG0217
        CG0218 CG0220 CG0224 CG0227 CG0230 CG0231 CG0244 CG0245 CG0246
        CG0247 CG0249 CG0250 CG0251 CG0252 CG0254 CG0256 CG0258 CG0262
        CG0263 CG0264 CG0265 CG0266 CG0267 CG0271 CG0291 CG0302 CG0306
    """,
}

LINKED_CANONICAL = {
    "CG0018": "S109",
    "CG0028": "S115",
    "CG0051": "S54",
    "CG0053": "S62",
    "CG0055": "S156",
    "CG0060": "S128",
    "CG0072": "S170",
    "CG0078": "S119",
    "CG0088": "S119",
    "CG0093": "S170",
    "CG0098": "S40",
    "CG0099": "S97",
    "CG0118": "S50",
    "CG0122": "S95",
    "CG0128": "S90",
    "CG0141": "S131",
    "CG0148": "S172",
    "CG0149": "S176",
    "CG0151": "S161",
    "CG0152": "S102",
    "CG0161": "S116",
    "CG0163": "S116",
    "CG0176": "S102",
    "CG0177": "S169",
    "CG0179": "S132",
    "CG0184": "S169",
    "CG0198": "S120",
    "CG0202": "S98",
    "CG0207": "S134",
    "CG0210": "S99",
    "CG0221": "S110",
    "CG0222": "S09",
    "CG0225": "S175",
    "CG0226": "S07",
    "CG0237": "S08",
    "CG0238": "S173",
    "CG0239": "S55",
    "CG0240": "S33",
    "CG0241": "S114",
    "CG0242": "S124",
    "CG0243": "S37",
    "CG0248": "S154",
    "CG0257": "S40",
    "CG0261": "S103",
    "CG0272": "S173",
    "CG0274": "S171",
    "CG0307": "S109",
}


CLOSEST_MATRIX = {
    "CG0029": "PA84",
    "CG0039": "PA85",
    "CG0048": "PA86",
    "CG0082": "PA82",
    "CG0095": "PA83",
    "CG0167": "PA87",
    "CG0172": "PA88",
    "CG0206": "PA81",
}


CLOSEST_EVIDENCE = {
    "CG0029": (
        "https://gpetri.github.io/publis/poling-cav15.pdf",
        "§2; Theorem 1; Treiber and elimination-stack evaluations",
        "Poling automates SC exact-CAS Treiber linearizability for a "
        "most-general client, but proves no weak-memory or progress result.",
    ),
    "CG0039": (
        "https://fpl.cs.depaul.edu/jriely/papers/2018-vmcai.pdf",
        "Theorem 14; Corollary 15; Theorem 16; §4.4",
        "Direct acquire/release Treiber abstraction and composition with "
        "exact CAS; liveness requires a stronger criterion and is not proved.",
    ),
    "CG0048": (
        "https://brijeshdongol.github.io/full-version/IFM-2018-full.pdf",
        "Theorems 7, 16, and 18; §6.2",
        "Direct C11 release/acquire Treiber safety and causal composition; "
        "finite exact-CAS safety only, with no fairness or response theorem.",
    ),
    "CG0082": (
        "https://user.it.uu.se/~bengt/Papers/Full/sas16.pdf",
        "§1; §8 and Figure 6",
        "Automatic parameterized Treiber linearizability for arbitrary "
        "threads and unbounded heap/data under SC exact CAS; safety only.",
    ),
    "CG0095": (
        "https://link.springer.com/content/pdf/10.1007/s10009-022-00648-0.pdf",
        "§9.6 TreiberStack and TreiberStack2; reported FDR checks",
        "Parameterized exact-CAS Treiber safety and selected CSP "
        "deadlock-freedom checks; no RC11 or matching response theorem.",
    ),
    "CG0167": (
        "https://plv.mpi-sws.org/gps/paper.pdf",
        "§3.7 Theorems 1–3; Appendix D.4; Coq development",
        "Coq-checked C11 program-logic soundness and Michael-Scott queue "
        "safety; no Treiber, fairness, genuine weak CAS, or liveness theorem.",
    ),
    "CG0172": (
        "https://www.cs.uni-salzburg.at/~ahaas/papers/POPL15-TSStack.pdf",
        "Theorem 1 and Isabelle development; Theorems 5–6; §9",
        "Mechanized generic stack safety plus handwritten exact-CAS "
        "lock-freedom for a time-stamped stack; not Treiber or weak memory.",
    ),
    "CG0206": (
        "https://plv.mpi-sws.org/yacovet/paper.pdf",
        "§§4–6; Theorem 1; Theorem 6; Coq artifact",
        "Direct RC11 stack safety and composition with partial Coq "
        "mechanization; 'weak stack' is not genuine primitive weak CAS and "
        "no positive liveness theorem is established.",
    ),
}


def identifiers(text: str) -> set[str]:
    return set(text.split())


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
            / "20260731T073200Z-closest-wave2-union"
            / "citation-screening-queue.csv"
        ),
    )
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.output.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.output}")

    decisions: dict[str, str] = {}
    duplicates: list[str] = []
    for decision, raw_ids in GROUPS.items():
        for candidate_id in identifiers(raw_ids):
            if candidate_id in decisions:
                duplicates.append(candidate_id)
            decisions[candidate_id] = decision
    if duplicates:
        raise ValueError(f"duplicate group assignments: {sorted(duplicates)}")

    with args.queue.open(newline="", encoding="utf-8-sig") as stream:
        queue_rows = list(csv.DictReader(stream))
    queue_ids = [row["candidate_id"] for row in queue_rows]
    if len(queue_ids) != len(set(queue_ids)):
        raise ValueError("queue candidate IDs are not unique")
    if set(queue_ids) != set(decisions):
        raise ValueError(
            "decision/queue mismatch: "
            f"decision-only={sorted(set(decisions) - set(queue_ids))}, "
            f"queue-only={sorted(set(queue_ids) - set(decisions))}"
        )
    if set(LINKED_CANONICAL) != identifiers(GROUPS["linked-existing"]):
        raise ValueError("linked-existing canonical map is incomplete")
    if set(CLOSEST_MATRIX) != identifiers(GROUPS["include-closest"]):
        raise ValueError("include-closest matrix map is incomplete")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=SPEC_FIELDS)
        writer.writeheader()
        for candidate_id in queue_ids:
            decision = decisions[candidate_id]
            evidence_url = ""
            evidence_location = ""
            reason = ""
            if candidate_id in CLOSEST_EVIDENCE:
                evidence_url, evidence_location, reason = CLOSEST_EVIDENCE[
                    candidate_id
                ]
            writer.writerow(
                {
                    "candidate_id": candidate_id,
                    "decision": decision,
                    "canonical_record_id": LINKED_CANONICAL.get(
                        candidate_id, ""
                    ),
                    "matrix_record_id": CLOSEST_MATRIX.get(candidate_id, ""),
                    "screening_stage": "",
                    "full_text_checked": "",
                    "evidence_url": evidence_url,
                    "evidence_location": evidence_location,
                    "reason": reason,
                }
            )

    counts = Counter(decisions.values())
    print(f"decision specification: {args.output}")
    print(f"rows: {len(queue_ids)}")
    print(f"counts: {dict(sorted(counts.items()))}")


if __name__ == "__main__":
    main()
