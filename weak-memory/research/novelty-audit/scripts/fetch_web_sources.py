#!/usr/bin/env python3
"""Download, extract, and checksum declared primary HTML sources."""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import urllib.request
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path


USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
SOURCE_FIELDS = (
    "source_id",
    "title",
    "document_date",
    "primary_url",
    "local_filename",
    "notes",
)
MANIFEST_FIELDS = (
    "source_id",
    "title",
    "document_date",
    "primary_url",
    "local_html",
    "local_text",
    "retrieved_at_utc",
    "html_sha256",
    "text_sha256",
    "bytes",
    "content_type",
    "status",
    "error",
)
BLOCK_TAGS = {
    "address",
    "article",
    "aside",
    "blockquote",
    "br",
    "dd",
    "div",
    "dl",
    "dt",
    "figcaption",
    "figure",
    "footer",
    "h1",
    "h2",
    "h3",
    "h4",
    "h5",
    "h6",
    "header",
    "hr",
    "li",
    "main",
    "nav",
    "ol",
    "p",
    "pre",
    "section",
    "table",
    "td",
    "th",
    "tr",
    "ul",
}
SKIP_TAGS = {"script", "style", "noscript"}


class TextExtractor(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self.skip_depth = 0

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        del attrs
        tag = tag.casefold()
        if tag in SKIP_TAGS:
            self.skip_depth += 1
        elif not self.skip_depth and tag in BLOCK_TAGS:
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        tag = tag.casefold()
        if tag in SKIP_TAGS and self.skip_depth:
            self.skip_depth -= 1
        elif not self.skip_depth and tag in BLOCK_TAGS:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if not self.skip_depth:
            self.parts.append(data)

    def text(self) -> str:
        lines = []
        for line in "".join(self.parts).splitlines():
            normalized = re.sub(r"\s+", " ", line).strip()
            if normalized:
                lines.append(normalized)
        return "\n".join(lines) + "\n"


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def read_sources(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    if tuple(reader.fieldnames or ()) != SOURCE_FIELDS:
        raise ValueError(
            f"{path} must have exactly these columns: {SOURCE_FIELDS}"
        )
    identifiers = [row["source_id"] for row in rows]
    filenames = [row["local_filename"] for row in rows]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("source_id values must be unique")
    if len(filenames) != len(set(filenames)):
        raise ValueError("local_filename values must be unique")
    if any(not filename.endswith((".html", ".htm")) for filename in filenames):
        raise ValueError("every local_filename must be an HTML filename")
    return rows


def extract_text(payload: bytes) -> bytes:
    parser = TextExtractor()
    parser.feed(payload.decode("utf-8", errors="replace"))
    parser.close()
    return parser.text().encode("utf-8")


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sources",
        type=Path,
        default=audit_dir / "standards-history-sources.csv",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=audit_dir / "data" / "standards",
    )
    parser.add_argument("--source-ids", nargs="+")
    parser.add_argument("--timeout", type=float, default=60.0)
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    sources = read_sources(arguments.sources.resolve())
    if arguments.source_ids:
        requested = set(arguments.source_ids)
        known = {source["source_id"] for source in sources}
        unknown = requested - known
        if unknown:
            raise ValueError(f"unknown source IDs: {sorted(unknown)}")
        sources = [
            source
            for source in sources
            if source["source_id"] in requested
        ]

    output_dir = arguments.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_rows: list[dict[str, str]] = []
    for source in sources:
        html_path = output_dir / source["local_filename"]
        text_path = html_path.with_suffix(".txt")
        row = {
            "source_id": source["source_id"],
            "title": source["title"],
            "document_date": source["document_date"],
            "primary_url": source["primary_url"],
            "local_html": html_path.name,
            "local_text": text_path.name,
            "retrieved_at_utc": "",
            "html_sha256": "",
            "text_sha256": "",
            "bytes": "",
            "content_type": "",
            "status": "",
            "error": "",
        }
        try:
            if html_path.exists():
                payload = html_path.read_bytes()
                row["status"] = "existing"
                row["content_type"] = "text/html"
            else:
                request = urllib.request.Request(
                    source["primary_url"],
                    headers={
                        "Accept": "text/html,application/xhtml+xml",
                        "User-Agent": USER_AGENT,
                    },
                )
                with urllib.request.urlopen(
                    request,
                    timeout=arguments.timeout,
                ) as response:
                    payload = response.read()
                    row["content_type"] = (
                        response.headers.get_content_type()
                    )
                if "html" not in row["content_type"]:
                    raise ValueError(
                        "response is not declared as HTML: "
                        f"{row['content_type']}"
                    )
                html_path.write_bytes(payload)
                row["status"] = "downloaded"

            text_payload = (
                text_path.read_bytes()
                if text_path.exists()
                else extract_text(payload)
            )
            if not text_path.exists():
                text_path.write_bytes(text_payload)
            row["retrieved_at_utc"] = utc_now()
            row["html_sha256"] = sha256_bytes(payload)
            row["text_sha256"] = sha256_bytes(text_payload)
            row["bytes"] = str(len(payload))
        except Exception as error:
            row["status"] = "failed"
            row["error"] = f"{type(error).__name__}: {error}"
        manifest_rows.append(row)
        print(f"{source['source_id']}: {row['status']}")

    manifest_path = output_dir / f"manifest-{run_id()}.csv"
    with manifest_path.open("x", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=MANIFEST_FIELDS)
        writer.writeheader()
        writer.writerows(manifest_rows)
    print(f"manifest: {manifest_path}")
    failures = sum(row["status"] == "failed" for row in manifest_rows)
    print(f"failures: {failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
