#!/usr/bin/env python3
"""Download and hash the declared primary-source corpus without overwriting it."""

from __future__ import annotations

import argparse
import csv
import hashlib
import shutil
import subprocess
import urllib.request
from urllib.error import HTTPError, URLError
from datetime import datetime, timezone
from pathlib import Path


USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
MANIFEST_FIELDS = (
    "source_id",
    "title",
    "version",
    "doi",
    "primary_url",
    "local_pdf",
    "local_text",
    "retrieved_at_utc",
    "sha256",
    "text_sha256",
    "bytes",
    "text_bytes",
    "content_type",
    "status",
    "error",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def download_pdf(url: str, timeout: float) -> tuple[bytes, str]:
    """Download a PDF, retrying public repositories that reject named bots."""
    header_sets = (
        {
            "Accept": "application/pdf",
            "User-Agent": USER_AGENT,
        },
        {
            "Accept": "application/pdf",
            "User-Agent": (
                "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"
            ),
        },
        {
            "Accept": "application/pdf",
            "User-Agent": "curl/8.0.1",
        },
    )
    last_error: Exception | None = None
    for headers in header_sets:
        request = urllib.request.Request(url, headers=headers)
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read(), response.headers.get_content_type()
        except HTTPError as error:
            last_error = error
            if error.code not in {403, 404}:
                raise
        except URLError as error:
            last_error = error

    curl = shutil.which("curl")
    if curl:
        completed = subprocess.run(
            [
                curl,
                "--location",
                "--fail",
                "--silent",
                "--show-error",
                "--max-time",
                str(timeout),
                "--header",
                "Accept: application/pdf",
                url,
            ],
            check=True,
            capture_output=True,
        )
        return completed.stdout, "application/pdf"

    if last_error is not None:
        raise last_error
    raise AssertionError("unreachable download retry state")


def read_sources(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    required = {
        "source_id",
        "category",
        "title",
        "version",
        "doi",
        "primary_url",
        "local_filename",
        "notes",
    }
    if set(reader.fieldnames or []) != required:
        raise ValueError(f"{path} must have exactly these columns: {sorted(required)}")
    identifiers = [row["source_id"] for row in rows]
    filenames = [row["local_filename"] for row in rows]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("source_id values must be unique")
    if len(filenames) != len(set(filenames)):
        raise ValueError("local_filename values must be unique")
    return rows


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sources",
        type=Path,
        default=audit_dir / "primary-sources.csv",
        help="primary-source catalogue",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=audit_dir / "data" / "papers",
        help="local PDF and text cache",
    )
    parser.add_argument(
        "--source-ids",
        nargs="+",
        help="optional subset of source IDs",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="download timeout in seconds",
    )
    parser.add_argument(
        "--no-text",
        action="store_true",
        help="do not run pdftotext",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    sources_path = arguments.sources.resolve()
    output_dir = arguments.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    sources = read_sources(sources_path)
    if arguments.source_ids:
        requested = set(arguments.source_ids)
        known = {source["source_id"] for source in sources}
        unknown = requested - known
        if unknown:
            raise ValueError(f"unknown source IDs: {sorted(unknown)}")
        sources = [source for source in sources if source["source_id"] in requested]

    manifest_rows: list[dict[str, str]] = []
    for source in sources:
        pdf_path = output_dir / source["local_filename"]
        text_path = pdf_path.with_suffix(".txt")
        row = {
            "source_id": source["source_id"],
            "title": source["title"],
            "version": source["version"],
            "doi": source["doi"],
            "primary_url": source["primary_url"],
            "local_pdf": str(pdf_path.relative_to(output_dir)),
            "local_text": "",
            "retrieved_at_utc": "",
            "sha256": "",
            "text_sha256": "",
            "bytes": "",
            "text_bytes": "",
            "content_type": "",
            "status": "",
            "error": "",
        }
        try:
            if pdf_path.exists():
                row["status"] = "existing"
            else:
                payload, row["content_type"] = download_pdf(
                    source["primary_url"], arguments.timeout
                )
                if not payload.startswith(b"%PDF-"):
                    raise ValueError(
                        "response does not start with a PDF signature"
                    )
                with pdf_path.open("xb") as handle:
                    handle.write(payload)
                row["status"] = "downloaded"
            if not arguments.no_text:
                if not text_path.exists():
                    subprocess.run(
                        ["pdftotext", "-layout", str(pdf_path), str(text_path)],
                        check=True,
                    )
                row["local_text"] = str(text_path.relative_to(output_dir))
                row["text_sha256"] = sha256(text_path)
                row["text_bytes"] = str(text_path.stat().st_size)
            row["retrieved_at_utc"] = utc_now()
            row["sha256"] = sha256(pdf_path)
            row["bytes"] = str(pdf_path.stat().st_size)
            if not row["content_type"]:
                row["content_type"] = "application/pdf"
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
