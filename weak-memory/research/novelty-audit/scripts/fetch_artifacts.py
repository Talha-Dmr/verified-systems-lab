#!/usr/bin/env python3
"""Download, verify, and safely extract the declared artifact corpus."""

from __future__ import annotations

import argparse
import csv
import hashlib
import shutil
import stat
import tarfile
import urllib.request
import zipfile
from datetime import datetime, timezone
from pathlib import Path


USER_AGENT = (
    "verified-systems-lab-novelty-audit/1 "
    "(https://github.com/Talha-Dmr/verified-systems-lab)"
)
MANIFEST_FIELDS = (
    "artifact_id",
    "related_record",
    "title",
    "version",
    "archive_url",
    "local_archive",
    "extracted_directory",
    "retrieved_at_utc",
    "expected_checksum",
    "actual_md5",
    "actual_sha256",
    "bytes",
    "file_count",
    "status",
    "error",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def run_id() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def digest(path: Path, algorithm: str) -> str:
    result = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def read_sources(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    required = {
        "artifact_id",
        "related_record",
        "title",
        "version",
        "archive_url",
        "local_filename",
        "expected_checksum",
        "notes",
    }
    if set(reader.fieldnames or []) != required:
        raise ValueError(f"{path} must have exactly these columns: {sorted(required)}")
    identifiers = [row["artifact_id"] for row in rows]
    filenames = [row["local_filename"] for row in rows]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("artifact_id values must be unique")
    if len(filenames) != len(set(filenames)):
        raise ValueError("local_filename values must be unique")
    return rows


def is_zip_symlink(member: zipfile.ZipInfo) -> bool:
    unix_mode = member.external_attr >> 16
    return stat.S_ISLNK(unix_mode)


def validate_archive_target(destination: Path, member_name: str) -> Path:
    root = destination.resolve()
    target = (destination / member_name).resolve()
    if not target.is_relative_to(root):
        raise ValueError(f"unsafe archive path: {member_name!r}")
    return target


def safe_extract_zip(archive: Path, destination: Path) -> None:
    with zipfile.ZipFile(archive) as handle:
        members = handle.infolist()
        for member in members:
            validate_archive_target(destination, member.filename)
            if is_zip_symlink(member):
                raise ValueError(
                    f"symbolic links are not extracted: {member.filename!r}"
                )
        handle.extractall(destination)


def safe_extract_tar(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, mode="r:*") as handle:
        members = handle.getmembers()
        for member in members:
            validate_archive_target(destination, member.name)
            if not (member.isdir() or member.isfile()):
                raise ValueError(
                    "only regular files and directories are extracted: "
                    f"{member.name!r}"
                )
        for member in members:
            target = validate_archive_target(destination, member.name)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = handle.extractfile(member)
            if source is None:
                raise ValueError(
                    f"could not read regular archive member: {member.name!r}"
                )
            with source, target.open("xb") as output:
                shutil.copyfileobj(source, output)


def safe_extract(archive: Path, destination: Path) -> int:
    if destination.exists():
        return sum(path.is_file() for path in destination.rglob("*"))
    destination.mkdir(parents=True, exist_ok=False)
    try:
        if zipfile.is_zipfile(archive):
            safe_extract_zip(archive, destination)
        elif tarfile.is_tarfile(archive):
            safe_extract_tar(archive, destination)
        else:
            raise ValueError("archive is neither ZIP nor supported tar")
        return sum(path.is_file() for path in destination.rglob("*"))
    except Exception:
        for path in sorted(
            destination.rglob("*"), key=lambda value: len(value.parts), reverse=True
        ):
            if path.is_file():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
        destination.rmdir()
        raise


def parse_arguments() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    audit_dir = script_dir.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sources",
        type=Path,
        default=audit_dir / "artifact-sources.csv",
        help="artifact source catalogue",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=audit_dir / "data" / "artifacts",
        help="archive cache and extraction root",
    )
    parser.add_argument(
        "--artifact-ids",
        nargs="+",
        help="optional subset of artifact IDs",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="download timeout in seconds",
    )
    parser.add_argument(
        "--no-extract",
        action="store_true",
        help="verify archives without extracting them",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    sources_path = arguments.sources.resolve()
    output_dir = arguments.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    extraction_root = output_dir / "extracted"
    sources = read_sources(sources_path)
    if arguments.artifact_ids:
        requested = set(arguments.artifact_ids)
        known = {source["artifact_id"] for source in sources}
        unknown = requested - known
        if unknown:
            raise ValueError(f"unknown artifact IDs: {sorted(unknown)}")
        sources = [
            source for source in sources if source["artifact_id"] in requested
        ]

    manifest_rows: list[dict[str, str]] = []
    for source in sources:
        archive = output_dir / source["local_filename"]
        extracted = extraction_root / archive.stem
        row = {
            "artifact_id": source["artifact_id"],
            "related_record": source["related_record"],
            "title": source["title"],
            "version": source["version"],
            "archive_url": source["archive_url"],
            "local_archive": archive.name,
            "extracted_directory": "",
            "retrieved_at_utc": "",
            "expected_checksum": source["expected_checksum"],
            "actual_md5": "",
            "actual_sha256": "",
            "bytes": "",
            "file_count": "",
            "status": "",
            "error": "",
        }
        try:
            if archive.exists():
                row["status"] = "existing"
            else:
                request = urllib.request.Request(
                    source["archive_url"],
                    headers={
                        "User-Agent": USER_AGENT,
                    },
                )
                with urllib.request.urlopen(
                    request, timeout=arguments.timeout
                ) as response:
                    payload = response.read()
                if not (
                    payload.startswith(b"PK")
                    or payload.startswith(b"\x1f\x8b")
                ):
                    raise ValueError(
                        "response does not have a ZIP or gzip signature"
                    )
                with archive.open("xb") as handle:
                    handle.write(payload)
                row["status"] = "downloaded"

            actual_md5 = digest(archive, "md5")
            actual_sha256 = digest(archive, "sha256")
            expected_algorithm, expected_value = source[
                "expected_checksum"
            ].split(":", 1)
            actual_expected = digest(archive, expected_algorithm)
            if actual_expected.lower() != expected_value.lower():
                raise ValueError(
                    f"checksum mismatch: expected {source['expected_checksum']}"
                )
            row.update(
                {
                    "retrieved_at_utc": utc_now(),
                    "actual_md5": actual_md5,
                    "actual_sha256": actual_sha256,
                    "bytes": str(archive.stat().st_size),
                }
            )
            if not arguments.no_extract:
                row["file_count"] = str(safe_extract(archive, extracted))
                row["extracted_directory"] = str(
                    extracted.relative_to(output_dir)
                )
        except Exception as error:
            row["status"] = "failed"
            row["error"] = f"{type(error).__name__}: {error}"
        manifest_rows.append(row)
        print(f"{source['artifact_id']}: {row['status']}")

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
