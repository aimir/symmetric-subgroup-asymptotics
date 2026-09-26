#!/usr/bin/env python3
"""Extract one bounded action-hint record for the admitted 16T832 pilot.

No group computation or Lean emission occurs. Required --source b16_832 and
--output /absolute/private/path.json; use --write or read-only --check.
The output discards all normal-subgroup data and keeps only original child
labels and original point conjugators. These are untrusted search hints,
never a proof of subgroup equality or action coverage.

Immutable ceilings: 8 MiB compressed input, 128 MiB decompressed prefix,
1 MiB header, 2 MiB per materialized record, 800 records, 5 seconds, 32 KiB
output, 8 child hints. Oversized records are skipped in at most 64 KiB chunks
under the same total prefix/time caps, without JSON parsing. An oversized
selected record therefore cannot be accepted. Limits may only be lowered. Time checks are cooperative,
not OS preemption. All writes are atomic and outside the repository.
The pinned input hash comes from the existing finite-witness manifest.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True
import argparse
import gzip
import hashlib
import io
import json
import math
import os
from pathlib import Path
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
INPUT = ROOT / "certificates/data/binary_menu.jsonl.gz"
SOURCE = "b16_832"
INPUT_SHA = "a28f0c47797feb254647ffa2dd345c4c565266859eed8968a06a3db6c2ba888a"
HEADER_SHA = "3e137e152a68aa3a3ac2f745f866082a2cb16f9d6d31bf1a09acfbb73cbdf1a1"
NODE_SHA = "0e40491ba44ca59bc1a51fdbcf8dc3b39932bf4e400275bb2b0a6b566aa5e4cd"
MAX_INPUT = 8 * 1024 * 1024
# The prefix ceiling bounds cumulative decompression. Materialized records
# and skipped-record chunks have separate, smaller bounds below.
MAX_PREFIX = 128 * 1024 * 1024
MAX_HEADER = 1024 * 1024
MAX_RECORD = 2 * 1024 * 1024
MAX_RECORDS = 800
MAX_SECONDS = 5.0
MAX_OUTPUT = 32 * 1024
MAX_EDGES = 8


class Refused(Exception):
    pass


def require(ok: bool, message: str) -> None:
    if not ok:
        raise Refused(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def read_bounded(path: Path, limit: int) -> bytes:
    require(path.is_file() and not path.is_symlink(), f"not a regular input: {path}")
    with path.open("rb") as handle:
        data = handle.read(limit + 1)
    require(len(data) <= limit, f"input exceeds byte ceiling: {path}")
    return data


def private_json_path(raw: str) -> Path:
    path = Path(raw).expanduser()
    require(path.is_absolute() and path.suffix == ".json", "need an absolute .json output")
    require(not path.is_symlink(), "refusing symbolic-link output")
    path = path.resolve()
    require(not path.is_relative_to(ROOT.resolve()), "audit output must be outside repository")
    require(path.parent.is_dir(), "output parent must already exist")
    return path


def atomic_write(path: Path, data: bytes) -> None:
    require(not path.is_symlink(), "refusing symbolic-link output")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix=f".{path.name}.", dir=path.parent,
                                         delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def permutation(row) -> bool:
    return (isinstance(row, list) and len(row) == 16
            and all(type(x) is int for x in row)
            and sorted(row) == list(range(1, 17)))


def validate_edges(action: dict, nodes: dict) -> list[dict]:
    require(action.get("kind") == "action" and action.get("id") == SOURCE,
            "wrong selected action record")
    edges = action.get("action_children")
    require(isinstance(edges, list) and len(edges) <= MAX_EDGES, "too many/malformed child hints")
    result = []
    for edge in edges:
        require(isinstance(edge, dict), "malformed child hint")
        target, conjugator = edge.get("target"), edge.get("conjugator")
        require(isinstance(target, str) and target in nodes and nodes[target].get("degree") == 16,
                "child target is not an original degree-sixteen label")
        require(permutation(conjugator), "invalid original-point conjugator")
        result.append({"target": target, "conjugator": conjugator})
    return result


def extract(packed: bytes, *, prefix_limit: int, record_limit: int,
            record_count: int, time_check) -> dict:
    require(digest(packed) == INPUT_SHA, "pinned compressed catalogue hash mismatch")
    with gzip.GzipFile(fileobj=io.BytesIO(packed), mode="rb") as stream:
        header = stream.readline(min(MAX_HEADER, prefix_limit) + 1)
        require(0 < len(header) <= min(MAX_HEADER, prefix_limit) and header.endswith(b"\n"),
                "bounded catalogue header is incomplete")
        require(digest(header) == HEADER_SHA, "pinned header hash mismatch")
        decoded = json.loads(header)
        nodes = {node["id"]: node for node in decoded["nodes"]}
        require(SOURCE in nodes and digest(canonical(nodes[SOURCE])) == NODE_SHA,
                "original selected generator record changed")
        source_generators = nodes[SOURCE].get("generators")
        require(isinstance(source_generators, list) and len(source_generators) == 2
                and all(permutation(g) for g in source_generators), "expected two original generators")
        consumed = len(header)
        skipped_records = skipped_bytes = 0
        for number in range(1, record_count + 1):
            time_check()
            remaining = prefix_limit - consumed
            require(remaining > 0,
                    f"prefix ceiling before record {number}: consumed={consumed}, "
                    f"prefix_limit={prefix_limit}")
            limit = min(record_limit, remaining)
            line = stream.readline(limit + 1)
            require(bool(line),
                    f"EOF before selected action at record {number}: consumed={consumed}")
            if len(line) > limit:
                limiting = "prefix" if remaining <= record_limit else "record"
                if limiting == "prefix":
                    raise Refused(
                        f"prefix ceiling at record {number}: prefix_before={consumed}, "
                        f"record_bytes_at_least={len(line)}, record_limit={record_limit}, "
                        f"prefix_remaining={remaining}, prefix_limit={prefix_limit}, "
                        f"oversized_records_skipped={skipped_records}")
                # This whole line is ineligible for selection. Discard its
                # bounded prefix and scan only to its newline, never parsing
                # its normal data. If it were the selected action, no later
                # success is fabricated: that action must still be found as
                # a complete bounded record or the extraction is refused.
                skipped_records += 1
                consumed += len(line)
                skipped_bytes += len(line)
                ended = line.endswith(b"\n")
                del line
                while not ended:
                    time_check()
                    remaining = prefix_limit - consumed
                    require(remaining > 0,
                            f"prefix ceiling while skipping oversized record {number}: "
                            f"consumed={consumed}, prefix_limit={prefix_limit}, "
                            f"oversized_records_skipped={skipped_records}")
                    chunk = stream.readline(min(64 * 1024, remaining))
                    require(bool(chunk), f"EOF inside oversized record {number}")
                    consumed += len(chunk)
                    skipped_bytes += len(chunk)
                    ended = chunk.endswith(b"\n")
                continue
            require(line.endswith(b"\n"),
                    f"unterminated record {number}: prefix_before={consumed}, "
                    f"record_bytes={len(line)}")
            consumed += len(line)
            record = json.loads(line)
            require(isinstance(record, dict), "malformed catalogue record")
            if record.get("kind") != "action" or record.get("id") != SOURCE:
                continue
            edges = validate_edges(record, nodes)
            time_check()
            return {"schema": "selected-schreier-action-hints-v1", "source": SOURCE,
                    "compressed_input_sha256": INPUT_SHA, "header_sha256": HEADER_SHA,
                    "source_node_sha256": NODE_SHA, "selected_record_sha256": digest(line),
                    "decompressed_prefix_bytes": consumed, "records_scanned": number,
                    "oversized_records_skipped": skipped_records,
                    "oversized_record_bytes_skipped": skipped_bytes,
                    "action": {"kind": "action", "id": SOURCE, "action_children": edges},
                    "target_node_sha256": {e["target"]: digest(canonical(nodes[e["target"]]))
                                           for e in edges},
                    "scope": "untrusted original-point search hints; no order or coverage premise"}
    raise Refused(f"record-count ceiling {record_count} reached before selected action; "
                  f"consumed_prefix_bytes={consumed}, prefix_limit={prefix_limit}, "
                  f"oversized_records_skipped={skipped_records}; "
                  "oversized selected records are not admitted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, choices=(SOURCE,))
    parser.add_argument("--output", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-prefix-bytes", type=int, default=MAX_PREFIX)
    parser.add_argument("--max-record-bytes", type=int, default=MAX_RECORD)
    parser.add_argument("--max-records", type=int, default=MAX_RECORDS)
    parser.add_argument("--max-seconds", type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    require(1 <= args.max_prefix_bytes <= MAX_PREFIX, "prefix limit exceeds immutable ceiling")
    require(1 <= args.max_record_bytes <= MAX_RECORD, "record limit exceeds immutable ceiling")
    require(1 <= args.max_records <= MAX_RECORDS, "record-count limit exceeds immutable ceiling")
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= MAX_SECONDS,
            "time limit exceeds immutable ceiling")
    output = private_json_path(args.output)
    started = time.monotonic()
    def time_check():
        require(time.monotonic() - started <= args.max_seconds, "selected extraction time ceiling reached")
    own_path = Path(__file__).resolve()
    own = read_bounded(own_path, MAX_HEADER)
    packed = read_bounded(INPUT, MAX_INPUT)
    report = extract(packed, prefix_limit=args.max_prefix_bytes,
                     record_limit=args.max_record_bytes, record_count=args.max_records,
                     time_check=time_check)
    result = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    require(len(result) <= MAX_OUTPUT, "selected-hint output exceeds 32 KiB")
    require(read_bounded(own_path, MAX_HEADER) == own, "extractor changed during run")
    require(read_bounded(INPUT, MAX_INPUT) == packed, "compressed input changed during run")
    time_check()
    if args.check:
        require(read_bounded(output, MAX_OUTPUT) == result, "selected-record bytes differ")
    else:
        atomic_write(output, result)
    print(json.dumps({"source": SOURCE, "sha256": digest(result), "bytes": len(result),
                      "prefix_bytes": report["decompressed_prefix_bytes"],
                      "records": report["records_scanned"],
                      "oversized_records_skipped": report["oversized_records_skipped"],
                      "edges": len(report["action"]["action_children"]),
                      "mode": "checked" if args.check else "written"}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, ValueError, TypeError, KeyError) as error:
        raise SystemExit(f"selected record refused: {error}") from None
