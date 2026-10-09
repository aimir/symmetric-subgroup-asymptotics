#!/usr/bin/env python3
"""Prepare a bounded manifest or one selected pair-top row for Lean emitters.

The committed alphabet, group rows, and module rows are joined only after
their SHA-256 digests, order, identifiers, and literal ordered generators
have been checked.  This program deliberately has no whole-catalogue Lean
emission mode.  ``manifest`` writes the small catalogue plan; ``selected``
writes one JSON payload from which later normal-word and cyclic-module Lean
chunks can be emitted without reopening the full inputs.

No Lean, GAP, subprocess, or other exporter is invoked here.  Receipts and
selected payloads belong outside the publication repository.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data"
ACTIONS = DATA / "pair_top_actions.json"
GROUPS = DATA / "pair_top_groups.jsonl.gz"
MODULES = DATA / "pair_top_modules.jsonl.gz"

ACTIONS_SHA256 = "0b6faa0cbb65ab790915de720f80ed62676fa8369aa003d3a4aaf209d6fd0493"
GROUPS_SHA256 = "9bbcb02690d8cb6d0e397d3e94dba9613c0f9e503fc3f27e44e1ba45f6817410"
MODULES_SHA256 = "ed80738802abd966f67bc2c1643556e87fd640357f3dcc6518fbbb561522816b"

ACTION_LIMIT = 256 * 1024
COMPRESSED_LIMIT = 256 * 1024
DECOMPRESSED_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 8 * 1024 * 1024
ROW_COUNT = 391

EXPECTED_FAMILIES = {
    "twelve": (301, 12, 24),
    "paired8": (24, 8, 32),
    "zero16": (29, 16, 32),
    "two_affine16": (15, 16, 32),
    "primitive16": (20, 16, 32),
    "paired6": (2, 6, 24),
}
EXPECTED_NORMALS = {
    "twelve": 3914,
    "paired8": 147,
    "zero16": 349,
    "two_affine16": 95,
    "primitive16": 101,
    "paired6": 17,
}
EXPECTED_TWELVE_BRANCHES = {
    "joint": 283,
    "core": 8,
    "ternary": 8,
    "paired": 2,
}


class Refused(ValueError):
    """A bounded-input or semantic pin failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def pinned_bytes(path: Path, limit: int, expected_sha256: str) -> bytes:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected input: {path.name}")
    raw = path.read_bytes()
    require(len(raw) <= limit, f"input ceiling reached: {path.name}")
    require(hashlib.sha256(raw).hexdigest() == expected_sha256,
            f"digest changed: {path.name}")
    return raw


def compressed_rows(path: Path, expected_sha256: str) -> list[dict]:
    compressed = pinned_bytes(path, COMPRESSED_LIMIT, expected_sha256)
    raw = gzip.decompress(compressed)
    require(len(raw) <= DECOMPRESSED_LIMIT,
            f"decompressed input ceiling reached: {path.name}")
    rows = [json.loads(line) for line in raw.splitlines() if line.strip()]
    require(len(rows) == ROW_COUNT, f"row count changed: {path.name}")
    return rows


def joined_rows() -> list[dict]:
    action_data = json.loads(pinned_bytes(
        ACTIONS, ACTION_LIMIT, ACTIONS_SHA256))
    require(action_data.get("schema_version") == 1,
            "unexpected pair-top alphabet schema")
    actions = action_data.get("actions")
    require(isinstance(actions, list) and len(actions) == ROW_COUNT,
            "pair-top action domain changed")
    groups = compressed_rows(GROUPS, GROUPS_SHA256)
    modules = compressed_rows(MODULES, MODULES_SHA256)

    ids = [row.get("id") for row in actions]
    require(len(set(ids)) == ROW_COUNT, "duplicate pair-top action id")
    require([row.get("id") for row in groups] == ids,
            "group rows changed order or domain")
    require([row.get("id") for row in modules] == ids,
            "module rows changed order or domain")

    family_count = Counter(row.get("family") for row in actions)
    require(family_count == Counter({k: v[0] for k, v in EXPECTED_FAMILIES.items()}),
            "pair-top family partition changed")
    normal_count = Counter()
    branch_count = Counter()
    result = []
    for position, (action, group, module) in enumerate(
            zip(actions, groups, modules, strict=True)):
        family = action.get("family")
        require(family in EXPECTED_FAMILIES,
                f"unknown family at row {position}")
        _, degree, width = EXPECTED_FAMILIES[family]
        require(action.get("degree") == degree and
                action.get("original_width") == width,
                f"degree/width mismatch: {action.get('id')}")
        generators = action.get("generators")
        require(generators == group.get("generators") == module.get("generators"),
                f"ordered generators disagree: {action.get('id')}")
        require(module.get("degree") == degree,
                f"module degree disagrees: {action.get('id')}")
        require(isinstance(group.get("normals"), list),
                f"missing normal rows: {action.get('id')}")
        require(isinstance(module.get("numerators"), list),
                f"missing module numerators: {action.get('id')}")
        normal_count[family] += len(group["normals"])
        if family == "twelve":
            branch_count[action.get("branch")] += 1
        result.append({
            "catalogue_position": position,
            "action": action,
            "group": group,
            "module": module,
        })
    require(dict(normal_count) == EXPECTED_NORMALS,
            "pair-top normal totals changed")
    require(dict(branch_count) == EXPECTED_TWELVE_BRANCHES,
            "degree-twelve branch partition changed")
    return result


def manifest(rows: list[dict]) -> dict:
    family_rows = defaultdict(list)
    for row in rows:
        action, group, module = row["action"], row["group"], row["module"]
        family_rows[action["family"]].append({
            "id": action["id"],
            "index": action["index"],
            "branch": action.get("branch"),
            "kappa": action["kappa"],
            "normal_count": len(group["normals"]),
            "module_state_count": len(module["numerators"]),
            "cyclic_count": module["cyclic_count"],
            "section_cap": module["section_cap"],
            "composition_cap": module["composition_cap"],
        })
    return {
        "schema_version": 1,
        "input_sha256": {
            "pair_top_actions.json": ACTIONS_SHA256,
            "pair_top_groups.jsonl.gz": GROUPS_SHA256,
            "pair_top_modules.jsonl.gz": MODULES_SHA256,
        },
        "row_count": ROW_COUNT,
        "family_counts": {k: len(family_rows[k]) for k in EXPECTED_FAMILIES},
        "normal_counts": EXPECTED_NORMALS,
        "twelve_branch_counts": EXPECTED_TWELVE_BRANCHES,
        "lean_targets": {
            "normal_registry": "FiniteNormalStateRegistry.ofWordRegistry",
            "module_registry": "BinaryInvariantCyclicOrbitRegistry",
            "finite_interface": "DegreeTwoPairTopFiniteInterface",
            "universal_boundary": "DegreeTwoPairTopRelativeLiftConclusion",
        },
        "reuse": {
            "paired8": "existing GeneratedPair8/BinaryFiniteEntryCoverage8 top rows",
            "all_families": "shared normal-word and cyclic-module importers",
        },
        "families": dict(family_rows),
    }


def write_json(path: Path, value: object) -> None:
    raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    require(len(raw) <= OUTPUT_LIMIT, "output ceiling reached")
    require(path.parent.exists(), "output parent must already exist")
    path.write_bytes(raw)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("manifest", "selected"), required=True)
    parser.add_argument("--id", help="exact action id for --stage selected")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = joined_rows()
    if args.stage == "manifest":
        require(args.id is None, "--id is only valid for selected output")
        value = manifest(rows)
    else:
        require(args.id is not None, "selected output requires --id")
        matches = [row for row in rows if row["action"]["id"] == args.id]
        require(len(matches) == 1, "selected id is absent or duplicated")
        value = {
            "schema_version": 1,
            "input_sha256": {
                "actions": ACTIONS_SHA256,
                "groups": GROUPS_SHA256,
                "modules": MODULES_SHA256,
            },
            **matches[0],
        }
    write_json(args.output, value)
    print(f"WROTE {args.stage}: {args.output}")


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, EOFError, json.JSONDecodeError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        raise SystemExit(1)
