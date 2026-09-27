#!/usr/bin/env python3
"""Emit one bounded literal action from the cyclic-module c=1 degree-12 slice.

Only transitive actions 12T20, 12T85 and 12T164 are accepted.  Their retained
owner records all have kind ``cyclic_module`` and their actual closures have
orders 36, 144 and 576.  Enumeration aborts before adding row 577, so this
selected producer cannot enter the larger degree-twelve cases or become a
bulk action-table build.

Rows and transition tables are packed into small Nat blocks.  Lean still
checks every decoded transition, predecessor edge, strict permutation code,
and original generator image.  ``--check`` compares bytes without writing;
compilation remains a separate serial ``scripts/check_lean.py`` step.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys
import tempfile
import time

sys.dont_write_bytecode = True

from export_lean_menu_cayley import ROOT, array, emit, table
from export_lean_prime_composition import (
    Budget,
    CertificateError,
    DATA,
    LIMIT_SPECS,
    bounded_file_hash,
    read_selected,
    require,
)

ALLOWED = {20, 85, 164}
ROW_CEILING = 576
OUTPUT_LIMIT = 4 * 1024 * 1024


def image_matrix(generators: list[list[int]]) -> str:
    return array([array(images) for images in generators])


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=int, required=True, choices=sorted(ALLOWED))
    parser.add_argument("--expect-row-sha256", help="Optional exact raw JSONL line hash pin.")
    parser.add_argument("--check", action="store_true",
                        help="Compare the selected output bytes; do not write.")
    parser.add_argument("--max-seconds", type=float, default=30.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= 120,
            "--max-seconds must be finite, positive and at most 120")
    if args.expect_row_sha256 is not None:
        require(re.fullmatch(r"[0-9a-f]{64}", args.expect_row_sha256) is not None,
                "--expect-row-sha256 must be a lowercase SHA256 digest")

    limits = {name: default for name, (default, _ceiling) in LIMIT_SPECS.items()}
    budget = Budget(limits, args.max_seconds, time.monotonic())
    selected = read_selected(12, args.index, budget, args.expect_row_sha256,
                             catalogue="transitive")
    row = selected.value
    require(row.get("owner", {}).get("kind") == "cyclic_module",
            "selected action lost its retained cyclic-module owner witness")
    require(row.get("normal_scope") == "all", "selected row lost its complete normal scope")
    require(isinstance(row.get("generators"), list) and row["generators"],
            "selected row has no literal generators")

    generators = [tuple(value - 1 for value in images) for images in row["generators"]]
    require(all(len(images) == 12 and sorted(images) == list(range(12))
                for images in generators), "selected row contains a malformed permutation")
    cayley = table(generators, 12, max_rows=ROW_CEILING)
    require(1 <= len(cayley["codes"]) <= ROW_CEILING,
            "selected closure escaped its fixed row ceiling")

    label = f"12T{args.index}"
    module_name = f"TernaryOwnerCayley{label}"
    extra_body = f'''/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin {len(generators)}, ∀ x : Fin 12,
    (generators j x).val + 1 =
      (({image_matrix(row["generators"])} : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

'''
    node = {"id": f"b12_{args.index}", "degree": 12, "generators": row["generators"]}
    path, text = emit(
        node,
        module_name=module_name,
        title=f"Literal c=1 high action certificate {label}",
        generated_from=(
            "Generated from certificates/data/primitive_rank.jsonl.gz by "
            "export_lean_c1_degree_twelve.py.\n"
            f"Selected transitive row {selected.line}; raw-line SHA256 "
            f"{selected.line_sha256}."),
        scope_text=(
            "This proves the literal selected action only;\n"
            "high-pair coverage and earlier-owner acceptance remain separate theorems."),
        extra_body=extra_body,
        packed_tables=True,
        max_rows=ROW_CEILING,
    )
    content = text.encode("utf-8")
    require(len(content) <= OUTPUT_LIMIT, "selected Lean output exceeds the fixed byte cap")
    require(bounded_file_hash(DATA, budget) == selected.data_sha256,
            "committed input changed during selected production; no output written")
    budget.time_check()

    if args.check:
        require(path.is_file() and path.read_bytes() == content,
                f"generated selected witness is missing/stale: {path.relative_to(ROOT)}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.is_file() or path.read_bytes() != content:
            temporary_path: Path | None = None
            try:
                with tempfile.NamedTemporaryFile(dir=path.parent, prefix=path.name + ".",
                                                 suffix=".tmp", delete=False) as stream:
                    temporary_path = Path(stream.name)
                    stream.write(content)
                os.replace(temporary_path, path)
            finally:
                if temporary_path is not None and temporary_path.exists():
                    temporary_path.unlink()

    print(json.dumps({
        "path": str(path.relative_to(ROOT)),
        "checked": args.check,
        "source_sha256": hashlib.sha256(content).hexdigest(),
        "selected_line": selected.line,
        "row_sha256": selected.line_sha256,
        "actual_rows": len(cayley["codes"]),
        "output_bytes": len(content),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, EOFError, RecursionError, ValueError,
            json.JSONDecodeError) as error:
        print(f"selected c=1 degree-twelve action: {error}", file=sys.stderr)
        raise SystemExit(2)
