#!/usr/bin/env python3
"""Export one row binding while reusing an already checked grouped top.

The representative row pays for conjugacy classes and the full normal lattice.
For another row with the identical literal top this exporter parses only its
stored local kernel, quotient, cosets, induced generators, and binary basis.
It checks those fields against the top's literal Cayley rows and copies the
previously checked top fields into the ordinary selected-binding schema.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import tempfile

import export_frames8_selected_binding_python as selected
from prepare_frames8_grouped_certificate_staged import (
    ASSEMBLED_SCHEMA, OUTPUT_LIMIT, read,
)


def permutation_rows(values, width: int):
    return [selected.permutation(x, width) for x in values]


def rows(values, width: int):
    return [[x + 1 for x in selected.permutation(value, width)]
            for value in values]


def export(row_index: int, top: dict) -> dict:
    raw = selected.SOURCE.read_bytes()
    selected.require(len(raw) <= selected.SOURCE_LIMIT,
                     "bindings source ceiling reached")
    selected.require(__import__("hashlib").sha256(raw).hexdigest() ==
                     selected.SOURCE_SHA256, "bindings source digest changed")
    assignments = selected.Parser(raw.decode()).assignments()
    tops = assignments["FrameEightTops"]
    bindings = assignments["FrameEightBindings"]
    selected.require(0 <= row_index < len(bindings), "binding row out of range")
    binding = bindings[row_index]
    selected.require(isinstance(binding, list) and len(binding) == 7,
                     "invalid selected binding shape")
    top_number, kernel, stabilizer, local_images, cosets, induced, basis = binding
    selected.require(top_number - 1 == top["top_index"],
                     "row does not use the grouped top")
    top_source = tops[top_number - 1]
    top_generators = [selected.permutation(x, 8) for x in top_source]
    selected.require([[x + 1 for x in g] for g in top_generators] ==
                     top["generators"], "literal top generators changed")

    cayley_rows = [tuple(x - 1 for x in g) for g in top["cayley"]["rows"]]
    top_set = set(cayley_rows)
    selected.require(len(top_set) == top["top_order"], "invalid grouped Cayley rows")
    stabilizer_rows = permutation_rows(stabilizer, 8)
    stabilizer_group = selected.generated_subgroup(
        stabilizer_rows, 8, top["top_order"] + 1)
    literal_stabilizer = {g for g in top_set if g[0] == 0}
    selected.require(stabilizer_group == literal_stabilizer,
                     "stored generators do not generate the point stabilizer")
    selected.require(isinstance(kernel, selected.GapGroup),
                     "invalid selected kernel")
    kernel_generators = [selected.permutation(x, 8) for x in kernel.generators]
    kernel_group = selected.generated_subgroup(
        kernel_generators, 8, len(stabilizer_group) + 1)
    selected.require(kernel_group <= stabilizer_group and
                     len(kernel_group) in (1, 2, 4, 7, 8, 12, 14, 24),
                     "invalid stabilizer kernel")
    selected.require(all({selected.conjugate(x, h) for x in kernel_group} ==
                         kernel_group for h in stabilizer_group),
                     "selected stabilizer kernel is not normal")

    shared = top["binding"]
    result = {key: shared[key] for key in (
        "schema", "bindings_sha256", "top_index", "top_order",
        "top_generators", "normal_generators", "normal_orders",
        "class_representatives", "class_sizes")}
    result.update({
        "row": row_index,
        "stabilizer_generators": rows(stabilizer, 8),
        "kernel_generators": [[x + 1 for x in g] for g in kernel_generators],
        "kernel_order": len(kernel_group),
        "local_images": rows(local_images, 3),
        "coset_representatives": rows(cosets, 8),
        "induced_generators": rows(induced, 32),
        "binary_basis": rows(basis, 32),
    })
    return result


def write(path: Path, value: dict, force: bool) -> None:
    payload = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    selected.require(len(payload) <= min(OUTPUT_LIMIT, selected.OUTPUT_LIMIT),
                     "binding output ceiling reached")
    selected.require(force or not path.exists(), "output exists; use --force")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("wb", delete=False, dir=path.parent,
                                     prefix=path.name + ".",
                                     suffix=".partial") as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", required=True, type=int,
                        help="zero-based frames8/bindings8 row")
    parser.add_argument("--top", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    result = export(args.row, read(args.top, ASSEMBLED_SCHEMA))
    write(args.output, result, args.force)
    print(f"{args.output}: row {args.row}; reused top {result['top_index']}; "
          f"kernel {result['kernel_order']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            ValueError) as error:
        raise SystemExit(f"refused: {error}")
