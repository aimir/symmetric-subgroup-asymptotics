#!/usr/bin/env python3
"""Prepare one bounded proof-carrying chunk of one six-pair action.

This producer requires an explicit action and one explicit chunk.  It has no
default action and no all-actions mode.  Output is untrusted JSON consumed by
the Lean source emitter: literal word equations and reversible coordinate
rows are checked again in Lean against the original permutations.

The script never invokes Lean, GAP, a subprocess, or another exporter.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from six_pair_selected_words import (
    Budget,
    Refused,
    compose,
    generator_enumeration,
    identity,
    inverse,
    join_transition_words,
    normality_words,
)


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/six_block.json.gz"
DATA_SHA256 = "446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3"
ACTION_COUNT = 182
WIDTH = 12
PAIR_COUNT = 6
CLASS_CHUNK_SIZE = 8
NORMAL_CHUNK_SIZE = 4
COMPRESSED_INPUT_LIMIT = 128 * 1024
DECOMPRESSED_INPUT_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 4 * 1024 * 1024
MAX_GROUP_ORDER = 46_080


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def selected_data() -> dict:
    require(DATA.is_file() and not DATA.is_symlink(), "missing or redirected six-pair data")
    compressed = DATA.read_bytes()
    require(len(compressed) <= COMPRESSED_INPUT_LIMIT,
            "compressed six-pair input ceiling reached")
    require(digest(compressed) == DATA_SHA256, "six-pair input digest changed")
    raw = gzip.decompress(compressed)
    require(len(raw) <= DECOMPRESSED_INPUT_LIMIT,
            "decompressed six-pair input ceiling reached")
    data = json.loads(raw)
    require(data.get("schema_version") == 1, "unexpected six-pair schema")
    require(len(data.get("actions", [])) == ACTION_COUNT,
            "six-pair action count changed")
    return data


def permutation(value) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == WIDTH,
            "invalid degree-twelve row")
    require(all(type(x) is int for x in value), "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(WIDTH)), "invalid degree-twelve permutation")
    return row


def pair_top(row: tuple[int, ...]) -> tuple[int, ...]:
    result = []
    for i in range(PAIR_COUNT):
        a, b = row[2 * i], row[2 * i + 1]
        require(a // 2 == b // 2, "selected action does not preserve standard pairs")
        result.append(a // 2)
    require(sorted(result) == list(range(PAIR_COUNT)), "invalid pair-top permutation")
    return tuple(result)


def permutation_sign(row: tuple[int, ...]) -> int:
    """Return the literal permutation sign as ``1`` or ``-1``."""
    inversions = sum(
        row[i] > row[j]
        for i in range(len(row)) for j in range(i + 1, len(row))
    )
    return -1 if inversions % 2 else 1


def word_for_row(group, row):
    require(row in group.position, "selected row escaped the literal action")
    return group.word(group.position[row])


def class_chunk(action: dict, group, start: int, stop: int, budget: Budget) -> dict:
    representatives = [permutation(x) for x in action["class_representatives"]]
    rows = []
    class_sum = 0
    all_classes = []
    for representative in representatives:
        centralizer = []
        conjugates = set()
        for g in group.rows:
            gi = inverse(g, budget)
            if compose(g, representative, budget) == compose(representative, g, budget):
                centralizer.append(g)
            conjugates.add(compose(compose(g, representative, budget), gi, budget))
        require(centralizer, "empty selected centralizer")
        all_classes.append(conjugates)
        class_sum += len(conjugates)
    require(all(all_classes[i].isdisjoint(all_classes[j])
                for i in range(len(all_classes)) for j in range(i)),
            "selected class representatives are conjugate")
    require(class_sum == len(group.rows), "selected class cardinalities do not exhaust action")

    for index in range(start, stop):
        representative = representatives[index]
        centralizer = [g for g in group.rows
                       if compose(g, representative, budget) ==
                       compose(representative, g, budget)]
        kernel = [g for g in centralizer if pair_top(g) == identity(PAIR_COUNT)]
        top_preimage = {}
        for g in centralizer:
            top_preimage.setdefault(pair_top(g), g)
        require(len(kernel) * len(top_preimage) == len(centralizer),
                "centralizer kernel/top product check failed")
        rows.append({
            "class_index": index + 1,
            "representative": list(x + 1 for x in representative),
            "centralizer_card": len(centralizer),
            "kernel_chart": [word_for_row(group, g) for g in kernel],
            "top_chart": [
                {"top": list(x + 1 for x in top),
                 "preimage": word_for_row(group, g)}
                for top, g in sorted(top_preimage.items())
            ],
            "class_card": len(group.rows) // len(centralizer),
        })
    return {"rows": rows, "class_card_sum": class_sum}


def normal_chunk(action: dict, start: int, stop: int, budget: Budget) -> dict:
    ambient = [permutation(x) for x in action["generators"]]
    representatives = [permutation(x) for x in action["class_representatives"]]
    normals = action["normals"]
    normal_generators = [
        [permutation(x) for x in normal["generators"]] for normal in normals
    ]
    # Reconstruct the complete join table from the literal action.  Most rows
    # in the historical file retain only an abbreviated `joins` list, so it
    # cannot be used as a proof premise.  A normal closure is generated by the
    # parent together with every ambient conjugate of the class
    # representative.  Match that literal subgroup against the supplied
    # normal-generator states; the emitted compact words are still checked by
    # Lean independently.
    ambient_group = generator_enumeration(
        ambient, WIDTH, budget, max_states=MAX_GROUP_ORDER)
    normal_groups = [
        generator_enumeration(generators, WIDTH, budget,
                              max_states=MAX_GROUP_ORDER)
        for generators in normal_generators
    ]
    normal_row_sets = [frozenset(group.rows) for group in normal_groups]
    require(len(set(normal_row_sets)) == len(normal_row_sets),
            "selected normal-generator states are not distinct")

    def literal_child(parent_index: int, representative: tuple[int, ...]) -> int:
        conjugates = []
        seen = set()
        for g in ambient_group.rows:
            atom = compose(compose(g, representative, budget),
                           inverse(g, budget), budget)
            if atom not in seen:
                seen.add(atom)
                conjugates.append(atom)
        joined = generator_enumeration(
            normal_generators[parent_index] + conjugates,
            WIDTH, budget, max_states=MAX_GROUP_ORDER)
        joined_rows = frozenset(joined.rows)
        matches = [i for i, rows in enumerate(normal_row_sets)
                   if rows == joined_rows]
        require(len(matches) == 1,
                "literal normal closure did not match one selected normal state")
        return matches[0]

    rows = []
    for index in range(start, stop):
        normal = normals[index]
        generators = normal_generators[index]
        transitions = []
        supplied_joins = normal.get("joins")
        full_supplied_row = (isinstance(supplied_joins, list) and
                             len(supplied_joins) == len(representatives))
        for class_index, representative in enumerate(representatives):
            child_index = literal_child(index, representative)
            child_one_based = child_index + 1
            if full_supplied_row:
                require(supplied_joins[class_index] == child_one_based,
                        "full supplied normal join row disagrees with literal closure")
            transitions.append({
                "class_index": class_index + 1,
                "child_index": child_one_based,
                "words": join_transition_words(
                    ambient, generators, representative,
                    normal_generators[child_index], WIDTH, budget,
                    max_states=MAX_GROUP_ORDER),
            })
        rows.append({
            "normal_index": index + 1,
            "declared_order": normal["order"],
            "normality": normality_words(
                ambient, generators, WIDTH, budget, max_states=MAX_GROUP_ORDER),
            "transitions": transitions,
        })
    content = {"rows": rows}
    if len(normals) == 3 and start == 0 and stop == len(normals):
        ambient_rows = frozenset(ambient_group.rows)
        bottom_indices = [
            i for i, group in enumerate(normal_groups)
            if len(group.rows) == 1
        ]
        top_indices = [
            i for i, group in enumerate(normal_groups)
            if frozenset(group.rows) == ambient_rows
        ]
        require(len(bottom_indices) == 1,
                "three-state chain has no unique literal bottom")
        require(len(top_indices) == 1,
                "three-state chain has no unique literal top")
        middle_indices = [
            i for i in range(len(normals))
            if i not in (bottom_indices[0], top_indices[0])
        ]
        require(len(middle_indices) == 1,
                "three-state chain has no unique literal middle")
        middle_index = middle_indices[0]
        middle_generators = normal_generators[middle_index]
        nonidentity = [
            i for i, generator in enumerate(middle_generators)
            if generator != identity(WIDTH)
        ]
        require(nonidentity,
                "three-state middle has no nonidentity displayed generator")
        odd_ambient = [
            i for i, generator in enumerate(ambient)
            if permutation_sign(pair_top(generator)) == -1
        ]
        top_group = normal_groups[top_indices[0]]
        require(all(generator in top_group.position for generator in ambient),
                "literal top does not contain every ambient generator")
        content["three_normal_chain"] = {
            "bottom_index": bottom_indices[0] + 1,
            "middle_index": middle_index + 1,
            "top_index": top_indices[0] + 1,
            "middle_nonidentity_generator": nonidentity[0] + 1,
            "middle_pair_top_signs": [
                permutation_sign(pair_top(generator))
                for generator in middle_generators
            ],
            "odd_ambient_generator":
                (odd_ambient[0] + 1 if odd_ambient else None),
            "top_ambient_words": [
                top_group.word(top_group.position[generator])
                for generator in ambient
            ],
        }
    return content


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "selected output byte ceiling reached")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("wb", delete=False, dir=path.parent,
                                     prefix=path.name + ".", suffix=".partial") as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--action", required=True, type=int)
    parser.add_argument("--stage", required=True, choices=("classes", "normals"))
    parser.add_argument("--chunk", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(1 <= args.action <= ACTION_COUNT, "action must lie in 1..182")
    require(args.chunk >= 0, "chunk must be nonnegative")
    data = selected_data()
    action = data["actions"][args.action - 1]
    ambient = [permutation(x) for x in action["generators"]]
    require(1 <= len(ambient) <= 11, "selected ambient generator count changed")
    budget = Budget()
    group = generator_enumeration(
        ambient, WIDTH, budget, max_states=MAX_GROUP_ORDER)
    require(len(group.rows) == action["order"], "selected action order check failed")
    if args.stage == "classes":
        total = len(action["class_representatives"])
        start = args.chunk * CLASS_CHUNK_SIZE
        stop = min(total, start + CLASS_CHUNK_SIZE)
        require(start < stop, "selected class chunk is empty")
        content = class_chunk(action, group, start, stop, budget)
    else:
        total = len(action["normals"])
        start = args.chunk * NORMAL_CHUNK_SIZE
        stop = min(total, start + NORMAL_CHUNK_SIZE)
        require(start < stop, "selected normal chunk is empty")
        content = normal_chunk(action, start, stop, budget)
    output = {
        "schema_version": 1,
        "source_sha256": DATA_SHA256,
        "action": args.action,
        "stage": args.stage,
        "chunk": args.chunk,
        "range": [start + 1, stop],
        "action_order": len(group.rows),
        "ambient_generator_count": len(ambient),
        "operations": budget.operations,
        "content": content,
    }
    payload = (json.dumps(output, sort_keys=True, separators=(",", ":")) + "\n").encode()
    write_atomic(args.output, payload, args.force)
    print("WROTE", args.output)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, EOFError, json.JSONDecodeError, Refused) as error:
        print("FAIL:", error, file=sys.stderr)
        raise SystemExit(1)
