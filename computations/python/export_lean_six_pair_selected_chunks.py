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
    rows = []
    for index in range(start, stop):
        normal = normals[index]
        generators = normal_generators[index]
        transitions = []
        joins = normal.get("joins")
        require(isinstance(joins, list) and len(joins) == len(representatives),
                "invalid selected normal join row")
        for class_index, child_one_based in enumerate(joins):
            require(type(child_one_based) is int and 1 <= child_one_based <= len(normals),
                    "selected child index out of range")
            child_index = child_one_based - 1
            transitions.append({
                "class_index": class_index + 1,
                "child_index": child_one_based,
                "words": join_transition_words(
                    ambient, generators, representatives[class_index],
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
    return {"rows": rows}


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
