#!/usr/bin/env python3
"""Prepare bounded proof-carrying chunks for one nonbinary degree-16 row.

The two pinned inputs are joined by ``action_id``.  Class chunks contain an
executable conjugacy code and a faithful-action chart of each centralizer.
Normal chunks contain compact normality and exact normal-join words for the
existing ``FiniteNormalJoinWordRegistryData`` importer.  The producer never
invokes Lean, GAP, a subprocess, or another exporter.

There is deliberately no all-actions proof mode.  ``--stage manifest`` only
reads catalogue metadata and writes a deterministic generation plan; proof
chunks require one explicit action and one explicit chunk.  Enumeration is
refused above the selected action ceiling, so large rows must use the sparse
Schreier/centralizer route recorded by the manifest.
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
ACTIONS = ROOT / "certificates/data/nonbinary_actions.json"
NORMALS = ROOT / "certificates/data/nonbinary_normals.jsonl.gz"
ACTIONS_SHA256 = "3c40109679d70c5929a1b5cbf7c65c390c18ee41a32e07981bf2190e1facffea"
NORMALS_SHA256 = "bfe1aa3d93e17c21457f618296af0f761f5bc2b906613e9a853ab2cca4144aa3"
ACTION_COUNT = 527
WIDTH = 16
CLASS_CHUNK_SIZE = 8
NORMAL_CHUNK_SIZE = 4
ACTIONS_INPUT_LIMIT = 1024 * 1024
NORMALS_COMPRESSED_LIMIT = 1024 * 1024
NORMALS_DECOMPRESSED_LIMIT = 8 * 1024 * 1024
OUTPUT_LIMIT = 8 * 1024 * 1024
MAX_GROUP_ORDER = 46_080


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_bytes(path: Path, limit: int, expected_digest: str) -> bytes:
    require(path.is_file() and not path.is_symlink(), f"missing or redirected {path.name}")
    raw = path.read_bytes()
    require(len(raw) <= limit, f"{path.name} input ceiling reached")
    require(digest(raw) == expected_digest, f"{path.name} digest changed")
    return raw


def pinned_rows() -> list[dict]:
    actions_raw = read_bytes(ACTIONS, ACTIONS_INPUT_LIMIT, ACTIONS_SHA256)
    action_data = json.loads(actions_raw)
    require(action_data.get("schema_version") == 1, "unexpected action schema")
    actions = action_data.get("actions")
    require(isinstance(actions, list) and len(actions) == ACTION_COUNT,
            "nonbinary action count changed")

    compressed = read_bytes(NORMALS, NORMALS_COMPRESSED_LIMIT, NORMALS_SHA256)
    raw = gzip.decompress(compressed)
    require(len(raw) <= NORMALS_DECOMPRESSED_LIMIT,
            "decompressed normal input ceiling reached")
    normal_rows = [json.loads(line) for line in raw.splitlines() if line.strip()]
    require(len(normal_rows) == ACTION_COUNT, "nonbinary normal row count changed")
    by_id = {row.get("action_id"): row for row in normal_rows}
    require(len(by_id) == ACTION_COUNT, "duplicate normal action id")

    result = []
    for index, action in enumerate(actions):
        action_id = action.get("action_id")
        require(action_id in by_id, f"missing normal row for {action_id}")
        normal = by_id[action_id]
        require(normal.get("schema_version") == 1, f"unexpected normal schema for {action_id}")
        require(action.get("degree") == WIDTH, f"unexpected action width for {action_id}")
        require(action.get("normal_count") == len(normal.get("normals", [])),
                f"normal count mismatch for {action_id}")
        result.append({**action, **normal, "catalogue_index": index})
    return result


def permutation(value: object) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == WIDTH,
            "invalid degree-sixteen permutation")
    require(all(type(x) is int for x in value), "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(WIDTH)), "invalid degree-sixteen permutation")
    return row


def word_for_row(group, row: tuple[int, ...]) -> dict:
    require(row in group.position, "selected row escaped the literal action")
    return group.word(group.position[row])


def class_chunk(action: dict, group, start: int, stop: int,
                budget: Budget) -> dict:
    representatives = [permutation(row["representative"])
                       for row in action["classes"]]
    class_sets = []
    class_sum = 0
    centralizers = []
    for index, representative in enumerate(representatives):
        centralizer = []
        conjugates = set()
        for g in group.rows:
            gi = inverse(g, budget)
            if compose(g, representative, budget) == compose(representative, g, budget):
                centralizer.append(g)
            conjugates.add(compose(compose(g, representative, budget), gi, budget))
        require(len(conjugates) == action["classes"][index]["size"],
                "literal class size disagrees with pinned class row")
        require(len(group.rows) == len(centralizer) * len(conjugates),
                "class/centralizer product check failed")
        class_sets.append(conjugates)
        centralizers.append(centralizer)
        class_sum += len(conjugates)
    require(all(class_sets[i].isdisjoint(class_sets[j])
                for i in range(len(class_sets)) for j in range(i)),
            "selected class representatives are conjugate")
    require(class_sum == len(group.rows), "selected classes do not exhaust action")

    rows = []
    for index in range(start, stop):
        representative = representatives[index]
        rows.append({
            "class_index": index + 1,
            "representative": list(x + 1 for x in representative),
            "representative_word": word_for_row(group, representative),
            "centralizer_card": len(centralizers[index]),
            # The original permutation action is faithful.  Listing its
            # centralizer image therefore gives a kernel-one coordinate chart.
            "faithful_centralizer_chart": [
                word_for_row(group, g) for g in centralizers[index]
            ],
            "class_card": len(class_sets[index]),
        })
    return {"rows": rows, "class_card_sum": class_sum}


def literal_child(ambient_group, normal_generators,
                  normal_row_sets, parent_index: int,
                  representative: tuple[int, ...], budget: Budget) -> int:
    conjugates = []
    seen = set()
    for g in ambient_group.rows:
        atom = compose(compose(g, representative, budget), inverse(g, budget), budget)
        if atom not in seen:
            seen.add(atom)
            conjugates.append(atom)
    joined = generator_enumeration(
        normal_generators[parent_index] + conjugates, WIDTH, budget,
        max_states=MAX_GROUP_ORDER)
    joined_rows = frozenset(joined.rows)
    matches = [i for i, rows in enumerate(normal_row_sets) if rows == joined_rows]
    require(len(matches) == 1,
            "literal normal closure did not match one selected normal state")
    return matches[0]


def relative_socle_plan(action: dict,
                        normal_row_sets: list[frozenset[tuple[int, ...]]],
                        base: int) -> dict:
    """Find the relative atoms, their join, and a short normal-generator path.

    The path uses conjugacy-class representatives.  Taking a transition from
    state ``N`` along class ``c`` replaces ``N`` by
    ``N ⋁ normalClosure(c)``.  Thus a path from the base to the relative
    socle carrier is exactly a tuple whose normal closure, together with the
    base, is that carrier.  Lean later rechecks the resulting subgroup
    equality on the executable row group.
    """
    count = len(normal_row_sets)
    base_rows = normal_row_sets[base]
    above = [j for j in range(count)
             if base_rows < normal_row_sets[j]]
    components = [
        j for j in above
        if not any(base_rows < normal_row_sets[k] < normal_row_sets[j]
                   for k in above)
    ]
    carriers = [
        j for j in range(count)
        if base_rows <= normal_row_sets[j]
        and all(normal_row_sets[k] <= normal_row_sets[j]
                for k in components)
    ]
    minimal_carriers = [
        j for j in carriers
        if not any(normal_row_sets[k] < normal_row_sets[j]
                   for k in carriers)
    ]
    require(len(minimal_carriers) == 1,
            "relative socle carrier is not unique")
    carrier = minimal_carriers[0]

    atoms = action["atoms"]
    atom_position = {normal_index: i for i, normal_index in enumerate(atoms)}
    class_atoms = [row["normal_closure"] for row in action["classes"]]
    joins = [row.get("joins") for row in action["normals"]]
    require(all(isinstance(row, list) and len(row) == len(atoms)
                for row in joins), "normal join table is incomplete")

    queue = [base]
    path: dict[int, list[int]] = {base: []}
    for state in queue:
        if state == carrier:
            break
        for class_index, closure_state in enumerate(class_atoms):
            child = joins[state][atom_position[closure_state]] - 1
            require(0 <= child < count, "normal join target is out of range")
            if child not in path:
                path[child] = path[state] + [class_index]
                queue.append(child)
    require(carrier in path, "relative socle carrier is unreachable")
    return {
        "minimal_state_indices": [j + 1 for j in components],
        "carrier_state_index": carrier + 1,
        "generator_class_indices": [j + 1 for j in path[carrier]],
    }


def normal_chunk(action: dict, ambient_group, start: int, stop: int,
                 budget: Budget) -> dict:
    ambient = [permutation(row) for row in action["generators"]]
    representatives = [permutation(row["representative"])
                       for row in action["classes"]]
    normals = action["normals"]
    atoms = action["atoms"]
    require(isinstance(atoms, list) and atoms == sorted(set(atoms)),
            "normal-closure atom list is malformed")
    atom_position = {normal_index: i for i, normal_index in enumerate(atoms)}
    require(all(row["normal_closure"] in atom_position
                for row in action["classes"]),
            "class normal closure is absent from atom list")
    normal_generators = [
        [permutation(row) for row in normal["generators"]] for normal in normals
    ]
    normal_groups = [
        generator_enumeration(generators, WIDTH, budget,
                              max_states=MAX_GROUP_ORDER)
        for generators in normal_generators
    ]
    normal_row_sets = [frozenset(group.rows) for group in normal_groups]
    require(len(set(normal_row_sets)) == len(normal_row_sets),
            "selected normal-generator states are not distinct")
    socle_plans = [relative_socle_plan(action, normal_row_sets, i)
                   for i in range(len(normals))]

    rows = []
    for index in range(start, stop):
        normal = normals[index]
        generators = normal_generators[index]
        require(len(normal_groups[index].rows) == normal["order"],
                "declared normal order disagrees with literal generators")
        transitions = []
        supplied = normal.get("joins")
        require(isinstance(supplied, list) and len(supplied) == len(atoms),
                "normal join row is not complete")
        for class_index, representative in enumerate(representatives):
            child = literal_child(ambient_group, normal_generators, normal_row_sets,
                                  index, representative, budget)
            closure_state = action["classes"][class_index]["normal_closure"]
            require(supplied[atom_position[closure_state]] == child + 1,
                    "pinned normal join disagrees with literal closure")
            transitions.append({
                "class_index": class_index + 1,
                "child_index": child + 1,
                "words": join_transition_words(
                    ambient, generators, representative,
                    normal_generators[child], WIDTH, budget,
                    max_states=MAX_GROUP_ORDER),
            })
        rows.append({
            "normal_index": index + 1,
            "declared_order": normal["order"],
            "certificate": normal.get("certificate"),
            "relative_socle": socle_plans[index],
            "normality": normality_words(
                ambient, generators, WIDTH, budget,
                max_states=MAX_GROUP_ORDER),
            "transitions": transitions,
        })
    return {"rows": rows}


def generation_manifest(rows: list[dict]) -> dict:
    actions = []
    for action in rows:
        order = action["order"]
        classes = len(action["classes"])
        normals = len(action["normals"])
        bounded = order <= MAX_GROUP_ORDER
        module_token = action["action_id"]
        class_chunks = (classes + CLASS_CHUNK_SIZE - 1) // CLASS_CHUNK_SIZE
        normal_chunks = (normals + NORMAL_CHUNK_SIZE - 1) // NORMAL_CHUNK_SIZE
        actions.append({
            "catalogue_index": action["catalogue_index"],
            "action_id": action["action_id"],
            "family": action["family"],
            "order": order,
            "class_count": classes,
            "normal_count": normals,
            "class_chunks": class_chunks,
            "normal_chunks": normal_chunks,
            "class_chunk_files": [
                f"{action['action_id']}_classes_{i:03d}.json"
                for i in range(class_chunks)
            ],
            "normal_chunk_files": [
                f"{action['action_id']}_normals_{i:03d}.json"
                for i in range(normal_chunks)
            ],
            "class_module":
                f"PrimitiveAffineDegreeTwoNonbinary{module_token}ClassPilot",
            "normal_module":
                f"PrimitiveAffineDegreeTwoNonbinary{module_token}Normals",
            "structural_module":
                f"PrimitiveAffineDegreeTwoNonbinary{module_token}Structural",
            "quotient_socle_module":
                f"PrimitiveAffineDegreeTwoNonbinary{module_token}QuotientSocles",
            "selected_route": ("bounded_faithful_action_words" if bounded
                               else "sparse_schreier_and_centralizer_coordinates"),
        })
    return {
        "schema_version": 1,
        "actions_sha256": ACTIONS_SHA256,
        "normals_sha256": NORMALS_SHA256,
        "width": WIDTH,
        "action_count": ACTION_COUNT,
        "class_chunk_size": CLASS_CHUNK_SIZE,
        "normal_chunk_size": NORMAL_CHUNK_SIZE,
        "bounded_action_order": MAX_GROUP_ORDER,
        "producer": "export_lean_nonbinary_selected_chunks.py",
        "class_emitter": "emit_lean_nonbinary_selected_class_pilot.py",
        "normal_emitter": "emit_lean_nonbinary_selected_normals.py",
        "quotient_socle_emitter":
            "emit_lean_nonbinary_selected_quotient_socles.py",
        "generation_policy": [
            "Generate one explicit action and chunk at a time.",
            "Assemble all class chunks before emitting the class module.",
            "Assemble all normal chunks before emitting the normal module.",
            "Emit relative-socle tables from those same checked normal chunks.",
            "Transport both modules to the literal subgroup and call FiniteNormalStateRegistry.ofWordRegistry.",
            "Use the sparse Schreier/centralizer route for rows above bounded_action_order.",
        ],
        "actions": actions,
    }


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
    parser.add_argument("--stage", required=True,
                        choices=("manifest", "classes", "normals"))
    parser.add_argument("--action-id")
    parser.add_argument("--chunk", type=int)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    rows = pinned_rows()
    if args.stage == "manifest":
        require(args.action_id is None and args.chunk is None,
                "manifest stage does not accept action or chunk")
        output = generation_manifest(rows)
    else:
        require(args.action_id is not None, "proof chunks require --action-id")
        require(args.chunk is not None and args.chunk >= 0,
                "proof chunks require a nonnegative --chunk")
        matches = [row for row in rows if row["action_id"] == args.action_id]
        require(len(matches) == 1, "unknown or duplicate action id")
        action = matches[0]
        require(action["order"] <= MAX_GROUP_ORDER,
                "selected action exceeds bounded enumeration route; use manifest sparse route")
        ambient = [permutation(row) for row in action["generators"]]
        require(1 <= len(ambient) <= 16, "ambient generator ceiling reached")
        budget = Budget(operation_limit=12_000_000, seconds_limit=60.0)
        group = generator_enumeration(
            ambient, WIDTH, budget, max_states=MAX_GROUP_ORDER)
        require(len(group.rows) == action["order"], "selected action order check failed")
        if args.stage == "classes":
            total, size = len(action["classes"]), CLASS_CHUNK_SIZE
            start, stop = args.chunk * size, min(total, (args.chunk + 1) * size)
            require(start < stop, "selected class chunk is empty")
            content = class_chunk(action, group, start, stop, budget)
        else:
            total, size = len(action["normals"]), NORMAL_CHUNK_SIZE
            start, stop = args.chunk * size, min(total, (args.chunk + 1) * size)
            require(start < stop, "selected normal chunk is empty")
            content = normal_chunk(action, group, start, stop, budget)
        output = {
            "schema_version": 1,
            "actions_sha256": ACTIONS_SHA256,
            "normals_sha256": NORMALS_SHA256,
            "catalogue_index": action["catalogue_index"],
            "action_id": action["action_id"],
            "family": action["family"],
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
    print(f"WROTE {args.output} ({len(payload)} bytes)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, EOFError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
