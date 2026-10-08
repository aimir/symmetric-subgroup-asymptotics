#!/usr/bin/env python3
"""Prepare one grouped point-stabilizer normal table for eight-frame rows.

The inputs are explicit ``frames8-selected-top-certificate-v1`` files whose
rows share one literal transitive top.  The first input supplies the chosen
top and point-stabilizer generators.  Every input supplies one eligible local
kernel.  This script enumerates only the selected point stabilizer (order at
most 144), computes its complete conjugacy and normal-subgroup tables, and
emits compact word certificates for the generic Lean normal-join registry.

There is deliberately no directory scan and no all-row mode.  The output is
untrusted certificate data; ``emit_lean_frames8_grouped_stabilizer_normals.py``
renders it, and Lean checks all finite equations and the kernel classification.
"""
from __future__ import annotations

import argparse
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
    conjugate,
    generator_enumeration,
    identity,
    inverse,
    join_transition_words,
    normality_words,
)


INPUT_SCHEMA = "frames8-selected-top-certificate-v1"
OUTPUT_SCHEMA = "frames8-selected-stabilizer-normal-table-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024
MAX_TOP_ORDER = 1_152
MAX_STABILIZER_ORDER = 144
MAX_CLASSES = 144
MAX_NORMALS = 256
MAX_NORMAL_GENERATOR_WIDTH = 16


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def read_json(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected input {path}")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "selected input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == INPUT_SCHEMA,
            "unexpected selected prepared schema")
    return value


def permutation(value: object, width: int, budget: Budget) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            f"invalid degree-{width} permutation")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    budget.tick(width)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def permutation_rows(value: object, width: int, budget: Budget):
    require(isinstance(value, list), "permutation family is not a list")
    return [permutation(row, width, budget) for row in value]


def subgroup_generators(rows: frozenset[tuple[int, ...]], width: int,
                        budget: Budget) -> list[tuple[int, ...]]:
    """Choose a short deterministic ordinary generating tuple."""
    one = identity(width)
    generators: list[tuple[int, ...]] = []
    generated = frozenset({one})
    for row in sorted(rows):
        if row in generated:
            continue
        generators.append(row)
        require(len(generators) <= MAX_NORMAL_GENERATOR_WIDTH,
                "normal subgroup needs too many selected generators")
        enumeration = generator_enumeration(
            generators, width, budget, max_states=MAX_STABILIZER_ORDER)
        generated = frozenset(enumeration.rows)
    require(generated == rows, "greedy normal generators are incomplete")
    return generators


def normal_closure(ambient_rows: list[tuple[int, ...]],
                   parent_rows: frozenset[tuple[int, ...]],
                   representative: tuple[int, ...], width: int,
                   budget: Budget) -> frozenset[tuple[int, ...]]:
    generators = subgroup_generators(parent_rows, width, budget)
    conjugates = {conjugate(g, representative, budget)
                  for g in ambient_rows}
    enumeration = generator_enumeration(
        generators + sorted(conjugates), width, budget,
        max_states=MAX_STABILIZER_ORDER)
    result = frozenset(enumeration.rows)
    require(result <= frozenset(ambient_rows),
            "normal closure escaped the selected stabilizer")
    return result


def commutative_quotient(ambient_rows: list[tuple[int, ...]],
                         normal_rows: frozenset[tuple[int, ...]],
                         budget: Budget) -> bool:
    for x in ambient_rows:
        xi = inverse(x, budget)
        for y in ambient_rows:
            yi = inverse(y, budget)
            commutator = compose(compose(compose(x, y, budget), xi, budget),
                                 yi, budget)
            if commutator not in normal_rows:
                return False
    return True


def parse_shared_inputs(values: list[dict], budget: Budget) -> dict:
    require(values, "no selected prepared inputs")
    first = values[0]
    top_order = first.get("top_order")
    top_index = first.get("top_index")
    require(type(top_order) is int and 1 <= top_order <= MAX_TOP_ORDER,
            "invalid selected top order")

    cayley_rows = permutation_rows(first["cayley"]["rows"], 8, budget)
    require(len(cayley_rows) == top_order and len(set(cayley_rows)) == top_order,
            "invalid selected Cayley rows")
    position = {row: i for i, row in enumerate(cayley_rows)}
    stabilizer_rows = sorted((row for row in cayley_rows if row[0] == 0),
                             key=position.__getitem__)
    require(1 <= len(stabilizer_rows) <= MAX_STABILIZER_ORDER and
            len(stabilizer_rows) * 8 == top_order,
            "invalid selected point-stabilizer order")
    stabilizer_set = frozenset(stabilizer_rows)

    ambient = permutation_rows(
        first["binding"]["stabilizer_generators"], 8, budget)
    ambient_group = generator_enumeration(
        ambient, 8, budget, max_states=MAX_STABILIZER_ORDER)
    require(frozenset(ambient_group.rows) == stabilizer_set,
            "stored generators do not generate the selected stabilizer")

    kernels = []
    source_rows = []
    for value in values:
        require(value.get("top_index") == top_index and
                value.get("top_order") == top_order,
                "grouped row has a different selected top")
        rows = permutation_rows(value["cayley"]["rows"], 8, budget)
        require(rows == cayley_rows,
                "grouped row has different canonical Cayley coordinates")
        local_order = value["module_certificate"].get("local_quotient_order")
        require(local_order in (3, 6), "invalid grouped local quotient order")
        kernel_generators = permutation_rows(
            value["binding"]["kernel_generators"], 8, budget)
        kernel = frozenset(generator_enumeration(
            kernel_generators, 8, budget,
            max_states=MAX_STABILIZER_ORDER).rows)
        require(kernel <= stabilizer_set and
                len(stabilizer_rows) // len(kernel) == local_order,
                "grouped row kernel has the wrong local index")
        kernels.append(kernel)
        source_rows.append(value.get("source_row"))

    return {
        "source_rows": source_rows,
        "top_index": top_index,
        "top_order": top_order,
        "cayley_rows": cayley_rows,
        "position": position,
        "stabilizer_rows": stabilizer_rows,
        "stabilizer_set": stabilizer_set,
        "ambient": ambient,
        "kernels": kernels,
    }


def prepare(values: list[dict], budget: Budget) -> dict:
    shared = parse_shared_inputs(values, budget)
    rows = shared["stabilizer_rows"]
    row_set = shared["stabilizer_set"]
    position = shared["position"]
    one = identity(8)

    # Complete literal conjugacy classes inside the selected point stabilizer.
    unassigned = set(rows)
    classes: list[frozenset[tuple[int, ...]]] = []
    representatives: list[tuple[int, ...]] = []
    centralizers: list[int] = []
    while unassigned:
        representative = min(unassigned, key=position.__getitem__)
        conjugacy_class = frozenset(
            conjugate(g, representative, budget) for g in rows)
        require(conjugacy_class <= row_set,
                "stabilizer conjugacy class escaped the stabilizer")
        centralizer = [g for g in rows
                       if compose(g, representative, budget) ==
                       compose(representative, g, budget)]
        require(len(conjugacy_class) * len(centralizer) == len(rows),
                "stabilizer class/centralizer count mismatch")
        classes.append(conjugacy_class)
        representatives.append(representative)
        centralizers.append(len(centralizer))
        unassigned -= conjugacy_class
    require(len(classes) <= MAX_CLASSES and
            sum(map(len, classes)) == len(rows),
            "invalid stabilizer conjugacy cover")

    class_code = {}
    for code, conjugacy_class in enumerate(classes):
        for row in conjugacy_class:
            require(row not in class_code, "overlapping stabilizer classes")
            class_code[row] = code
    require(set(class_code) == row_set, "stabilizer classes are incomplete")

    # Enumerate the normal lattice as the closure of the bottom state under
    # adjoining one representative from each literal conjugacy class.
    states: list[frozenset[tuple[int, ...]]] = [frozenset({one})]
    state_position = {states[0]: 0}
    children: list[list[int]] = []
    cursor = 0
    while cursor < len(states):
        child_row = []
        for representative in representatives:
            child = normal_closure(rows, states[cursor], representative,
                                   8, budget)
            index = state_position.get(child)
            if index is None:
                require(len(states) < MAX_NORMALS,
                        "stabilizer normal-state ceiling reached")
                index = len(states)
                state_position[child] = index
                states.append(child)
            child_row.append(index)
        children.append(child_row)
        cursor += 1
    require(len(children) == len(states), "normal-state traversal incomplete")

    raw_generators = [subgroup_generators(state, 8, budget)
                      for state in states]
    generator_width = max([1] + list(map(len, raw_generators)))
    require(generator_width <= MAX_NORMAL_GENERATOR_WIDTH,
            "normal generator width ceiling reached")
    generators = [row + [one] * (generator_width - len(row))
                  for row in raw_generators]

    # One checked word for every member of every explicit state lets Lean
    # identify the generated closure with a decidable literal subgroup.  This
    # is what makes the final kernel and index classification cheap and
    # uniform across all rows sharing the top.
    state_words = []
    for state, generator in zip(states, generators):
        enumeration = generator_enumeration(
            generator, 8, budget, max_states=MAX_STABILIZER_ORDER)
        require(frozenset(enumeration.rows) == state,
                "padded normal generators changed their subgroup")
        words = []
        for row in shared["cayley_rows"]:
            index = enumeration.position.get(row)
            words.append(None if index is None else enumeration.word(index))
        state_words.append(words)

    normality = [normality_words(shared["ambient"], generator, 8, budget,
                                 max_states=MAX_STABILIZER_ORDER)
                 for generator in generators]
    transitions = []
    for state_index, generator in enumerate(generators):
        transition_row = []
        for class_index, representative in enumerate(representatives):
            transition_row.append(join_transition_words(
                shared["ambient"], generator, representative,
                generators[children[state_index][class_index]], 8, budget,
                max_states=MAX_STABILIZER_ORDER))
        transitions.append(transition_row)

    kernel_state = []
    for kernel in shared["kernels"]:
        require(kernel in state_position,
                "grouped row kernel escaped the complete normal table")
        kernel_state.append(state_position[kernel])

    classification = []
    for state in states:
        row_indices = [i for i, kernel in enumerate(shared["kernels"])
                       if kernel == state]
        index = len(rows) // len(state)
        commutative = commutative_quotient(rows, state, budget)
        if row_indices:
            classification.append({"tag": "row", "row": row_indices[0]})
        elif index not in (3, 6):
            classification.append({"tag": "irrelevant", "index": index})
        elif index == 6 and commutative:
            classification.append({"tag": "commutative-six"})
        else:
            raise Refused(
                "eligible stabilizer quotient has no grouped row kernel")

    return {
        "schema": OUTPUT_SCHEMA,
        "source_rows": shared["source_rows"],
        "top_index": shared["top_index"],
        "top_order": shared["top_order"],
        "stabilizer_order": len(rows),
        "ambient_count": len(shared["ambient"]),
        "ambient_indices": [position[x] for x in shared["ambient"]],
        "class_representative_indices": [position[x] for x in representatives],
        "centralizer_orders": centralizers,
        "class_code": [class_code.get(row, 0)
                       for row in shared["cayley_rows"]],
        "normal_generator_width": generator_width,
        "normal_generators": [[position[x] for x in row]
                              for row in generators],
        "normal_orders": list(map(len, states)),
        "state_words": state_words,
        "normality": normality,
        "children": children,
        "transitions": transitions,
        "kernel_states": kernel_state,
        "classification": classification,
    }


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "selected output ceiling reached")
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
    parser.add_argument("--input", required=True, type=Path,
                        action="append",
                        help="one explicit prepared row; repeat for shared rows")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--operation-limit", type=int, default=20_000_000)
    parser.add_argument("--seconds-limit", type=float, default=180.0)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(1 <= len(args.input) <= 16, "grouped input count ceiling reached")
    require(1 <= args.operation_limit <= 40_000_000,
            "operation limit outside selected ceiling")
    require(1.0 <= args.seconds_limit <= 300.0,
            "time limit outside selected ceiling")
    budget = Budget(operation_limit=args.operation_limit,
                    seconds_limit=args.seconds_limit)
    result = prepare([read_json(path) for path in args.input], budget)
    payload = (json.dumps(result, separators=(",", ":")) + "\n").encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; top {result['top_index']}; "
          f"stabilizer order {result['stabilizer_order']}; "
          f"{len(result['classification'])} normal states; "
          f"operations {budget.operations}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
