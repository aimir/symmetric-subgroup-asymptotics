#!/usr/bin/env python3
"""Reconstruct one pair-top natural-module generator certificate.

The input must be one bounded payload written by
``export_lean_pair_top_selected.py --stage selected``.  This program checks
the stored invariant-state list against the literal permutation generators,
enumerates the vector orbits of that one binary module, and emits the data
needed by the Lean cyclic-orbit importer:

* vector-orbit representatives and positive-generator paths;
* distinct cyclic orbit spans and the complete state/child table;
* sparse witnesses for every cyclic basis and child-join basis; and
* one shortest, zero-padded cyclic-generator path for every invariant state.

It deliberately accepts only one selected row and never opens the full
catalogue.  The output is a checked witness payload, not a Lean theorem.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import sys


SCHEMA = "pair-top-selected-module-generators-v1"
INPUT_LIMIT = 8 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024


class Refused(ValueError):
    """The selected payload or reconstructed certificate failed a pin."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def basis(vectors: tuple[int, ...] | list[int], n: int) -> tuple[int, ...]:
    """Canonical reduced binary echelon basis used by pair_top_modules.py."""
    rows: dict[int, int] = {}
    for original in vectors:
        value = int(original)
        require(0 <= value < 1 << n, "binary vector outside module")
        for pivot in sorted(rows, reverse=True):
            if (value >> pivot) & 1:
                value ^= rows[pivot]
        if value:
            pivot = value.bit_length() - 1
            for old_pivot in rows:
                if (rows[old_pivot] >> pivot) & 1:
                    rows[old_pivot] ^= value
            rows[pivot] = value
    return tuple(rows[pivot] for pivot in sorted(rows))


def basis_with_provenance(
        vectors: tuple[int, ...] | list[int], n: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Canonical basis plus masks in the supplied ordered vector list."""
    values = tuple(map(int, vectors))
    rows: dict[int, tuple[int, int]] = {}
    for index, original in enumerate(values):
        value, witness = original, 1 << index
        for pivot in sorted(rows, reverse=True):
            if (value >> pivot) & 1:
                value ^= rows[pivot][0]
                witness ^= rows[pivot][1]
        if value:
            pivot = value.bit_length() - 1
            for old_pivot in tuple(rows):
                if (rows[old_pivot][0] >> pivot) & 1:
                    old_value, old_witness = rows[old_pivot]
                    rows[old_pivot] = (old_value ^ value, old_witness ^ witness)
            rows[pivot] = (value, witness)
    output = tuple(rows[pivot] for pivot in sorted(rows))
    for value, witness in output:
        actual = 0
        for index, original in enumerate(values):
            if (witness >> index) & 1:
                actual ^= original
        require(actual == value, "basis provenance mismatch")
    return tuple(value for value, _ in output), tuple(w for _, w in output)


def coordinate_mask(rows: tuple[int, ...], value: int) -> int | None:
    result = 0
    for index in range(len(rows) - 1, -1, -1):
        row = rows[index]
        if (value >> (row.bit_length() - 1)) & 1:
            value ^= row
            result ^= 1 << index
    return result if value == 0 else None


def coordinate_dual_masks(rows: tuple[int, ...], n: int) -> list[int]:
    """A checked left inverse of the displayed ambient-coordinate basis."""
    output = [0] * len(rows)
    for coordinate in range(n):
        value = 1 << coordinate
        result = 0
        for index in range(len(rows) - 1, -1, -1):
            row = rows[index]
            if (value >> (row.bit_length() - 1)) & 1:
                value ^= row
                result ^= 1 << index
        for index in range(len(rows)):
            if (result >> index) & 1:
                output[index] |= 1 << coordinate
    for index, row in enumerate(rows):
        actual = sum(((row & mask).bit_count() & 1) << j
                     for j, mask in enumerate(output))
        require(actual == 1 << index, "coordinate dual is not a left inverse")
    return output


def permutation_tables(generators: list[list[int]], n: int) -> list[list[int]]:
    tables = []
    for permutation in generators:
        require(isinstance(permutation, list) and
                all(type(x) is int for x in permutation) and
                sorted(permutation) == list(range(1, n + 1)),
                "invalid literal permutation")
        table = [0] * (1 << n)
        for value in range(1, 1 << n):
            low = value & -value
            table[value] = (table[value ^ low] |
                            (1 << (permutation[low.bit_length() - 1] - 1)))
        tables.append(table)
    require(tables, "empty ordered generator list")
    return tables


def orbit_with_words(seed: int, tables: list[list[int]]) -> tuple[list[int], list[list[int]]]:
    orbit, words = [seed], [[]]
    position = {seed: 0}
    for index, value in enumerate(orbit):
        for generator, table in enumerate(tables):
            image = table[value]
            if image not in position:
                position[image] = len(orbit)
                orbit.append(image)
                words.append(words[index] + [generator])
    return orbit, words


def selected_words(mask: int, words: list[list[int]]) -> list[list[int]]:
    return [words[index] for index in range(len(words))
            if (mask >> index) & 1]


def read_selected(path: Path) -> tuple[dict, str]:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected selected payload")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "selected payload ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema_version") == 1,
            "unexpected selected payload schema")
    require(isinstance(value.get("action"), dict) and
            isinstance(value.get("module"), dict),
            "selected payload lacks action/module rows")
    require(value["action"].get("id") == value["module"].get("id"),
            "selected action/module identifiers disagree")
    return value, hashlib.sha256(raw).hexdigest()


def certificate(value: dict, selected_sha256: str) -> dict:
    action, stored = value["action"], value["module"]
    n = action.get("degree")
    require(type(n) is int and n in (6, 8, 12, 16),
            "unsupported natural-module degree")
    generators = action.get("generators")
    require(isinstance(generators, list) and generators == stored.get("generators"),
            "ordered module generators changed")
    tables = permutation_tables(generators, n)

    raw_states = stored.get("numerators")
    require(isinstance(raw_states, list) and raw_states,
            "missing invariant-state rows")
    states = [tuple(row) for row in raw_states]
    require(all(basis(list(row), n) == row for row in states),
            "noncanonical invariant-state basis")
    require(states == sorted(set(states), key=lambda row: (len(row), row)),
            "invariant-state list is not the canonical duplicate-free order")
    state_index = {row: index for index, row in enumerate(states)}
    require(states[0] == () and
            basis([1 << coordinate for coordinate in range(n)], n) in state_index,
            "invariant-state list lacks bottom or whole module")
    require(all(table[value] in range(1 << n)
                for table in tables for value in range(1 << n)),
            "permutation table escaped module")
    require(all(coordinate_mask(state, table[value]) is not None
                for state in states for table in tables for value in state),
            "stored numerator is not invariant")

    seen = bytearray(1 << n)
    orbit_representatives: list[int] = []
    orbit_cardinalities: list[int] = []
    orbit_cyclic_bases: list[tuple[int, ...]] = []
    orbit_cyclic_basis_words: list[list[list[int]]] = []
    for seed in range(1 << n):
        if seen[seed]:
            continue
        orbit, words = orbit_with_words(seed, tables)
        require(all(not seen[point] for point in orbit),
                "selected vector orbits overlap")
        for point in orbit:
            seen[point] = 1
        cyclic_basis, provenance = basis_with_provenance(orbit, n)
        require(cyclic_basis in state_index,
                "cyclic orbit span is absent from invariant states")
        orbit_representatives.append(seed)
        orbit_cardinalities.append(len(orbit))
        orbit_cyclic_bases.append(cyclic_basis)
        orbit_cyclic_basis_words.append(
            [selected_words(mask, words) for mask in provenance])
    require(all(seen) and sum(orbit_cardinalities) == 1 << n,
            "vector orbits do not cover the module")

    cyclic_modules = sorted(set(orbit_cyclic_bases),
                            key=lambda row: (len(row), row))
    require(len(cyclic_modules) == stored.get("cyclic_count"),
            "reconstructed cyclic count disagrees with stored row")
    cyclic_index = {row: index for index, row in enumerate(cyclic_modules)}
    orbit_cyclic_index = [cyclic_index[row] for row in orbit_cyclic_bases]
    cyclic_first_orbit = [orbit_cyclic_index.index(index)
                          for index in range(len(cyclic_modules))]
    cyclic_representatives = [orbit_representatives[index]
                              for index in cyclic_first_orbit]
    cyclic_state_index = [state_index[row] for row in cyclic_modules]
    zero_cyclic = cyclic_index[()]

    children: list[list[int]] = []
    child_old_coordinates: list[list[list[int]]] = []
    child_orbit_words: list[list[list[list[list[int]]]]] = []
    for state in states:
        state_children, state_old, state_words = [], [], []
        for cyclic_number, cyclic in enumerate(cyclic_modules):
            representative = cyclic_representatives[cyclic_number]
            orbit, words = orbit_with_words(representative, tables)
            child, provenance = basis_with_provenance(list(state) + orbit, n)
            require(child == basis(list(state) + list(cyclic), n),
                    "orbit span and cyclic state disagree")
            require(child in state_index, "state/cyclic join is absent")
            state_children.append(state_index[child])
            old_rows, word_rows = [], []
            for mask in provenance:
                old_rows.append(mask & ((1 << len(state)) - 1))
                word_rows.append(selected_words(mask >> len(state), words))
            state_old.append(old_rows)
            state_words.append(word_rows)
        children.append(state_children)
        child_old_coordinates.append(state_old)
        child_orbit_words.append(state_words)

    cap = stored.get("section_cap")
    require(type(cap) is int and 0 <= cap <= n, "invalid stored section cap")
    paths: list[list[int] | None] = [None] * len(states)
    paths[0] = []
    queue: deque[int] = deque([0])
    while queue:
        state = queue.popleft()
        current = paths[state]
        require(current is not None, "internal missing generator path")
        if len(current) == cap:
            continue
        for cyclic_number, child in enumerate(children[state]):
            if paths[child] is None:
                paths[child] = current + [cyclic_number]
                queue.append(child)
    require(all(path is not None for path in paths),
            "stored Schur cap does not generate every invariant state")
    generator_paths = [([zero_cyclic] * (cap - len(path)) + path)
                       for path in paths if path is not None]
    require(len(generator_paths) == len(states) and
            all(len(path) == cap for path in generator_paths),
            "failed to pad generator paths")
    for target, path in enumerate(generator_paths):
        state = 0
        for cyclic_number in path:
            state = children[state][cyclic_number]
        require(state == target, "padded generator path ends at wrong state")

    order = action.get("order")
    require(type(order) is int and order > 0 and
            all(order % cardinality == 0 for cardinality in orbit_cardinalities),
            "orbit cardinality does not divide literal top order")
    return {
        "schema": SCHEMA,
        "selected_sha256": selected_sha256,
        "source_id": action["id"],
        "catalogue_position": value.get("catalogue_position"),
        "family": action.get("family"),
        "degree": n,
        "top_order": order,
        "generator_count": len(generators),
        "state_count": len(states),
        "cyclic_count": len(cyclic_modules),
        "orbit_count": len(orbit_representatives),
        "section_cap": cap,
        "generators": generators,
        "states": [list(row) for row in states],
        "state_coordinate_masks": [coordinate_dual_masks(row, n)
                                   for row in states],
        "orbit_representatives": orbit_representatives,
        "orbit_cardinalities": orbit_cardinalities,
        "orbit_stabilizer_orders": [order // cardinality
                                    for cardinality in orbit_cardinalities],
        "orbit_cyclic_index": orbit_cyclic_index,
        "orbit_cyclic_basis_words": orbit_cyclic_basis_words,
        "cyclic_modules": [list(row) for row in cyclic_modules],
        "cyclic_state_index": cyclic_state_index,
        "cyclic_representatives": cyclic_representatives,
        "cyclic_first_orbit": cyclic_first_orbit,
        "zero_cyclic": zero_cyclic,
        "children": children,
        "child_old_coordinates": child_old_coordinates,
        "child_orbit_words": child_orbit_words,
        "generator_paths": generator_paths,
    }


def write_json(path: Path, value: dict) -> None:
    raw = (json.dumps(value, separators=(",", ":"), sort_keys=True) + "\n").encode()
    require(len(raw) <= OUTPUT_LIMIT, "prepared certificate ceiling reached")
    require(path.parent.exists(), "output parent must already exist")
    path.write_bytes(raw)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True,
                        help="one selected pair-top payload")
    parser.add_argument("--output", type=Path, required=True,
                        help="scratch output path outside the publication repo")
    args = parser.parse_args()
    value, selected_sha256 = read_selected(args.input)
    result = certificate(value, selected_sha256)
    write_json(args.output, result)
    print("WROTE MODULE GENERATORS:", args.output)
    print("ROW:", result["source_id"],
          "states", result["state_count"],
          "cyclic", result["cyclic_count"],
          "orbits", result["orbit_count"],
          "cap", result["section_cap"])


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, EOFError, json.JSONDecodeError,
            KeyError, TypeError) as error:
        print("REFUSED:", error, file=sys.stderr)
        raise SystemExit(1)
