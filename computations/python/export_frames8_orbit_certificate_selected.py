#!/usr/bin/env python3
"""Emit one selected eight-frame module certificate in sparse JSON form.

This is deliberately a selected-row emitter.  It never walks all thirty
frames in one invocation.  The output contains exactly the data consumed by
`BinaryInvariantCyclicOrbitRegistry` and
`RepresentationCoinvariantFiniteCertificate`:

* canonical invariant-submodule bases;
* one representative and exact cardinality for each vector orbit;
* the state/distinct-cyclic-submodule join table;
* a basis of the literal generator-displacement subspace of each state;
* sparse linear provenance for every orbit-span, child-join, and
  displacement-basis equality needed by the Lean importer.

The script independently rechecks every property before writing.  It does
not emit a Lean theorem and it does not assert catalogue/action matching;
those are separate checked bindings in the Lean importer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FRAMES = ROOT / "computations/frames/frames8.json"
FRAMES_SHA256 = "f57e814e457b4c66b724e33028fea8d46c1a633738cb00a0abcb59cf663dfe78"
FRAMES_LIMIT = 128 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def pinned_records():
    require(FRAMES.is_file() and not FRAMES.is_symlink(),
            "missing or redirected frames8 source")
    raw = FRAMES.read_bytes()
    require(len(raw) <= FRAMES_LIMIT, "frames8 source ceiling reached")
    require(hashlib.sha256(raw).hexdigest() == FRAMES_SHA256,
            "frames8 source digest changed")
    records = json.loads(raw)
    require(isinstance(records, list) and len(records) == 30,
            "unexpected frames8 row count")
    return records


def basis(vectors):
    """Canonical reduced binary echelon basis in the frames8 convention."""
    rows = [0] * 16
    for value in vectors:
        value = int(value)
        while value:
            pivot = value.bit_length() - 1
            if rows[pivot]:
                value ^= rows[pivot]
            else:
                rows[pivot] = value
                break
    for pivot in range(16):
        if rows[pivot]:
            for higher in range(pivot + 1, 16):
                if (rows[higher] >> pivot) & 1:
                    rows[higher] ^= rows[pivot]
    return tuple(value for value in rows if value)


def basis_with_provenance(vectors):
    """Canonical basis and F2 provenance in the supplied vector list."""
    vectors = tuple(map(int, vectors))
    rows = [0] * 16
    provenance = [0] * 16
    for index, original in enumerate(vectors):
        value = original
        witness = 1 << index
        while value:
            pivot = value.bit_length() - 1
            if rows[pivot]:
                value ^= rows[pivot]
                witness ^= provenance[pivot]
            else:
                rows[pivot] = value
                provenance[pivot] = witness
                break
        # If `value` vanishes then `witness` records a genuine dependency
        # among the supplied rows.  Such a witness need not be zero; the
        # dependent row is simply omitted from the resulting basis.
    for pivot in range(16):
        if rows[pivot]:
            for higher in range(pivot + 1, 16):
                if (rows[higher] >> pivot) & 1:
                    rows[higher] ^= rows[pivot]
                    provenance[higher] ^= provenance[pivot]
    result_rows, result_provenance = [], []
    for value, witness in zip(rows, provenance):
        if value:
            result_rows.append(value)
            result_provenance.append(witness)
    for value, witness in zip(result_rows, result_provenance):
        actual = 0
        for index, original in enumerate(vectors):
            if (witness >> index) & 1:
                actual ^= original
        require(actual == value, "binary basis provenance mismatch")
    return tuple(result_rows), tuple(result_provenance)


def coordinate_mask(rows, value):
    """Coordinates of value in an echelon basis, or None outside its span."""
    value = int(value)
    result = 0
    for index in range(len(rows) - 1, -1, -1):
        row = rows[index]
        if (value >> (row.bit_length() - 1)) & 1:
            value ^= row
            result ^= 1 << index
    return result if value == 0 else None


def coordinate_dual_masks(rows):
    """Rows of the left-inverse coordinate matrix on the ambient 16-space."""
    output = [0] * len(rows)
    for coordinate in range(16):
        value = coordinate_mask(rows, 1 << coordinate)
        if value is None:
            # The coordinate map is allowed to be arbitrary off the subspace;
            # zero is the convenient checked extension.
            continue
        for index in range(len(rows)):
            if (value >> index) & 1:
                output[index] |= 1 << coordinate
    # Standard-basis coordinates outside the subspace cannot all be zero if
    # the displayed rows are correlated.  Construct a true linear left
    # inverse instead by recording elimination against the displayed pivots.
    output = [0] * len(rows)
    for coordinate in range(16):
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
        require(sum(((row & mask).bit_count() & 1) << j
                    for j, mask in enumerate(output)) == 1 << index,
                "coordinate dual is not a left inverse")
    return output


def contains(rows, value):
    for row in reversed(rows):
        if (value >> (row.bit_length() - 1)) & 1:
            value ^= row
    return value == 0


def matrix_table(matrix):
    require(len(matrix) == 16 and len(basis(matrix)) == 16,
            "generator matrix is not invertible")
    table = [0] * (1 << 16)
    for value in range(1, 1 << 16):
        low = value & -value
        table[value] = table[value - low] ^ matrix[low.bit_length() - 1]
    return table


def inverse_matrix(matrix, table):
    inverse = []
    position = {value: source for source, value in enumerate(table)}
    for coordinate in range(16):
        require((1 << coordinate) in position,
                "generator matrix table is not onto")
        inverse.append(position[1 << coordinate])
    require(len(basis(inverse)) == 16, "inverse matrix is singular")
    return inverse


def orbit_with_words(seed, tables):
    """One generator orbit with a positive-generator word for each point."""
    orbit = [seed]
    words = [[]]
    position = {seed: 0}
    for index, value in enumerate(orbit):
        for generator, table in enumerate(tables):
            image = table[value]
            if image not in position:
                position[image] = len(orbit)
                orbit.append(image)
                words.append(words[index] + [generator])
    return orbit, words


def selected_words(mask, words):
    return [words[index] for index in range(len(words))
            if (mask >> index) & 1]


def selected_certificate(row_index: int):
    records = pinned_records()
    require(0 <= row_index < len(records), "row index is out of range")
    record = records[row_index]
    top_id, order, local, kernel, z, ceiling, mu, matrices, raw_modules = record
    tables = [matrix_table(matrix) for matrix in matrices]
    inverse_matrices = [inverse_matrix(matrix, table)
                        for matrix, table in zip(matrices, tables)]
    inverse_tables = [matrix_table(matrix) for matrix in inverse_matrices]

    modules = sorted({basis(rows) for rows in raw_modules},
                     key=lambda rows: (len(rows), rows))
    require(len(modules) == len(raw_modules), "duplicate invariant modules")
    require(() in modules, "zero module missing")
    require(basis(1 << i for i in range(16)) in modules,
            "whole module missing")
    module_index = {rows: i for i, rows in enumerate(modules)}

    # Orbit cardinalities, together with pairwise separation of the selected
    # representatives, certify coverage without emitting one path per vector.
    seen = bytearray(1 << 16)
    representatives = []
    orbit_cardinalities = []
    orbit_cyclic_bases = []
    orbit_cyclic_basis_words = []
    for seed in range(1 << 16):
        if seen[seed]:
            continue
        representatives.append(seed)
        orbit, words = orbit_with_words(seed, tables)
        require(all(not seen[value] for value in orbit),
                "selected vector orbits overlap")
        for value in orbit:
            seen[value] = 1
        orbit_cardinalities.append(len(orbit))
        cyclic_basis, cyclic_provenance = basis_with_provenance(orbit)
        orbit_cyclic_bases.append(cyclic_basis)
        orbit_cyclic_basis_words.append(
            [selected_words(mask, words) for mask in cyclic_provenance])
    require(all(seen), "orbits do not cover the vector space")
    require(sum(orbit_cardinalities) == 1 << 16,
            "orbit cardinalities do not exhaust the vector space")
    require(all(order % size == 0 for size in orbit_cardinalities),
            "vector orbit size does not divide the top order")
    orbit_stabilizer_orders = [order // size for size in orbit_cardinalities]
    require(all(rows in module_index for rows in orbit_cyclic_bases),
            "a cyclic orbit module is absent from the module list")

    # Several vector orbits generate the same invariant submodule.  Coverage
    # is indexed by all vector orbits, while joins use only the distinct
    # cyclic modules.  This is the 39,449-cell compression checked by
    # verify_modules8.py.
    cyclic_modules = sorted(set(orbit_cyclic_bases),
                            key=lambda rows: (len(rows), rows))
    cyclic_index = {rows: i for i, rows in enumerate(cyclic_modules)}
    orbit_cyclic_index = [cyclic_index[rows] for rows in orbit_cyclic_bases]
    cyclic_first_orbit = [orbit_cyclic_index.index(i)
                          for i in range(len(cyclic_modules))]
    cyclic_representatives = [representatives[i] for i in cyclic_first_orbit]
    cyclic_state_index = [module_index[rows] for rows in cyclic_modules]

    children = []
    child_old_coordinates = []
    child_orbit_words = []
    displacement_bases = []
    displacement_provenance = []
    head_dimensions = []
    for state in modules:
        require(all(contains(state, table[value])
                    for table in tables for value in state),
                "listed module is not invariant")
        state_children = []
        state_old_coordinates = []
        state_orbit_words = []
        for cyclic_number, cyclic in enumerate(cyclic_modules):
            representative = cyclic_representatives[cyclic_number]
            orbit, words = orbit_with_words(representative, tables)
            child, child_provenance = basis_with_provenance(state + tuple(orbit))
            require(child in module_index, "state/orbit join is absent")
            state_children.append(module_index[child])
            old_row, orbit_row = [], []
            for mask in child_provenance:
                old_row.append(mask & ((1 << len(state)) - 1))
                orbit_row.append(selected_words(mask >> len(state), words))
            state_old_coordinates.append(old_row)
            state_orbit_words.append(orbit_row)
        children.append(state_children)
        child_old_coordinates.append(state_old_coordinates)
        child_orbit_words.append(state_orbit_words)
        displacement_terms = [table[value] ^ value
                              for table in tables for value in state]
        displacement, displacement_witness = basis_with_provenance(
            displacement_terms)
        require(all(contains(state, value) for value in displacement),
                "displacement escaped the invariant module")
        displacement_bases.append(displacement)
        displacement_provenance.append([
            [[index // len(state), index % len(state)]
             for index in range(len(displacement_terms))
             if (mask >> index) & 1]
            for mask in displacement_witness
        ] if state else [])
        head_dimensions.append(len(state) - len(displacement))

    module_coordinate_masks = [coordinate_dual_masks(state)
                               for state in modules]
    module_generator_coordinates = []
    module_inverse_generator_coordinates = []
    for state in modules:
        positive, negative = [], []
        for table, inverse_table in zip(tables, inverse_tables):
            positive_row = [coordinate_mask(state, table[value])
                            for value in state]
            negative_row = [coordinate_mask(state, inverse_table[value])
                            for value in state]
            require(all(value is not None for value in positive_row + negative_row),
                    "listed module is not invariant in both directions")
            positive.append(positive_row)
            negative.append(negative_row)
        module_generator_coordinates.append(positive)
        module_inverse_generator_coordinates.append(negative)

    require(max(head_dimensions) == mu and mu <= 2 and z <= 2,
            "stored top/module head maxima do not match recomputation")
    return {
        "schema": "frames8-selected-cyclic-orbit-certificate-v5",
        "source_sha256": FRAMES_SHA256,
        "source_row": row_index,
        "top_id": top_id,
        "top_order": order,
        "local_quotient_order": local,
        "stabilizer_kernel_order": kernel,
        "top_relative_binary_rank": z,
        "sylow3_fixed_dimension": ceiling,
        "maximum_module_head": mu,
        "generator_matrices": matrices,
        "inverse_generator_matrices": inverse_matrices,
        "modules": [list(rows) for rows in modules],
        "module_coordinate_masks": module_coordinate_masks,
        "module_generator_coordinates": module_generator_coordinates,
        "module_inverse_generator_coordinates":
            module_inverse_generator_coordinates,
        "orbit_representatives": representatives,
        "orbit_cardinalities": orbit_cardinalities,
        "orbit_stabilizer_orders": orbit_stabilizer_orders,
        "cyclic_modules": [list(rows) for rows in cyclic_modules],
        "cyclic_state_index": cyclic_state_index,
        "cyclic_representatives": cyclic_representatives,
        "cyclic_first_orbit": cyclic_first_orbit,
        "orbit_cyclic_index": orbit_cyclic_index,
        "orbit_cyclic_basis_words": orbit_cyclic_basis_words,
        "children": children,
        "child_old_coordinates": child_old_coordinates,
        "child_orbit_words": child_orbit_words,
        "displacement_bases": [list(rows) for rows in displacement_bases],
        "displacement_coordinate_masks":
            [coordinate_dual_masks(rows) for rows in displacement_bases],
        "displacement_provenance": displacement_provenance,
        "head_dimensions": head_dimensions,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", type=int, required=True,
                        help="zero-based frames8.json row index")
    parser.add_argument("--output", type=Path,
                        help="output path; omit to print JSON to stdout")
    args = parser.parse_args()
    certificate = selected_certificate(args.row)
    text = json.dumps(certificate, separators=(",", ":")) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
