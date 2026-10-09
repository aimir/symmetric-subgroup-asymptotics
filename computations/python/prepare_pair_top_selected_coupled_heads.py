#!/usr/bin/env python3
"""Reconstruct one selected paired-eight coupled-head certificate.

This is the bounded producer for the direct quartet-kernel estimate.  It
consumes one selected action/module row and its already checked natural-module
registry.  It reconstructs, from the literal permutation generators:

* every retained-generator displacement space and its sparse provenance;
* every coordinatewise product of two invariant states;
* every admissible product-plus-displacement denominator; and
* the complete ``head(K)+head(W)+quotientHead(P,L) <= 4`` table.

Only one degree-eight row is accepted.  The output is scratch certificate
data for the Lean renderer; it is not itself a proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from prepare_pair_top_selected_module_generators import (
    Refused,
    basis,
    basis_with_provenance,
    coordinate_dual_masks,
    coordinate_mask,
    permutation_tables,
    require,
)


SCHEMA = "pair-top-selected-coupled-heads-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024


def read_json(path: Path) -> tuple[dict, str]:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected input")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), "input is not a JSON object")
    return value, hashlib.sha256(raw).hexdigest()


def contained(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    return all(coordinate_mask(right, value) is not None for value in left)


def selected_certificate(selected: dict, selected_sha256: str,
                         registry: dict, registry_sha256: str) -> dict:
    require(selected.get("schema_version") == 1 and
            registry.get("schema") == "pair-top-selected-module-generators-v1",
            "unexpected input schema")
    action, stored = selected.get("action"), selected.get("module")
    require(isinstance(action, dict) and isinstance(stored, dict),
            "selected payload lacks action/module")
    require(action.get("id") == stored.get("id") == registry.get("source_id"),
            "selected and registry identifiers disagree")
    require(registry.get("selected_sha256") == selected_sha256,
            "registry was not prepared from this selected payload")
    n = action.get("degree")
    require(n == 8 and action.get("family") == "paired8",
            "coupled-head producer accepts one paired-eight row")
    generators = action.get("generators")
    require(generators == stored.get("generators") == registry.get("generators"),
            "ordered generators disagree")
    tables = permutation_tables(generators, n)
    states = [tuple(row) for row in registry.get("states", [])]
    require(states and states == [tuple(row) for row in stored.get("numerators", [])],
            "registry states differ from stored invariant numerators")
    state_index = {row: index for index, row in enumerate(states)}
    require(len(state_index) == len(states), "duplicate invariant state")

    displacements = []
    heads = []
    raw_displacements: list[list[tuple[int, int, int]]] = []
    for state in states:
        raw = [(table[value] ^ value, generator, vector)
               for generator, table in enumerate(tables)
               for vector, value in enumerate(state)]
        displacement_basis, provenance = basis_with_provenance(
            [value for value, _, _ in raw], n)
        terms = []
        for mask in provenance:
            row = [[raw[index][1], raw[index][2]]
                   for index in range(len(raw)) if (mask >> index) & 1]
            terms.append(row)
        displacements.append({
            "basis": list(displacement_basis),
            "dual": coordinate_dual_masks(displacement_basis, n),
            "terms": terms,
        })
        raw_displacements.append(raw)
        heads.append(len(state) - len(displacement_basis))
    require(heads == stored.get("trivial_heads"),
            "literal displacement heads differ from stored row")

    products = []
    product_state_table = []
    for left in states:
        product_row = []
        product_state_row = []
        for right in states:
            raw = [(x & y, i, j) for i, x in enumerate(left)
                   for j, y in enumerate(right)]
            product_basis, provenance = basis_with_provenance(
                [value for value, _, _ in raw], n)
            require(product_basis in state_index,
                    "coordinate product is absent from invariant states")
            terms = []
            for mask in provenance:
                terms.append([[raw[index][1], raw[index][2]]
                              for index in range(len(raw))
                              if (mask >> index) & 1])
            product_row.append({
                "state": state_index[product_basis],
                "terms": terms,
            })
            product_state_row.append(state_index[product_basis])
        products.append(product_row)
        product_state_table.append(product_state_row)

    denominators = []
    quotient_heads = [[None for _ in states] for _ in states]
    for product_index, product in enumerate(states):
        for upper_index, upper in enumerate(states):
            if not contained(product, upper):
                continue
            raw = [(value, 0, basis_index, 0)
                   for basis_index, value in enumerate(product)]
            raw += [(value, 1, generator, vector)
                    for value, generator, vector
                    in raw_displacements[upper_index]]
            denominator_basis, provenance = basis_with_provenance(
                [value for value, *_ in raw], n)
            terms = []
            for mask in provenance:
                row = []
                for index, (_, kind, first, second) in enumerate(raw):
                    if (mask >> index) & 1:
                        row.append([kind, first] if kind == 0 else
                                   [kind, first, second])
                terms.append(row)
            quotient = len(upper) - len(denominator_basis)
            quotient_heads[product_index][upper_index] = quotient
            denominators.append({
                "product": product_index,
                "upper": upper_index,
                "basis": list(denominator_basis),
                "dual": coordinate_dual_masks(denominator_basis, n),
                "terms": terms,
                "quotient_head": quotient,
            })

    cap = stored.get("composition_cap")
    require(cap == 4, "paired-eight coupled cap changed")
    triple_count = 0
    for left in range(len(states)):
        for right in range(len(states)):
            product = product_state_table[left][right]
            for upper in range(len(states)):
                quotient = quotient_heads[product][upper]
                if quotient is None:
                    continue
                require(heads[left] + heads[right] + quotient <= cap,
                        "coupled-head inequality failed")
                triple_count += 1
    require(triple_count == stored.get("product_triples"),
            "admissible product-triple count differs from stored row")

    return {
        "schema": SCHEMA,
        "selected_sha256": selected_sha256,
        "registry_sha256": registry_sha256,
        "source_id": action["id"],
        "degree": n,
        "generator_count": len(generators),
        "state_count": len(states),
        "cap": cap,
        "product_triples": triple_count,
        "states": [list(row) for row in states],
        "heads": heads,
        "displacements": displacements,
        "products": products,
        "product_state_table": product_state_table,
        "denominators": denominators,
        "quotient_heads": quotient_heads,
    }


def write_json(path: Path, value: dict) -> None:
    raw = (json.dumps(value, separators=(",", ":"), sort_keys=True) +
           "\n").encode()
    require(len(raw) <= OUTPUT_LIMIT, "coupled certificate ceiling reached")
    require(path.parent.exists(), "output parent must already exist")
    path.write_bytes(raw)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selected", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    selected, selected_sha256 = read_json(args.selected)
    registry, registry_sha256 = read_json(args.registry)
    result = selected_certificate(
        selected, selected_sha256, registry, registry_sha256)
    write_json(args.output, result)
    print("WROTE COUPLED HEADS:", args.output)
    print("ROW:", result["source_id"], "states", result["state_count"],
          "denominators", len(result["denominators"]),
          "triples", result["product_triples"], "cap", result["cap"])


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, EOFError, json.JSONDecodeError,
            KeyError, TypeError) as error:
        print("REFUSED:", error, file=sys.stderr)
        raise SystemExit(1)
