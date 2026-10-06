#!/usr/bin/env python3
"""Prepare one bounded top/radical certificate for an eight-frame row.

The inputs are one JSON file from ``export_selected_frame8_binding.g`` and
one JSON file from ``export_frames8_orbit_certificate_selected.py``.  This
script has no directory scan and no all-row mode.  It rechecks the literal
degree-eight group, its complete class and normal lists, every normal join,
every exact relative binary radical, the point-stabilizer epimorphism and
Schreier induction formula, and the degree-32 binary-basis/matrix binding.
The output is still untrusted certificate data: the Lean emitter must replay
all word and finite equations in the kernel.

No subprocess, GAP process, Lean process, or other exporter is invoked.
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
    enumerate_generated,
    generator_enumeration,
    identity,
    inverse,
    join_transition_words,
    normality_words,
    word_generator,
)


BINDING_SCHEMA = "frames8-selected-binding-v1"
MODULE_SCHEMA = "frames8-selected-cyclic-orbit-certificate-v5"
BINDINGS_SHA256 = "d5a3ef513faa40a10f666478628f5f23f0a156db58e75d8a7be4068c3c2fa3fa"
FRAMES_SHA256 = "f57e814e457b4c66b724e33028fea8d46c1a633738cb00a0abcb59cf663dfe78"
INPUT_LIMIT = 8 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024
MAX_TOP_ORDER = 1_152
MAX_NORMALS = 256
MAX_CLASSES = 256
MAX_RADICAL_WORD_NODES = 2_304
MAX_RADICAL_WORD_DEPTH = 256


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def read_json(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected input {path}")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "selected input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), "selected input is not an object")
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


def gap_product(left, right, budget: Budget):
    """Multiply exported GAP permutation rows in GAP's right-action order."""
    # The exported row of g is ``i |-> i^g``.  Hence the row of ``g * h``
    # first applies g and then h, whereas ``compose(a, b)`` first applies b.
    return compose(right, left, budget)


def paired_hom_enumeration(generators, images, width: int,
                            image_width: int, budget: Budget) -> dict:
    """Enumerate a presented finite homomorphism and reject inconsistent words."""
    require(len(generators) == len(images) and generators,
            "local generator/image lists have different or zero width")
    one = identity(width)
    image_one = identity(image_width)
    rows = [one]
    image_rows = [image_one]
    parents = [0]
    letters = [0]
    position = {one: 0}
    cursor = 0
    while cursor < len(rows):
        for letter, (generator, image) in enumerate(zip(generators, images)):
            child = gap_product(rows[cursor], generator, budget)
            child_image = gap_product(image_rows[cursor], image, budget)
            known = position.get(child)
            if known is None:
                require(len(rows) < MAX_TOP_ORDER,
                        "local homomorphism state ceiling reached")
                position[child] = len(rows)
                rows.append(child)
                image_rows.append(child_image)
                parents.append(cursor)
                letters.append(letter)
            else:
                require(image_rows[known] == child_image,
                        "local images do not define a homomorphism")
        cursor += 1

    words = []
    for index in range(len(rows)):
        word = []
        while index:
            word.append(letters[index])
            index = parents[index]
        word.reverse()
        words.append(word)
    return {
        "rows": rows,
        "position": position,
        "images": image_rows,
        "parents": parents,
        "letters": letters,
        "words": words,
    }


def validate_induced_binding(binding: dict, top, expected_local_order: int,
                             budget: Budget) -> dict:
    """Reconstruct the literal local quotient and the 32-point induction.

    This is the Python-side independent audit of the GAP ``BuildFrame``
    formula.  The returned Schreier words are still untrusted data: a Lean
    renderer must replay their finite equations in the kernel.
    """
    top_rows = set(top.rows)
    top_generators = permutation_rows(binding["top_generators"], 8, budget)
    stabilizer_rows = [row for row in top.rows if row[0] == 0]
    stabilizer_set = set(stabilizer_rows)
    require(len(stabilizer_rows) * 8 == len(top.rows),
            "literal point stabilizer has the wrong index")

    stabilizer_generators = permutation_rows(
        binding["stabilizer_generators"], 8, budget)
    local_images = permutation_rows(binding["local_images"], 3, budget)
    hom = paired_hom_enumeration(
        stabilizer_generators, local_images, 8, 3, budget)
    require(set(hom["rows"]) == stabilizer_set,
            "stored local generators do not generate the point stabilizer")
    image_set = set(hom["images"])
    require(expected_local_order in (3, 6) and
            len(image_set) == expected_local_order,
            "stored local map has the wrong order-three/order-six image")

    kernel_generators = permutation_rows(
        binding["kernel_generators"], 8, budget)
    kernel = generator_enumeration(
        kernel_generators, 8, budget, max_states=MAX_TOP_ORDER)
    hom_kernel = {row for row, image in zip(hom["rows"], hom["images"])
                  if image == identity(3)}
    require(set(kernel.rows) == hom_kernel and
            len(hom_kernel) == binding["kernel_order"],
            "stored kernel is not the exact kernel of the local map")

    representatives = permutation_rows(
        binding["coset_representatives"], 8, budget)
    require(len(representatives) == 8 and
            all(representative in top_rows for representative in representatives),
            "invalid right-coset representative list")
    cosets = [frozenset(gap_product(h, representative, budget)
                        for h in stabilizer_rows)
              for representative in representatives]
    require(len(set(cosets)) == 8 and
            set().union(*cosets) == top_rows,
            "right-coset representatives do not partition the top")

    induced = permutation_rows(binding["induced_generators"], 32, budget)
    require(len(induced) == len(top_generators),
            "induced/top generator count mismatch")
    coset_next = []
    twist_words = []
    twist_images = []
    reconstructed = []
    for generator, supplied in zip(top_generators, induced):
        generator_next = []
        generator_words = []
        generator_images = []
        expected = [0] * 32
        for i, representative in enumerate(representatives):
            product = gap_product(representative, generator, budget)
            destinations = [j for j, coset in enumerate(cosets)
                            if product in coset]
            require(len(destinations) == 1,
                    "top generator has no unique Schreier destination")
            j = destinations[0]
            twist = gap_product(
                product, inverse(representatives[j], budget), budget)
            require(twist in stabilizer_set,
                    "Schreier twist escaped the point stabilizer")
            twist_index = hom["position"].get(twist)
            require(twist_index is not None,
                    "Schreier twist lacks a stabilizer word")
            local_image = hom["images"][twist_index]
            generator_next.append(j)
            generator_words.append(hom["words"][twist_index])
            generator_images.append(list(x + 1 for x in local_image))
            for k in range(4):
                # The local C3 or S3 permutation fixes the fourth affine point.
                local_target = local_image[k] if k < 3 else 3
                expected[4 * i + k] = 4 * j + local_target
        expected_row = tuple(expected)
        require(expected_row == supplied,
                "stored induced generator does not match the Schreier formula")
        coset_next.append(generator_next)
        twist_words.append(generator_words)
        twist_images.append(generator_images)
        reconstructed.append(list(x + 1 for x in expected_row))

    return {
        "stabilizer_order": len(stabilizer_rows),
        "local_image_order": len(image_set),
        "kernel_order": len(hom_kernel),
        "coset_next": coset_next,
        "twist_stabilizer_words": twist_words,
        "twist_local_images": twist_images,
        "reconstructed_induced_generators": reconstructed,
    }


def packed(row: tuple[int, ...]) -> int:
    width = len(row)
    return sum(value * width ** i for i, value in enumerate(row))


def positive_cayley(generators, width: int, expected_order: int,
                    budget: Budget) -> dict:
    alphabet = [(g, word_generator(i)) for i, g in enumerate(generators)]
    group = enumerate_generated(
        alphabet, width, budget, max_states=MAX_TOP_ORDER)
    require(len(group.rows) == expected_order,
            "positive-generator Cayley enumeration has wrong order")
    next_rows = [[group.position[compose(x, g, budget)]
                  for g in generators] for x in group.rows]
    inverse_generators = [inverse(g, budget) for g in generators]
    previous_rows = [[group.position[compose(x, g, budget)]
                      for g in inverse_generators] for x in group.rows]
    depths = [0] * len(group.rows)
    words: list[list[int]] = [[] for _ in group.rows]
    for i in range(1, len(group.rows)):
        parent = group.parents[i]
        require(parent < i, "Cayley parent is not acyclic")
        depths[i] = depths[parent] + 1
        words[i] = words[parent] + [group.letters[i]]
    return {
        "rows": [list(x + 1 for x in row) for row in group.rows],
        "codes": [packed(row) for row in group.rows],
        "identity": 0,
        "parents": list(group.parents),
        "letters": list(group.letters),
        "ranks": depths,
        "words": words,
        "next": next_rows,
        "previous": previous_rows,
    }


def normal_closure_child(ambient, parent_generators, representative,
                         width: int, budget: Budget):
    conjugates = []
    seen = set()
    for g in ambient.rows:
        atom = conjugate(g, representative, budget)
        if atom not in seen:
            seen.add(atom)
            conjugates.append(atom)
    return generator_enumeration(
        parent_generators + conjugates, width, budget,
        max_states=MAX_TOP_ORDER)


def radical_search(ambient_generators, normal, lookup, budget: Budget) -> dict:
    """Close generator squares and mixed commutators with explicit DAG words."""
    one = identity(8)
    allowed = set(normal["rows"])
    rows = [one]
    position = {one: 0}
    nodes = [("one",)]
    depths = [0]

    def add(value, node, depth):
        budget.tick()
        require(value in allowed, "relative radical escaped its normal state")
        if value in position:
            return position[value]
        require(len(rows) < MAX_RADICAL_WORD_NODES,
                "relative radical state ceiling reached")
        require(depth <= MAX_RADICAL_WORD_DEPTH,
                "relative radical word-depth ceiling reached")
        position[value] = len(rows)
        rows.append(value)
        nodes.append(node)
        depths.append(depth)
        return position[value]

    inverse_ambient = [inverse(g, budget) for g in ambient_generators]
    powers, mixed, seeds = [], [], []
    for j, n in enumerate(normal["generators"]):
        square = compose(n, n, budget)
        powers.append(square)
        seeds.append(add(square, ("power", j), 1))
        inverse_n = inverse(n, budget)
        mixed_row = []
        for i, g in enumerate(ambient_generators):
            value = compose(
                compose(compose(n, g, budget), inverse_n, budget),
                inverse_ambient[i], budget)
            mixed_row.append(value)
            seeds.append(add(value, ("mixed", j, i), 1))
        mixed.append(mixed_row)
    seeds = sorted(set(seeds) - {0})
    cursor = 0
    while cursor < len(rows):
        x = rows[cursor]
        for seed in seeds:
            add(compose(x, rows[seed], budget),
                ("mul", cursor, seed),
                1 + max(depths[cursor], depths[seed]))
        for i, g in enumerate(ambient_generators):
            add(compose(compose(g, x, budget), inverse_ambient[i], budget),
                ("conj", i, cursor), 1 + depths[cursor])
            add(compose(compose(inverse_ambient[i], x, budget), g, budget),
                ("conjInv", i, cursor), 1 + depths[cursor])
        cursor += 1
    target = lookup.get(frozenset(rows))
    require(target is not None,
            "exact relative radical is absent from normal-state list")
    target_state = normal["all_states"][target]
    target_generator_nodes = []
    for value in target_state["generators"]:
        require(value in position, "radical-state generator lacks radical word")
        target_generator_nodes.append(position[value])
    target_enum = target_state["enumeration"]
    power_words = [target_enum.word(target_enum.position[x]) for x in powers]
    mixed_words = [[target_enum.word(target_enum.position[x]) for x in row]
                   for row in mixed]
    quotient = len(normal["rows"]) // len(target_state["rows"])
    require(len(normal["rows"]) == quotient * len(target_state["rows"]),
            "relative radical order does not divide the normal order")
    require(quotient in (1, 2, 4), "relative binary head exceeds two")
    head_rank = {1: 0, 2: 1, 4: 2}[quotient]
    return {
        "target": target,
        "head_rank": head_rank,
        "nodes": [list(node) for node in nodes],
        "target_generator_nodes": target_generator_nodes,
        "power_words": power_words,
        "mixed_words": mixed_words,
        "maximum_depth": max(depths),
    }


def validate_binary_basis(binding: dict, module: dict, budget: Budget) -> None:
    induced = permutation_rows(binding["induced_generators"], 32, budget)
    basis = permutation_rows(binding["binary_basis"], 32, budget)
    require(len(basis) == 16, "binary basis does not have sixteen entries")
    one = identity(32)
    for x in basis:
        require(compose(x, x, budget) == one, "binary basis row is not involutory")
    for x in basis:
        for y in basis:
            require(compose(x, y, budget) == compose(y, x, budget),
                    "binary basis rows do not commute")
    values = [one]
    coordinates = {one: 0}
    for i, generator in enumerate(basis):
        old = list(values)
        for value in old:
            product = compose(value, generator, budget)
            require(product not in coordinates, "binary basis is dependent")
            coordinates[product] = len(values)
            values.append(product)
    require(len(values) == 1 << 16, "binary basis does not span the full frame")
    matrices = module["generator_matrices"]
    require(len(matrices) == len(induced), "matrix generator count mismatch")
    for g, matrix in zip(induced, matrices):
        require(isinstance(matrix, list) and len(matrix) == 16,
                "invalid binary generator matrix")
        for x, claimed in zip(basis, matrix):
            actual = conjugate(g, x, budget)
            require(actual in coordinates, "conjugated binary basis escaped frame")
            require(coordinates[actual] == claimed,
                    "literal conjugation matrix mismatch")


def binary_apply(matrix, value, budget: Budget) -> int:
    require(isinstance(matrix, list) and len(matrix) == 16,
            "invalid binary matrix")
    result = 0
    for index, image in enumerate(matrix):
        require(type(image) is int and 0 <= image < (1 << 16),
                "invalid binary matrix column")
        if (value >> index) & 1:
            result ^= image
        budget.tick()
    return result


def binary_word_apply(matrices, word, value, budget: Budget) -> int:
    require(isinstance(word, list), "binary action word is not a list")
    for generator in word:
        require(type(generator) is int and 0 <= generator < len(matrices),
                "binary action word has invalid generator")
        value = binary_apply(matrices[generator], value, budget)
    return value


def binary_sum_mask(rows, mask, budget: Budget) -> int:
    require(type(mask) is int and 0 <= mask < (1 << len(rows)),
            "binary coordinate mask is out of range")
    result = 0
    for index, value in enumerate(rows):
        require(type(value) is int and 0 <= value < (1 << 16),
                "invalid binary vector")
        if (mask >> index) & 1:
            result ^= value
        budget.tick()
    return result


def validate_module_provenance(module: dict, budget: Budget) -> None:
    """Recheck every sparse linear witness retained for Lean rendering."""
    matrices = module["generator_matrices"]
    inverse_matrices = module["inverse_generator_matrices"]
    require(len(matrices) == len(inverse_matrices),
            "inverse matrix count mismatch")
    for matrix, inverse_matrix in zip(matrices, inverse_matrices):
        for coordinate in range(16):
            vector = 1 << coordinate
            require(binary_apply(inverse_matrix,
                                 binary_apply(matrix, vector, budget), budget) ==
                    vector,
                    "binary inverse matrix mismatch")

    modules = module["modules"]
    coordinate_masks = module["module_coordinate_masks"]
    positive = module["module_generator_coordinates"]
    negative = module["module_inverse_generator_coordinates"]
    require(len(modules) == len(coordinate_masks) == len(positive) ==
            len(negative), "module-coordinate row count mismatch")
    for rows, dual, pos_row, neg_row in zip(
            modules, coordinate_masks, positive, negative):
        require(len(dual) == len(rows), "module dual width mismatch")
        for index, value in enumerate(rows):
            actual = sum((((value & mask).bit_count() & 1) << j)
                         for j, mask in enumerate(dual))
            require(actual == 1 << index,
                    "module coordinate map is not a left inverse")
        require(len(pos_row) == len(matrices) == len(neg_row),
                "module generator-coordinate row mismatch")
        for generator, (matrix, inverse_matrix) in enumerate(
                zip(matrices, inverse_matrices)):
            require(len(pos_row[generator]) == len(rows) and
                    len(neg_row[generator]) == len(rows),
                    "module generator-coordinate basis width mismatch")
            for index, value in enumerate(rows):
                require(binary_sum_mask(rows, pos_row[generator][index], budget) ==
                        binary_apply(matrix, value, budget),
                        "positive module coordinate mismatch")
                require(binary_sum_mask(rows, neg_row[generator][index], budget) ==
                        binary_apply(inverse_matrix, value, budget),
                        "negative module coordinate mismatch")

    orbit_representatives = module["orbit_representatives"]
    orbit_cyclic_index = module["orbit_cyclic_index"]
    orbit_basis_words = module["orbit_cyclic_basis_words"]
    cyclic_modules = module["cyclic_modules"]
    cyclic_representatives = module["cyclic_representatives"]
    cyclic_first_orbit = module["cyclic_first_orbit"]
    cyclic_state_index = module["cyclic_state_index"]
    require(len(orbit_representatives) == len(orbit_cyclic_index) ==
            len(orbit_basis_words), "orbit provenance row count mismatch")
    require(len(cyclic_modules) == len(cyclic_representatives) ==
            len(cyclic_first_orbit) == len(cyclic_state_index),
            "cyclic-module row count mismatch")
    for cyclic, first in enumerate(cyclic_first_orbit):
        require(orbit_cyclic_index[first] == cyclic and
                orbit_representatives[first] == cyclic_representatives[cyclic],
                "cyclic representative is not its selected orbit row")
        require(modules[cyclic_state_index[cyclic]] == cyclic_modules[cyclic],
                "cyclic module is not its selected invariant state")
    for representative, cyclic, basis_words in zip(
            orbit_representatives, orbit_cyclic_index, orbit_basis_words):
        require(len(basis_words) == len(cyclic_modules[cyclic]),
                "orbit-span basis width mismatch")
        for target, words in zip(cyclic_modules[cyclic], basis_words):
            actual = 0
            for word in words:
                actual ^= binary_word_apply(
                    matrices, word, representative, budget)
            require(actual == target, "orbit-span provenance mismatch")

    children = module["children"]
    child_old = module["child_old_coordinates"]
    child_orbit = module["child_orbit_words"]
    require(len(children) == len(modules) == len(child_old) == len(child_orbit),
            "child table state count mismatch")
    for state_index, state in enumerate(modules):
        require(len(children[state_index]) == len(cyclic_modules) ==
                len(child_old[state_index]) == len(child_orbit[state_index]),
                "child table cyclic width mismatch")
        for cyclic in range(len(cyclic_modules)):
            child = modules[children[state_index][cyclic]]
            require(len(child_old[state_index][cyclic]) == len(child) ==
                    len(child_orbit[state_index][cyclic]),
                    "child basis witness width mismatch")
            representative = cyclic_representatives[cyclic]
            for target, old_mask, words in zip(
                    child, child_old[state_index][cyclic],
                    child_orbit[state_index][cyclic]):
                actual = binary_sum_mask(state, old_mask, budget)
                for word in words:
                    actual ^= binary_word_apply(
                        matrices, word, representative, budget)
                require(actual == target, "child-join provenance mismatch")

    displacement = module["displacement_bases"]
    displacement_dual = module["displacement_coordinate_masks"]
    displacement_provenance = module["displacement_provenance"]
    require(len(displacement) == len(modules) == len(displacement_dual) ==
            len(displacement_provenance),
            "displacement row count mismatch")
    for state, rows, dual, provenance in zip(
            modules, displacement, displacement_dual,
            displacement_provenance):
        require(len(rows) == len(dual) == len(provenance),
                "displacement basis width mismatch")
        for index, target in enumerate(rows):
            actual_coordinate = sum(
                (((target & mask).bit_count() & 1) << j)
                for j, mask in enumerate(dual))
            require(actual_coordinate == 1 << index,
                    "displacement coordinate map is not a left inverse")
            actual = 0
            for generator, state_basis in provenance[index]:
                require(0 <= generator < len(matrices) and
                        0 <= state_basis < len(state),
                        "displacement term index is out of range")
                value = state[state_basis]
                actual ^= binary_apply(matrices[generator], value, budget) ^ value
            require(actual == target, "displacement provenance mismatch")


def prepare(binding: dict, module: dict, budget: Budget) -> dict:
    require(binding.get("schema") == BINDING_SCHEMA,
            "unexpected selected binding schema")
    require(binding.get("bindings_sha256") == BINDINGS_SHA256,
            "selected binding source digest changed")
    require(module.get("schema") == MODULE_SCHEMA,
            "unexpected selected module schema")
    require(module.get("source_sha256") == FRAMES_SHA256,
            "selected module source digest changed")
    require(binding.get("row") == module.get("source_row"),
            "binding/module row mismatch")
    require(binding.get("top_index") == module.get("top_id") - 1,
            "binding/module top mismatch")
    require(binding.get("top_order") == module.get("top_order"),
            "binding/module top order mismatch")
    require(binding.get("kernel_order") == module.get("stabilizer_kernel_order"),
            "binding/module kernel order mismatch")
    require(module.get("local_quotient_order") in (3, 6),
            "unexpected local quotient order")

    generators = permutation_rows(binding["top_generators"], 8, budget)
    top = generator_enumeration(
        generators, 8, budget, max_states=MAX_TOP_ORDER)
    require(len(top.rows) == binding["top_order"] <= MAX_TOP_ORDER,
            "literal top order mismatch")
    cayley = positive_cayley(generators, 8, len(top.rows), budget)

    representatives = permutation_rows(
        binding["class_representatives"], 8, budget)
    supplied_class_sizes = binding["class_sizes"]
    require(len(representatives) == len(supplied_class_sizes) <= MAX_CLASSES,
            "invalid selected class list")
    class_sets, centralizer_orders = [], []
    for representative, supplied_size in zip(representatives, supplied_class_sizes):
        require(representative in top.position,
                "class representative is outside the top")
        conjugates = {conjugate(g, representative, budget) for g in top.rows}
        centralizer = [g for g in top.rows
                       if compose(g, representative, budget) ==
                       compose(representative, g, budget)]
        require(len(conjugates) == supplied_size,
                "supplied conjugacy class size mismatch")
        require(len(conjugates) * len(centralizer) == len(top.rows),
                "class/centralizer orbit-stabilizer mismatch")
        class_sets.append(conjugates)
        centralizer_orders.append(len(centralizer))
    require(all(class_sets[i].isdisjoint(class_sets[j])
                for i in range(len(class_sets)) for j in range(i)),
            "selected conjugacy classes overlap")
    require(sum(map(len, class_sets)) == len(top.rows),
            "selected conjugacy classes do not exhaust the top")
    # `class_code` is consumed at the executable Cayley-row indices.  The
    # breadth-first literal enumeration above is only used to verify the
    # supplied conjugacy classes; `positive_cayley` has its own certified row
    # order, which need not coincide with `top.rows`.
    class_code = []
    for row1 in cayley["rows"]:
        row = tuple(value - 1 for value in row1)
        labels = [i for i, conjugacy_class in enumerate(class_sets)
                  if row in conjugacy_class]
        require(len(labels) == 1,
                "literal top row does not have a unique class label")
        class_code.append(labels[0])

    raw_normal_generators = binding["normal_generators"]
    supplied_normal_orders = binding["normal_orders"]
    require(isinstance(raw_normal_generators, list) and
            len(raw_normal_generators) == len(supplied_normal_orders) <= MAX_NORMALS,
            "invalid selected normal list")
    parsed_normal_generators = [permutation_rows(row, 8, budget)
                                for row in raw_normal_generators]
    generator_width = max([1] + [len(row) for row in parsed_normal_generators])
    one = identity(8)
    states = []
    for generators0, supplied_order in zip(
            parsed_normal_generators, supplied_normal_orders):
        generators1 = generators0 + [one] * (generator_width - len(generators0))
        enumeration = generator_enumeration(
            generators1, 8, budget, max_states=MAX_TOP_ORDER)
        require(len(enumeration.rows) == supplied_order,
                "normal-state order mismatch")
        require(set(enumeration.rows) <= set(top.rows),
                "normal state escaped the literal top")
        states.append({"generators": generators1,
                       "rows": enumeration.rows,
                       "enumeration": enumeration})
    lookup = {frozenset(state["rows"]): i for i, state in enumerate(states)}
    require(len(lookup) == len(states), "selected normal states are duplicated")
    for state in states:
        state["all_states"] = states

    normality = [normality_words(generators, state["generators"], 8, budget,
                                 max_states=MAX_TOP_ORDER)
                 for state in states]
    children, transitions = [], []
    for state in states:
        child_row, transition_row = [], []
        for representative in representatives:
            child_group = normal_closure_child(
                top, state["generators"], representative, 8, budget)
            child = lookup.get(frozenset(child_group.rows))
            require(child is not None, "normal join escaped the selected state list")
            child_row.append(child)
            transition_row.append(join_transition_words(
                generators, state["generators"], representative,
                states[child]["generators"], 8, budget,
                max_states=MAX_TOP_ORDER))
        children.append(child_row)
        transitions.append(transition_row)
    radical = [radical_search(generators, state, lookup, budget)
               for state in states]
    require(max(row["head_rank"] for row in radical) ==
            module["top_relative_binary_rank"] <= 2,
            "top relative binary-rank maximum mismatch")

    induced_binding = validate_induced_binding(
        binding, top, module["local_quotient_order"], budget)
    validate_binary_basis(binding, module, budget)
    validate_module_provenance(module, budget)
    return {
        "schema": "frames8-selected-top-certificate-v1",
        "source_row": binding["row"],
        "top_index": binding["top_index"],
        "top_order": len(top.rows),
        "generators": binding["top_generators"],
        "cayley": cayley,
        "class_representatives": binding["class_representatives"],
        "class_sizes": supplied_class_sizes,
        "centralizer_orders": centralizer_orders,
        "class_code": class_code,
        "normal_generator_width": generator_width,
        "normal_generators": [
            [list(x + 1 for x in g) for g in state["generators"]]
            for state in states],
        "normal_orders": [len(state["rows"]) for state in states],
        "normality": normality,
        "children": children,
        "transitions": transitions,
        "radicals": radical,
        "induced_binding": induced_binding,
        "module_certificate": module,
        "binding": binding,
    }


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "selected output ceiling reached")
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
    parser.add_argument("--binding", required=True, type=Path)
    parser.add_argument("--module", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--operation-limit", type=int, default=20_000_000)
    parser.add_argument("--seconds-limit", type=float, default=180.0)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(1 <= args.operation_limit <= 40_000_000,
            "operation limit outside selected ceiling")
    require(1.0 <= args.seconds_limit <= 300.0,
            "time limit outside selected ceiling")
    budget = Budget(operation_limit=args.operation_limit,
                    seconds_limit=args.seconds_limit)
    result = prepare(read_json(args.binding), read_json(args.module), budget)
    payload = (json.dumps(result, separators=(",", ":")) + "\n").encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; row {result['source_row']}; "
          f"top order {result['top_order']}; operations {budget.operations}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
