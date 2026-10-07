#!/usr/bin/env python3
"""Render a checked generator certificate for one selected point stabilizer.

The prepared eight-frame certificate already contains the literal top Cayley
rows and the two (or more) stored point-stabilizer generators.  This selected
renderer enumerates only that stabilizer, records one short positive word for
each of its elements, and emits Lean code that rechecks all equations in the
literal top group.  It has no directory scan or bulk mode.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import tempfile


SCHEMA = "frames8-selected-top-certificate-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 2 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def permutation(value: object, width: int) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid permutation width")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def product(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """Lean's permutation product on decoded function rows."""
    return tuple(left[right[i]] for i in range(len(left)))


def positive_word(letters: list[int]) -> str:
    word = "FiniteGeneratorWord.one"
    for letter in letters:
        word = (f"FiniteGeneratorWord.mul ({word}) "
                f"(FiniteGeneratorWord.generator {letter})")
    return word


def balanced(values: list[str], variable: str = "j.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{balanced(values[:middle], variable, start)} else "
            f"{balanced(values[middle:], variable, start + middle)})")


def read(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared schema")
    return value


def prepare(value: dict) -> dict:
    rows = [permutation(x, 8) for x in value["cayley"]["rows"]]
    position = {row: i for i, row in enumerate(rows)}
    require(len(position) == len(rows) == value["top_order"],
            "invalid literal top Cayley rows")
    binding = value["binding"]
    generators = [permutation(x, 8)
                  for x in binding["stabilizer_generators"]]
    require(generators and all(g in position for g in generators),
            "stabilizer generator escaped the top")

    identity = tuple(range(8))
    elements = [identity]
    parents = [0]
    letters = [0]
    seen = {identity: 0}
    cursor = 0
    while cursor < len(elements):
        for letter, generator in enumerate(generators):
            child = product(elements[cursor], generator)
            if child not in seen:
                require(len(elements) < value["top_order"],
                        "stabilizer enumeration reached the top order")
                seen[child] = len(elements)
                elements.append(child)
                parents.append(cursor)
                letters.append(letter)
        cursor += 1

    literal = sorted((row for row in rows if row[0] == 0),
                     key=position.__getitem__)
    require(set(elements) == set(literal),
            "stored generators do not enumerate the literal stabilizer")

    word_for: dict[tuple[int, ...], list[int]] = {}
    for row, index in seen.items():
        word: list[int] = []
        while index:
            word.append(letters[index])
            index = parents[index]
        word_for[row] = list(reversed(word))

    return {
        "row": value["source_row"],
        "top_order": value["top_order"],
        "generator_indices": [position[g] for g in generators],
        "element_indices": [position[x] for x in literal],
        "words": [word_for[x] for x in literal],
    }


def emit(module: str, induced_module: str, data: dict, input_name: str) -> str:
    n = len(data["element_indices"])
    g = len(data["generator_indices"])
    indices = balanced([str(x) for x in data["element_indices"]])
    generators = balanced([
        f"⟨⟨{x}⟩, by native_decide +revert⟩"
        for x in data["generator_indices"]])
    words = balanced([positive_word(x) for x in data["words"]])
    return f"""import SymmetricSubgroupAsymptotics.{induced_module}
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

/-!
# Selected eight-frame row {data['row']}: point-stabilizer generators

Generated by `emit_lean_frames8_selected_stabilizer_generators.py` from the
explicit selected input `{input_name}`.  Lean rechecks one short word for
each of the {n} literal point-stabilizer elements.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.{module}

open {induced_module}

local instance sourceGroup : Group Source :=
  {induced_module.replace('InducedBinding', 'TopCertificate')}.group

local instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable ({induced_module}.inStabilizer x.index)
  unfold {induced_module}.inStabilizer
  infer_instance

def generators (j : Fin {g}) : sourceStabilizer :=
  {generators}

private def elementIndex (j : Fin {n}) : Fin {data['top_order']} :=
  {indices}

def elements (j : Fin {n}) : sourceStabilizer :=
  ⟨⟨elementIndex j⟩, by native_decide +revert⟩

theorem elements_surjective : Function.Surjective elements := by
  native_decide +revert

private def elementWords (j : Fin {n}) :
    FiniteGeneratorWord (Fin {g}) :=
  {words}

private theorem elementWords_checked : ∀ j : Fin {n},
    (elementWords j).eval generators = elements j := by
  native_decide +revert

private def wordCertificate :
    FiniteGeneratorWordCertificate elements generators where
  words := elementWords
  equations := elementWords_checked

theorem generators_full :
    Subgroup.closure (Set.range generators) = ⊤ := by
  apply top_unique
  have htop : Subgroup.closure (Set.range elements) = ⊤ := by
    rw [Set.range_eq_univ.mpr elements_surjective]
    exact Subgroup.closure_univ
  rw [← htop]
  exact wordCertificate.closure_le

end SymmetricSubgroupAsymptotics.{module}

end
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--induced-module", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None,
            "invalid output module name")
    require(MODULE_RE.fullmatch(args.induced_module) is not None,
            "invalid induced module name")
    data = prepare(read(args.input))
    payload = emit(args.module, args.induced_module, data,
                   args.input.name).encode()
    require(len(payload) <= OUTPUT_LIMIT, "Lean output ceiling reached")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=args.output.name + ".",
                                dir=args.output.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(name, args.output)
    finally:
        if os.path.exists(name):
            os.unlink(name)
    print(f"{args.output}: row {data['row']}; "
          f"{len(data['element_indices'])} stabilizer elements")


if __name__ == "__main__":
    main()
