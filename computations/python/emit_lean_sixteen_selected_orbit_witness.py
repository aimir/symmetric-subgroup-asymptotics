#!/usr/bin/env python3
"""Emit one exact-top, sixteen-point cyclic orbit witness.

Explicit family and row selection plus either one generator index or a word
of at most sixteen generator indices is mandatory. The only computation is
composition and cycle traversal of those displayed sixteen-point permutations.
No group, vector, submodule, or catalogue enumeration is performed. Lean must
check the emitted point equalities; the provenance receipt is not a proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


FAMILIES = {
    "zero16": ("ZeroSixteen", 29),
    "twoAffine16": ("TwoAffineSixteen", 15),
    "primitive16": ("PrimitiveSixteen", 20),
}
PREFIX = "Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer."
INPUT_LIMIT = 2 * 1024 * 1024
WORD_LIMIT = 16
MODULE_NAME = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    """The selected source does not have the supported literal interface."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def selected_permutation(source: str, row: int, index: int) -> tuple[int, ...]:
    """Parse only the named row tuple and its one selected private definition."""
    tuple_name = f"row{row}Generators"
    tuple_match = re.search(
        rf"^def {tuple_name} : Fin (\d+) → Equiv\.Perm \(Fin 16\) :=\s*"
        rf"!\[([^\]]+)\]",
        source, re.MULTILINE,
    )
    require(tuple_match is not None,
            f"{tuple_name}: no supported literal tuple (reused interfaces need a separate binding)")
    assert tuple_match is not None
    names = [name.strip() for name in tuple_match.group(2).split(",")]
    require(len(names) == int(tuple_match.group(1)), "generator tuple length mismatch")
    require(0 <= index < len(names), f"generator-index must be in 0..{len(names) - 1}")
    require(all(re.fullmatch(rf"row{row}Generator\d+", name) for name in names),
            "generator tuple contains an unsupported nonliteral entry")

    top_pattern = (
        rf"^abbrev Row{row}Top : Subgroup \(Equiv\.Perm \(Fin 16\)\) :=\s*"
        rf"Subgroup\.closure \(Set\.range {tuple_name}\)\s*$"
    )
    interface_pattern = (
        rf"^noncomputable def row{row} : DegreeTwoPairTopFiniteInterface 16 :=\s*"
        rf"DegreeTwoPairTopFiniteInterface\.withCanonicalRegistries\s+Row{row}Top\s*$"
    )
    require(re.search(top_pattern, source, re.MULTILINE) is not None,
            "selected top is not the literal closure of the selected tuple")
    require(re.search(interface_pattern, source, re.MULTILINE) is not None,
            "selected interface does not definitionally use that literal top")

    selected_name = re.escape(names[index])
    definition = re.search(
        rf"^private def {selected_name} : Equiv\.Perm \(Fin 16\) where\n"
        rf"(?P<body>.*?)(?=^\S|\Z)",
        source, re.MULTILINE | re.DOTALL,
    )
    require(definition is not None, "selected private permutation definition is absent")
    assert definition is not None
    images = re.search(
        r"^  toFun x := \(#\[([0-9, ]+)\] : Array \(Fin 16\)\)\[x\.val\]!$",
        definition.group("body"), re.MULTILINE,
    )
    require(images is not None, "selected permutation images are not a literal sixteen-point array")
    assert images is not None
    permutation = tuple(int(entry.strip()) for entry in images.group(1).split(","))
    require(sorted(permutation) == list(range(16)), "selected images are not a permutation of Fin16")
    return permutation


def point_assignments(permutation: tuple[int, ...]) -> dict[str, list]:
    """Traverse at most sixteen points, with no group closure computation."""
    cycles: list[list[int]] = []
    orbit_index = [-1] * 16
    exponent = [-1] * 16
    for point in range(16):
        if orbit_index[point] != -1:
            continue
        cycle: list[int] = []
        current = point
        while orbit_index[current] == -1:
            orbit_index[current] = len(cycles)
            exponent[current] = len(cycle)
            cycle.append(current)
            current = permutation[current]
        require(current == point, "cycle traversal did not return to its selected representative")
        cycles.append(cycle)
    require(len(cycles) <= 4,
            f"selected permutation has {len(cycles)} cycles; at most four are permitted")
    representatives = [cycle[0] for cycle in cycles]
    representatives += [representatives[0]] * (4 - len(representatives))
    return {
        "cycles": cycles,
        "representatives": representatives,
        "orbit_index": orbit_index,
        "exponent": exponent,
    }


def lean_tuple(values: list[int]) -> str:
    return "![" + ", ".join(map(str, values)) + "]"


def render(module: str, interface_module: str, interface_namespace: str,
           row: int, index: int, source_relative: str, source_sha256: str,
           assignment: dict[str, list], *,
           generator_word: tuple[int, ...] | None = None) -> str:
    interface = f"{PREFIX}{interface_namespace}.row{row}"
    generators = f"{PREFIX}{interface_namespace}.row{row}Generators"
    if generator_word is None:
        selection = f"row {row}, generator index {index} (zero based)"
        element_definition = (
            f"def element : {interface}.top :=\n"
            f"  ⟨{generators} {index}, Subgroup.subset_closure ⟨{index}, rfl⟩⟩"
        )
    else:
        require(1 <= len(generator_word) <= WORD_LIMIT,
                f"generator-word must contain between one and {WORD_LIMIT} indices")
        selection = f"row {row}, generator word {list(generator_word)} (zero based)"
        factors = [
            f"def generatorFactor{position} : {interface}.top :=\n"
            f"  ⟨{generators} {factor}, Subgroup.subset_closure ⟨{factor}, rfl⟩⟩"
            for position, factor in enumerate(generator_word)
        ]
        product = " * ".join(f"generatorFactor{position}"
                             for position in range(len(generator_word)))
        element_definition = "\n\n".join(factors + [
            f"def element : {interface}.top :=\n  {product}"
        ])
    return f"""import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.{interface_module}

/-!
# Selected literal sixteen-point orbit witness

Source: `{source_relative}`
Source SHA-256: `{source_sha256}`
Selection: {selection}.
Only the sixteen displayed point equalities are decided below.
The output still requires a bounded Lean check. Quotient-socle bounds are separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace {module}

{element_definition}

def representatives : Fin 4 → Fin 16 :=
  {lean_tuple(assignment['representatives'])}

def orbitIndex : Fin 16 → Fin 4 :=
  {lean_tuple(assignment['orbit_index'])}

def exponent : Fin 16 → Fin 16 :=
  {lean_tuple(assignment['exponent'])}

def witness : LiteralCyclicOrbitWitness {interface}.top 4 where
  element := element
  representative := representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) {interface}.top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

end {module}
end SymmetricSubgroupAsymptotics

end
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", required=True, choices=FAMILIES)
    parser.add_argument("--row", required=True, type=int, help="one-based literal row number")
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--generator-index", type=int,
                           help="zero-based position in that row's displayed generator tuple")
    selection.add_argument("--generator-word", type=int, nargs="+",
                           help="one to sixteen zero-based indices, in Lean product order")
    parser.add_argument("--output", required=True, type=Path, help="new Lean module path")
    parser.add_argument("--receipt", required=True, type=Path,
                        help="new provenance JSON path outside the publication repository")
    args = parser.parse_args()
    try:
        repo = Path(__file__).resolve().parents[2]
        family_stem, row_count = FAMILIES[args.family]
        require(1 <= args.row <= row_count, f"row must be in 1..{row_count}")
        interface_module = f"PrimitiveAffineDegreeTwo{family_stem}Interfaces"
        interface_namespace = f"DegreeTwo{family_stem}Interfaces"
        source_relative = f"formal/SymmetricSubgroupAsymptotics/{interface_module}.lean"
        source_path = repo / source_relative
        require(source_path.stat().st_size <= INPUT_LIMIT, "interface source exceeds the input limit")
        source_bytes = source_path.read_bytes()
        source_sha256 = hashlib.sha256(source_bytes).hexdigest()
        source = source_bytes.decode("utf-8")
        if args.generator_word is None:
            word = (args.generator_index,)
        else:
            word = tuple(args.generator_word)
        require(1 <= len(word) <= WORD_LIMIT,
                f"generator-word must contain between one and {WORD_LIMIT} indices")
        # Lean permutations multiply by composition: (g * h)(x) = g(h(x)).
        # This evaluates only the explicitly requested factors on sixteen points.
        permutation = tuple(range(16))
        for index in word:
            factor = selected_permutation(source, args.row, index)
            permutation = tuple(permutation[factor[point]] for point in range(16))
        assignment = point_assignments(permutation)
        output = args.output.resolve()
        receipt = args.receipt.resolve()
        require(output.suffix == ".lean" and MODULE_NAME.fullmatch(output.stem) is not None,
                "output must be a .lean file with a simple capitalized module name")
        require(output.parent == repo / "formal/SymmetricSubgroupAsymptotics",
                "output must be in this checkout's formal/SymmetricSubgroupAsymptotics directory")
        require(not receipt.is_relative_to(repo), "provenance receipts must stay outside the repository")
        require(not output.exists() and not receipt.exists(), "refusing to overwrite an existing file")
        lean = render(output.stem, interface_module, interface_namespace, args.row,
                      word[0], source_relative, source_sha256, assignment,
                      generator_word=None if args.generator_word is None else word)
        provenance = {
            "schema": "literal-sixteen-cyclic-orbit-witness-v1",
            "family": args.family,
            "row_one_based": args.row,
            "generator_index_zero_based": args.generator_index,
            "generator_word_zero_based": list(word),
            "source": source_relative,
            "source_sha256": source_sha256,
            "permutation": list(permutation),
            **assignment,
            "output": str(output),
            "output_sha256": hashlib.sha256(lean.encode("utf-8")).hexdigest(),
            "lean_checked": False,
            "note": "Generation provenance only; the emitted point equalities require Lean verification.",
        }
        receipt.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as stream:
            stream.write(lean)
        with receipt.open("x", encoding="utf-8") as stream:
            json.dump(provenance, stream, indent=2)
            stream.write("\n")
        print(json.dumps({"output": str(output), "receipt": str(receipt),
                          "cycle_lengths": [len(cycle) for cycle in assignment["cycles"]]}))
    except (Refused, OSError, UnicodeError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
