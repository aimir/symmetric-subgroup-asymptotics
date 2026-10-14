#!/usr/bin/env python3
"""Emit one quotient-socle adapter from an existing sixteen-point normal registry.

Family, row, degree-four owner, output, and external receipt are mandatory.
Only the selected literal generator arrays and the small existing normal-state
transition table are interpreted. No group, socle, vector, or submodule is
enumerated. The result uses the existing normal-word proofs; generation and
its receipt do not establish a Lean theorem. Do not run a catalogue batch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


FAMILIES = {"zero16": "ZeroSixteen", "primitive16": "PrimitiveSixteen"}
PRIMITIVE_OWNERS = {3: 30, 4: 31, 6: 33, 7: 34, 9: 36, 12: 37, 14: 38}
PREFIX = "Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer."
SOURCE_LIMIT = 2 * 1024 * 1024
LINE_LIMIT = 256 * 1024
STATES_LIMIT = 64
CLASSES_LIMIT = 64
MODULE_NAME = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    """The selected source is not one of the supported literal forms."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def bounded_lines(path: Path):
    """Stream source text with small limits; never decode a group table."""
    total = 0
    with path.open(encoding="utf-8") as stream:
        while True:
            line = stream.readline(LINE_LIMIT + 1)
            if not line:
                return
            total += len(line.encode("utf-8"))
            require(len(line) <= LINE_LIMIT, f"{path}: source line exceeds the limit")
            require(total <= SOURCE_LIMIT, f"{path}: selected-source scan exceeds the limit")
            yield line


def declaration(path: Path, signature: str) -> str:
    """Read one declaration, retaining no preceding declarations."""
    selected: list[str] = []
    for line in bounded_lines(path):
        if not selected:
            if re.match(signature, line):
                selected.append(line)
        elif line.strip() and not line[0].isspace():
            break
        else:
            selected.append(line)
    require(bool(selected), f"{path}: selected declaration is absent")
    return "".join(selected).rstrip() + "\n"


def top_header(path: Path) -> str:
    """Stop immediately after generators, before any encoded Cayley data."""
    lines: list[str] = []
    found = False
    for line in bounded_lines(path):
        if found and line.strip() and not line[0].isspace():
            break
        lines.append(line)
        found = found or bool(re.match(r"^def generators\b", line))
        if found and not line.strip():
            break
    require(found, f"{path}: no public generators declaration before the scan limit")
    return "".join(lines)


def permutation(source: str, name: str) -> tuple[int, ...]:
    block = re.search(
        rf"^private def {re.escape(name)} : Equiv\.Perm \(Fin 16\) where\n"
        r"(?P<body>.*?)(?=^\S|\Z)", source, re.MULTILINE | re.DOTALL,
    )
    require(block is not None, f"{name}: expected a private literal Fin16 permutation")
    assert block is not None
    arrays = []
    for field in ("toFun", "invFun"):
        match = re.search(
            rf"^  {field} x := \(#\[([0-9, ]+)\] : Array \(Fin 16\)\)\[x\.val\]!$",
            block.group("body"), re.MULTILINE,
        )
        require(match is not None, f"{name}.{field}: expected a literal array")
        assert match is not None
        values = tuple(int(x.strip()) for x in match.group(1).split(","))
        require(sorted(values) == list(range(16)), f"{name}.{field}: not a Fin16 permutation")
        arrays.append(values)
    forward, inverse = arrays
    require(all(inverse[forward[i]] == i for i in range(16)), f"{name}: inverse array mismatch")
    return forward


class Tokens:
    """A closed parser for small literal expressions, never Python/Lean eval."""

    def __init__(self, source: str):
        self.items = re.findall(r"Fin\.cases|Fin\.elim0|j\.val|generator\d+|=>|[A-Za-z_]+|\d+|[()]|<|\S", source)
        self.position = 0

    def take(self, expected: str | None = None) -> str:
        require(self.position < len(self.items), "unexpected end of literal expression")
        value = self.items[self.position]
        self.position += 1
        require(expected is None or value == expected, f"expected {expected!r}, found {value!r}")
        return value

    def finish(self) -> None:
        require(self.position == len(self.items), "trailing unsupported expression syntax")


def generator_tree(tokens: Tokens):
    token = tokens.take()
    if token == "(":
        result = generator_tree(tokens)
        tokens.take(")")
        return result
    if token == "if":
        tokens.take("j.val")
        tokens.take("<")
        cutoff = tokens.take()
        require(cutoff.isdecimal(), "generator cutoff is not a natural literal")
        tokens.take("then")
        left = generator_tree(tokens)
        tokens.take("else")
        right = generator_tree(tokens)
        return int(cutoff), left, right
    require(re.fullmatch(r"generator\d+", token) is not None,
            "unsupported leaf in generator selector")
    return token


def choose_generator(tree, index: int) -> str:
    if isinstance(tree, str):
        return tree
    cutoff, left, right = tree
    return choose_generator(left if index < cutoff else right, index)


def top_generators(header: str) -> list[tuple[int, ...]]:
    match = re.search(
        r"^def generators \(j : Fin (\d+)\) : Equiv\.Perm \(Fin 16\) :=\s*([^\n]+)",
        header, re.MULTILINE,
    )
    require(match is not None, "degree-four generators selector has an unsupported form")
    assert match is not None
    width = int(match.group(1))
    require(1 <= width <= 16, "generator width is outside the selected bound")
    tokens = Tokens(match.group(2))
    tree = generator_tree(tokens)
    tokens.finish()
    return [permutation(header, choose_generator(tree, j)) for j in range(width)]


def interface_generators(path: Path, row: int) -> tuple[list[tuple[int, ...]], dict[str, str]]:
    tuple_block = declaration(path, rf"^def row{row}Generators\b")
    match = re.fullmatch(
        rf"def row{row}Generators : Fin (\d+) → Equiv\.Perm \(Fin 16\) :=\s*!\[([^\]]+)\]\s*",
        tuple_block,
    )
    require(match is not None, "degree-two generator tuple has an unsupported form")
    assert match is not None
    width = int(match.group(1))
    names = [name.strip() for name in match.group(2).split(",")]
    require(1 <= width <= 16 and len(names) == width, "degree-two generator width mismatch")
    require(all(re.fullmatch(rf"row{row}Generator\d+", n) for n in names),
            "degree-two tuple contains a nonliteral entry")
    fragments = {f"row{row}Generators": tuple_block}
    values = []
    for name in names:
        block = declaration(path, rf"^private def {re.escape(name)}\b")
        fragments[name] = block
        values.append(permutation(block, name))
    top = declaration(path, rf"^abbrev Row{row}Top\b")
    interface = declaration(path, rf"^noncomputable def row{row}\b")
    require(" ".join(top.split()) ==
            f"abbrev Row{row}Top : Subgroup (Equiv.Perm (Fin 16)) := "
            f"Subgroup.closure (Set.range row{row}Generators)",
            "degree-two top is not the selected tuple's literal closure")
    require(" ".join(interface.split()) ==
            f"noncomputable def row{row} : DegreeTwoPairTopFiniteInterface 16 := "
            f"DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Row{row}Top",
            "degree-two interface does not use that literal top")
    fragments[f"Row{row}Top"] = top
    fragments[f"row{row}"] = interface
    return values, fragments


def zero_row_one_binding(path: Path) -> str:
    block = declaration(path, r"^noncomputable def row1\b")
    top = "PrimitiveAffineSixteenFrameRow1TopCertificate"
    normal = "PrimitiveAffineSixteenFrameRow1NormalCertificate"
    expected = f"""noncomputable def row1 : DegreeTwoPairTopFiniteInterface 16 := by
  letI : Group {top}.Source := {top}.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    {normal}.topConjugacy.toCardinalCover {normal}.topAmbient
    {normal}.stateGenerators {normal}.data
    (Subgroup.closure (Set.range {top}.generators)) {top}.originalEquiv"""
    require(" ".join(block.split()) == " ".join(expected.split()),
            "zero16-1 no longer has its audited direct originalEquiv binding")
    return block


def cases_tree(tokens: Tokens):
    token = tokens.take()
    if token == "(":
        result = cases_tree(tokens)
        tokens.take(")")
        return result
    if token == "Fin.cases":
        head = cases_tree(tokens)
        tail = cases_tree(tokens)
        return head, tail
    if token == "fun":
        variable = tokens.take()
        require(re.fullmatch(r"[A-Za-z_]+", variable) is not None, "unsupported empty-case binder")
        tokens.take("=>")
        tokens.take("Fin.elim0")
        tokens.take(variable)
        return None
    require(token.isdecimal(), "unsupported normal-state table term")
    return int(token)


def cases_list(tree) -> list:
    result = []
    while tree is not None:
        require(isinstance(tree, tuple) and len(tree) == 2, "malformed Fin.cases spine")
        head, tree = tree
        result.append(head)
        require(len(result) <= max(STATES_LIMIT, CLASSES_LIMIT), "Fin.cases spine exceeds the bound")
    return result


def child_table(block: str) -> list[list[int]]:
    match = re.fullmatch(r"def child : Fin (\d+) → Fin (\d+) → Fin (\d+) :=\s*(.*?)\s*",
                         block, re.DOTALL)
    require(match is not None, "child table has an unsupported signature")
    assert match is not None
    states, classes, target = map(int, match.group(1, 2, 3))
    require(1 <= states <= STATES_LIMIT and states == target, "normal-state count exceeds the bound")
    require(1 <= classes <= CLASSES_LIMIT, "class-index count exceeds the bound")
    tokens = Tokens(match.group(4))
    tree = cases_tree(tokens)
    tokens.finish()
    rows = [cases_list(row) for row in cases_list(tree)]
    require(len(rows) == states and all(len(row) == classes for row in rows),
            "child table dimensions do not match its signature")
    require(all(type(x) is int and 0 <= x < states for row in rows for x in row),
            "child table contains an invalid state index")
    return rows


def two_steps(child: list[list[int]], bottom: int) -> list[tuple[int, int]]:
    require(0 <= bottom < len(child), "bottom is not a valid state index")
    witnesses: dict[int, tuple[int, int]] = {}
    for a in range(len(child[0])):
        for b in range(len(child[0])):
            witnesses.setdefault(child[child[bottom][a]][b], (a, b))
    missing = sorted(set(range(len(child))) - witnesses.keys())
    require(not missing, f"normal states not reached in two transitions: {missing}")
    return [witnesses[i] for i in range(len(child))]


def render(module: str, stem: str, row: int, owner: int, bottom: int,
           child: list[list[int]], witnesses: list[tuple[int, int]]) -> str:
    interface = f"{PREFIX}DegreeTwo{stem}Interfaces.row{row}"
    generators = f"{PREFIX}DegreeTwo{stem}Interfaces.row{row}Generators"
    top = f"PrimitiveAffineSixteenFrameRow{owner}TopCertificate"
    normal = f"PrimitiveAffineSixteenFrameRow{owner}NormalCertificate"
    if stem == "ZeroSixteen" and row == 1:
        binding = f"""/-- The existing interface directly retains this literal top. -/
theorem top_eq :
    Subgroup.closure (Set.range {top}.generators) =
      {interface}.top := by
  rfl
"""
    else:
        binding = f"""/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    {top}.generators = {generators} := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range {top}.generators) =
      {interface}.top := by
  change Subgroup.closure (Set.range {top}.generators) =
    Subgroup.closure (Set.range {generators})
  rw [generators_eq]
"""
    cases = "\n".join(f"  · exact ⟨{a}, {b}, rfl⟩" for a, b in witnesses)
    return f"""import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwo{stem}Interfaces
import SymmetricSubgroupAsymptotics.{normal}

/-!
# Selected literal sixteen-point quotient-socle adapter

Generated by `emit_lean_pair_top_selected_registry_socles.py` for {stem}
row {row}, degree-four owner {owner}. Every normal state is reached by two
existing class-representative transitions. No group, socle, or vector
enumeration is used. This output still requires a bounded Lean check.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace {module}

abbrev Source := {top}.Source
local instance sourceGroup : Group Source := {top}.group

{binding}
noncomputable def originalEquiv : Source ≃* {interface}.top :=
  {top}.originalEquiv.trans (MulEquiv.subgroupCongr top_eq)

private theorem two_steps (i : Fin {len(child)}) :
    ∃ a b : Fin {len(child[0])},
      {normal}.child ({normal}.child {bottom} a) b = i := by
  fin_cases i
{cases}

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact {normal}.data.toRegistry.normal_generating_pair two_steps N

theorem top_normal_generators (N : Subgroup {interface}.top) (hN : N.Normal) :
    ∃ x : Fin 2 → {interface}.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

theorem topSocle (N : {{N : Subgroup {interface}.top // N.Normal}}) :
    SocleNormalGeneratorBound ({interface}.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Keep the original interface's normal-state type and literal subgroups. -/
noncomputable def family :
    {interface}.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    {interface}.normalRegistry topSocle

end {module}
end SymmetricSubgroupAsymptotics

end
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", required=True, choices=FAMILIES)
    parser.add_argument("--row", required=True, type=int, help="one-based degree-two row")
    parser.add_argument("--degree4-owner", required=True, type=int,
                        help="explicit matching degree-four table owner")
    parser.add_argument("--degree4-source-root", type=Path,
                        help="checked main/row checkout to read; default: this checkout")
    parser.add_argument("--output", required=True, type=Path, help="new Lean module path")
    parser.add_argument("--receipt", required=True, type=Path,
                        help="new provenance JSON outside the source/output repositories")
    args = parser.parse_args()
    try:
        repo = Path(__file__).resolve().parents[2]
        source_root = (args.degree4_source_root or repo).resolve()
        stem = FAMILIES[args.family]
        expected = args.row if args.family == "zero16" and 1 <= args.row <= 29 else None
        if args.family == "primitive16":
            expected = PRIMITIVE_OWNERS.get(args.row)
        require(expected is not None and args.degree4_owner == expected,
                "family/row/degree4-owner is not one of the 36 audited exact matches")
        formal = repo / "formal/SymmetricSubgroupAsymptotics"
        source_formal = source_root / "formal/SymmetricSubgroupAsymptotics"
        interface_path = formal / f"PrimitiveAffineDegreeTwo{stem}Interfaces.lean"
        top_path = source_formal / f"PrimitiveAffineSixteenFrameRow{expected}TopCertificate.lean"
        normal_path = source_formal / f"PrimitiveAffineSixteenFrameRow{expected}NormalCertificate.lean"
        core_path = source_formal / f"PrimitiveAffineSixteenFrameRow{expected}NormalCore.lean"
        if expected == 1:
            core_path = normal_path
        output, receipt = args.output.resolve(), args.receipt.resolve()
        require(output.suffix == ".lean" and MODULE_NAME.fullmatch(output.stem) is not None,
                "output needs a simple capitalized Lean module name")
        require(output.parent == formal, "output must be in this checkout's formal module directory")
        require(not receipt.is_relative_to(repo) and not receipt.is_relative_to(source_root),
                "receipt must remain outside both publication checkouts")
        require(not output.exists() and not receipt.exists(), "refusing to overwrite existing files")

        header = top_header(top_path)
        original = top_generators(header)
        fragments = {str(top_path): {"generator_header": digest(header)}}
        if args.family == "zero16" and args.row == 1:
            binding = zero_row_one_binding(interface_path)
            # This interface imports its own literal owner, so cross-root headers must agree.
            local_top = top_header(formal / top_path.name)
            require(top_generators(local_top) == original, "row1 direct binding uses different generators")
            fragments[str(interface_path)] = {"row1": digest(binding)}
            fragments[str(formal / top_path.name)] = {"generator_header": digest(local_top)}
        else:
            selected, selected_fragments = interface_generators(interface_path, args.row)
            require(selected == original, "ordered literal generator arrays do not match")
            fragments[str(interface_path)] = {name: digest(text) for name, text in selected_fragments.items()}

        child_block = declaration(core_path, r"^def child\b")
        child = child_table(child_block)
        data_block = declaration(normal_path, r"^noncomputable def data\b")
        require("FiniteNormalJoinWordRegistryData" in data_block,
                "normal data is not an existing normal-word registry")
        bottoms = re.findall(r"^  bottom := (\d+)\s*$", data_block, re.MULTILINE)
        require(len(bottoms) == 1, "registry bottom is not one explicit index")
        require(re.search(r"^  child := child\s*$", data_block, re.MULTILINE) is not None,
                "registry data does not retain its exported child table")
        if expected != 1:
            alias = declaration(normal_path, r"^abbrev child\b")
            require(" ".join(alias.split()) ==
                    f"abbrev child := PrimitiveAffineSixteenFrameRow{expected}NormalCore.child",
                    "normal certificate does not export the selected core child table")
            fragments.setdefault(str(normal_path), {})["child_alias"] = digest(alias)
        bottom = int(bottoms[0])
        witnesses = two_steps(child, bottom)
        fragments.setdefault(str(core_path), {})["child"] = digest(child_block)
        fragments.setdefault(str(normal_path), {})["data"] = digest(data_block)
        lean = render(output.stem, stem, args.row, expected, bottom, child, witnesses)
        provenance = {
            "schema": "selected-literal-registry-socles-v1",
            "family": args.family, "row_one_based": args.row, "degree4_owner": expected,
            "degree4_source_root": str(source_root),
            "source_fragment_sha256": fragments,
            "generator_arrays_zero_based": [list(p) for p in original],
            "state_count": len(child), "class_count": len(child[0]), "bottom": bottom,
            "child_index_table": child, "two_step_witnesses": witnesses,
            "output": str(output), "output_sha256": digest(lean), "lean_checked": False,
            "note": "Generation provenance only. Fragment hashes are not whole-source or dependency receipts; Lean must check the original imported registry and the emitted adapter.",
        }
        receipt.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as stream:
            stream.write(lean)
        with receipt.open("x", encoding="utf-8") as stream:
            json.dump(provenance, stream, indent=2)
            stream.write("\n")
        print(json.dumps({"output": str(output), "receipt": str(receipt),
                          "states": len(child), "classes": len(child[0]), "lean_checked": False}))
    except (Refused, OSError, UnicodeError, RecursionError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
