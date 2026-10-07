#!/usr/bin/env python3
"""Render the relative-binary-head registry of one selected frame row.

The prepared certificate retains an exact radical word for every generator
of every normal state's relative radical.  This bounded renderer turns those
words into Lean certificates and derives each head rank from checked subgroup
orders.  It scans no directory and invokes no subprocess.
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
OUTPUT_LIMIT = 4 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def lookup(values: list[str], variable: str = "j.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{lookup(values[:middle], variable, start)} else "
            f"{lookup(values[middle:], variable, start + middle)})")


def disjunction(values: list[int], variable: str) -> str:
    require(values, "empty membership list")
    if len(values) == 1:
        return f"{variable} = {values[0]}"
    middle = len(values) // 2
    return (f"({disjunction(values[:middle], variable)} ∨ "
            f"{disjunction(values[middle:], variable)})")


def boolean_disjunction(values: list[int], variable: str) -> str:
    """A compiler-executable balanced membership test.

    Large proposition-valued disjunctions inside a `noncomputable section`
    can cause Lean to select `Classical.propDecidable`; `native_decide` then
    cannot compile later subgroup checks.  Retaining the same literal list as
    a Boolean test makes the decision procedure explicit and executable.
    """
    require(values, "empty membership list")
    if len(values) == 1:
        return f"{variable} == {values[0]}"
    middle = len(values) // 2
    return (f"({boolean_disjunction(values[:middle], variable)} || "
            f"{boolean_disjunction(values[middle:], variable)})")


def positive_word(letters: list[int]) -> str:
    word = ".one"
    for letter in letters:
        word = f".mul ({word}) (.generator {letter})"
    return word


def finite_word(node: dict) -> str:
    require(isinstance(node, dict), "invalid finite word")
    tag = node.get("tag")
    if tag == "one":
        return ".one"
    if tag == "generator":
        return f".generator {node['index']}"
    if tag == "mul":
        return f".mul ({finite_word(node['left'])}) ({finite_word(node['right'])})"
    if tag == "inv":
        return f".inv ({finite_word(node['word'])})"
    raise Refused("unknown finite-word node")


def radical_word(node: list, names: list[str]) -> str:
    require(isinstance(node, list) and node, "invalid radical word")
    tag = node[0]
    if tag == "one" and len(node) == 1:
        return ".one"
    if tag == "power" and len(node) == 2:
        return f".power {node[1]}"
    if tag == "mixed" and len(node) == 3:
        return f".mixed {node[1]} {node[2]}"
    if tag == "mul" and len(node) == 3:
        return f".mul {names[node[1]]} {names[node[2]]}"
    if tag == "inv" and len(node) == 2:
        return f".inv {names[node[1]]}"
    if tag == "conj" and len(node) == 3:
        return f".conj {node[1]} {names[node[2]]}"
    if tag == "conjInv" and len(node) == 3:
        return f".conjInv {node[1]} {names[node[2]]}"
    raise Refused("unknown radical-word node")


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(), "missing prepared input")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared schema")
    generators = value.get("generators")
    normal_generators = value.get("normal_generators")
    normal_orders = value.get("normal_orders")
    radicals = value.get("radicals")
    cayley = value.get("cayley")
    state_count = len(normal_generators) if isinstance(normal_generators, list) else 0
    generator_count = len(generators) if isinstance(generators, list) else 0
    width = value.get("normal_generator_width")
    require(1 <= state_count <= 256 and 1 <= generator_count <= 16 and
            type(width) is int and 1 <= width <= 16 and
            isinstance(normal_orders, list) and len(normal_orders) == state_count and
            isinstance(radicals, list) and len(radicals) == state_count and
            all(isinstance(row, list) and len(row) == width
                for row in normal_generators), "invalid normal/radical registry")
    for i, row in enumerate(radicals):
        require(isinstance(row, dict) and
                type(row.get("target")) is int and 0 <= row["target"] < state_count and
                row.get("head_rank") in (0, 1, 2) and
                isinstance(row.get("nodes"), list) and row["nodes"] and
                isinstance(row.get("target_generator_nodes"), list) and
                  len(row["target_generator_nodes"]) == width and
                isinstance(row.get("power_words"), list) and
                  len(row["power_words"]) == width and
                isinstance(row.get("mixed_words"), list) and
                  len(row["mixed_words"]) == width and
                  all(len(x) == generator_count for x in row["mixed_words"]),
                f"invalid radical row {i}")
        require(normal_orders[i] ==
                (2 ** row["head_rank"]) * normal_orders[row["target"]],
                "radical head/order mismatch")
        names = [f"word{k}" for k in range(len(row["nodes"]))]
        for k, node in enumerate(row["nodes"]):
            radical_word(node, names[:k])
        require(all(type(k) is int and 0 <= k < len(names)
                    for k in row["target_generator_nodes"]),
                "invalid radical generator node")
        for word in row["power_words"]:
            finite_word(word)
        for words in row["mixed_words"]:
            for word in words:
                finite_word(word)
    require(isinstance(cayley, dict) and
            isinstance(cayley.get("rows"), list) and
            isinstance(cayley.get("words"), list) and
            isinstance(cayley.get("next"), list) and
            type(cayley.get("identity")) is int,
            "invalid Cayley data")
    rows = cayley["rows"]
    require(len(rows) == len(cayley["words"]) == len(cayley["next"]),
            "inconsistent Cayley data")
    row_index = {tuple(row): i for i, row in enumerate(rows)}
    require(len(row_index) == len(rows), "duplicate Cayley row")
    normal_indices = []
    normal_elements = []
    normal_words = []
    for state, generators_row in enumerate(normal_generators):
        try:
            indices = [row_index[tuple(row)] for row in generators_row]
        except KeyError as error:
            raise Refused(f"normal generator outside Cayley rows: {state}") from error

        def row_mul(left: int, right: int) -> int:
            result = left
            for letter in cayley["words"][right]:
                result = cayley["next"][result][letter]
            return result

        identity = cayley["identity"]
        word_for = {identity: []}
        queue = [identity]
        for current in queue:
            for letter, generator in enumerate(indices):
                child = row_mul(current, generator)
                if child not in word_for:
                    word_for[child] = word_for[current] + [letter]
                    queue.append(child)
        elements = sorted(word_for)
        require(len(elements) == normal_orders[state],
                f"normal subgroup order mismatch: {state}")
        normal_indices.append(indices)
        normal_elements.append(elements)
        normal_words.append([word_for.get(i, []) for i in range(len(rows))])
    return {
        "source_row": value["source_row"],
        "state_count": state_count,
        "generator_count": generator_count,
        "width": width,
        "normal_orders": normal_orders,
        "normal_elements": normal_elements,
        "normal_words": normal_words,
        "radicals": radicals,
    }


def emit(module_name: str, normal_module: str, data: dict,
         input_name: str) -> str:
    n = data["state_count"]
    g = data["generator_count"]
    width = data["width"]
    text = f"""import SymmetricSubgroupAsymptotics.{normal_module}
import SymmetricSubgroupAsymptotics.FiniteTopRelativeBinaryRankWordRegistry
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalWords

/-!
# Selected eight-frame row {data['source_row']}: relative binary heads

Generated by `emit_lean_frames8_selected_top_registry.py` from
`{input_name}`.  Every displayed radical is reconstructed from literal
power and ambient-commutator words; subgroup orders and head ranks are
checked in Lean.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.{module_name}

abbrev Source := {normal_module}.Source
local instance sourceGroup : Group Source :=
  {normal_module}.sourceGroup

"""
    # The generated normal module deliberately keeps its group instance local,
    # so referring to it by name may fail if Lean privatizes it.  Use the top
    # module's public group value through the normal module's source alias.
    text = text.replace(
        f"  {normal_module}.sourceGroup\n",
        f"  {normal_module.rsplit('NormalCertificate', 1)[0]}TopCertificate.group\n")
    for i in range(n):
        member = boolean_disjunction(
            data["normal_elements"][i], "x.index.val")
        words = [positive_word(word) for word in data["normal_words"][i]]
        text += f"""private abbrev N{i} : Subgroup Source :=
  Subgroup.closure (Set.range ({normal_module}.stateGenerators {i}))

private def explicitN{i}MembershipTest (x : Source) : Bool :=
  {member}

private def inExplicitN{i} (x : Source) : Prop :=
  explicitN{i}MembershipTest x = true

local instance inExplicitN{i}Decidable (x : Source) :
    Decidable (inExplicitN{i} x) := by
  unfold inExplicitN{i}
  infer_instance

private def explicitN{i} : Subgroup Source where
  carrier := {{x | inExplicitN{i} x}}
  one_mem' := by native_decide +revert
  mul_mem' := by native_decide +revert
  inv_mem' := by native_decide +revert

local instance explicitN{i}Membership (x : Source) :
    Decidable (x ∈ explicitN{i}) := inExplicitN{i}Decidable x

private def explicitN{i}Word (x : Source) :
    FiniteGeneratorWord (Fin {width}) :=
  {lookup(words, 'x.index.val')}

private theorem explicitN{i}Word_eq : ∀ x : Source,
    inExplicitN{i} x →
      (explicitN{i}Word x).eval ({normal_module}.stateGenerators {i}) = x := by
  native_decide +revert

private theorem n{i}_eq_explicit : N{i} = explicitN{i} := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change inExplicitN{i} ({normal_module}.stateGenerators {i} j)
    fin_cases j <;> native_decide
  · intro x hx
    change inExplicitN{i} x at hx
    rw [← explicitN{i}Word_eq x hx]
    exact (explicitN{i}Word x).eval_mem_closure
      ({normal_module}.stateGenerators {i})

local instance n{i}Normal : N{i}.Normal :=
  ({normal_module}.data.normality {i}).normal
    {normal_module}.data.ambient_full

private theorem n{i}Card : Nat.card N{i} = {data['normal_orders'][i]} := by
  rw [n{i}_eq_explicit, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  native_decide +revert

"""
    for i, row in enumerate(data["radicals"]):
        target = row["target"]
        names = [f"word{k}" for k in range(len(row["nodes"]))]
        text += f"namespace R{i}\n\n"
        for k, node in enumerate(row["nodes"]):
            text += (f"private def word{k} : "
                     f"PrimeRelativeRadicalWord (Fin {g}) (Fin {width}) :=\n"
                     f"  {radical_word(node, names[:k])}\n\n")
        target_words = [names[k] for k in row["target_generator_nodes"]]
        text += f"""private def radicalWords (j : Fin {width}) :
    PrimeRelativeRadicalWord (Fin {g}) (Fin {width}) :=
  {lookup(target_words)}

private theorem radicalWords_checked : ∀ j : Fin {width},
    (radicalWords j).eval 2 {normal_module}.topAmbient
        ({normal_module}.stateGenerators {i}) =
      {normal_module}.stateGenerators {target} j := by
  intro j
  fin_cases j <;> native_decide

"""
        power_exprs = [finite_word(x) for x in row["power_words"]]
        mixed_exprs = [finite_word(x)
                       for words in row["mixed_words"] for x in words]
        text += f"""private def powerWord (j : Fin {width}) :
    FiniteGeneratorWord (Fin {width}) :=
  {lookup(power_exprs)}

private def mixedWord (j : Fin {width}) (k : Fin {g}) :
    FiniteGeneratorWord (Fin {width}) :=
  {lookup(mixed_exprs, f'j.val * {g} + k.val')}

private theorem power_checked : ∀ j : Fin {width},
    ({normal_module}.stateGenerators {i} j) ^ 2 =
      (powerWord j).eval ({normal_module}.stateGenerators {target}) := by
  intro j
  fin_cases j <;> native_decide

private theorem mixed_checked : ∀ (j : Fin {width}) (k : Fin {g}),
    ⁅{normal_module}.stateGenerators {i} j,
        {normal_module}.topAmbient k⁆ =
      (mixedWord j k).eval ({normal_module}.stateGenerators {target}) := by
  intro j k
  fin_cases j <;> fin_cases k <;> native_decide

theorem radical_eq : primeRelativeRadical 2 N{i} = N{target} := by
  apply primeRelativeRadical_eq_of_generator_words 2 N{i} N{target}
    {normal_module}.topAmbient {normal_module}.topAmbient_full
    ({normal_module}.stateGenerators {i}) rfl
    ({normal_module}.stateGenerators {target}) rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact (powerWord j).eval_mem_closure
      ({normal_module}.stateGenerators {target})
  · intro j k
    rw [mixed_checked]
    exact (mixedWord j k).eval_mem_closure
      ({normal_module}.stateGenerators {target})

theorem head_eq :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N{i}) =
      {row['head_rank']} := by
  apply primeRelativeHead_eq_of_radical_card 2 N{i} N{target}
    {row['head_rank']} radical_eq
  simp only [n{i}Card, n{target}Card]
  norm_num

end R{i}

"""
    cases = "\n".join(
        (f"    · change Module.finrank (ZMod 2) "
         f"(primeRelativeCharacters 2 N{i}) ≤ 2\n"
         f"      rw [R{i}.head_eq]\n      omega") for i in range(n))
    text += f"""/-- Complete normal-axis registry with relative binary head at most two. -/
noncomputable def registry : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) {normal_module}.topConjugacy.toCardinalCover
      {normal_module}.topAmbient {normal_module}.stateGenerators where
  indexFinite := inferInstance
  data := {normal_module}.data
  head_le i := by
    fin_cases i
{cases}

end SymmetricSubgroupAsymptotics.{module_name}

end
"""
    return text


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
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
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--normal-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.normal_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid Lean module")
    data = read_input(args.input)
    payload = emit(args.module, args.normal_module, data,
                   args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; {data['state_count']} heads")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
