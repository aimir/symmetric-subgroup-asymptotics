#!/usr/bin/env python3
"""Render one prepared eight-frame top as a kernel-checked Lean module.

The mandatory input is one object produced by
``prepare_frames8_selected_top_certificate.py``.  This is deliberately a
selected-row emitter: it has no directory scan, row range, or bulk mode and
it never invokes Lean, GAP, or another subprocess.

The generated module reconstructs the literal degree-eight permutation
group, its executable positive-generator Cayley row, and a complete sparse
conjugacy cover.  The producer's class labels and centralizer orders are
only certificate data: Lean rechecks generator invariance, literal
centralizer cardinalities, and the exact class-size sum.
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
WIDTH = 8


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    return value


def permutation(value: object, width: int = WIDTH) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid permutation width")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def inverse(row: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(row)
    for i, x in enumerate(row):
        result[x] = i
    return tuple(result)


def lookup(values: list[object], variable: str = "i.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return str(values[0])
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{lookup(values[:middle], variable, start)} else "
            f"{lookup(values[middle:], variable, start + middle)})")


def lean_array(values) -> str:
    return "#[" + ",".join(str(x) for x in values) + "]"


def finite_checks(n: int) -> str:
    require(n >= 1, "empty finite check")
    if n <= 16:
        return "(by decide +kernel)"
    left = n // 2
    return (f"(Fin.addCases (m := {left}) (n := {n-left}) "
            f"{finite_checks(left)} {finite_checks(n-left)})")


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def permutation_def(name: str, row: tuple[int, ...]) -> str:
    return f"""private def {name} : Equiv.Perm (Fin {WIDTH}) where
  toFun x := ({lean_array(row)} : Array (Fin {WIDTH}))[x.val]!
  invFun x := ({lean_array(inverse(row))} : Array (Fin {WIDTH}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

"""


def validate(value: dict) -> dict:
    cayley = value.get("cayley")
    require(isinstance(cayley, dict), "missing Cayley data")
    rows = [permutation(row) for row in cayley.get("rows", [])]
    n = value.get("top_order")
    require(type(n) is int and 2 <= n <= 1152 and len(rows) == n,
            "invalid selected top order")
    generators = [permutation(row) for row in value.get("generators", [])]
    d = len(generators)
    require(1 <= d <= 16, "invalid selected generator width")
    codes = cayley.get("codes")
    ranks = cayley.get("ranks")
    parents = cayley.get("parents")
    letters = cayley.get("letters")
    nxt = cayley.get("next")
    previous = cayley.get("previous")
    identity = cayley.get("identity")
    require(isinstance(codes, list) and len(codes) == n and
            all(type(x) is int and 0 <= x < WIDTH ** WIDTH for x in codes),
            "invalid Cayley codes")
    require(len(set(codes)) == n, "Cayley codes are not injective")
    require(all(isinstance(row, list) and len(row) == d and
                all(type(x) is int and 0 <= x < n for x in row)
                for row in nxt), "invalid next table")
    require(all(isinstance(row, list) and len(row) == d and
                all(type(x) is int and 0 <= x < n for x in row)
                for row in previous), "invalid previous table")
    require(isinstance(ranks, list) and len(ranks) == n and
            isinstance(parents, list) and len(parents) == n and
            isinstance(letters, list) and len(letters) == n,
            "invalid Cayley word arrays")
    require(type(identity) is int and 0 <= identity < n,
            "invalid Cayley identity")
    representatives = [permutation(row) for row in
                       value.get("class_representatives", [])]
    centralizers = value.get("centralizer_orders")
    class_code = value.get("class_code")
    c = len(representatives)
    require(1 <= c <= 128 and isinstance(centralizers, list) and
            len(centralizers) == c and all(type(x) is int and x > 0
                                           for x in centralizers),
            "invalid conjugacy rows")
    require(isinstance(class_code, list) and len(class_code) == n and
            all(type(x) is int and 0 <= x < c for x in class_code),
            "invalid class-code row")
    position = {row: i for i, row in enumerate(rows)}
    require(all(row in position for row in representatives),
            "class representative escaped Cayley rows")
    return {
        "source_row": value.get("source_row"),
        "top_index": value.get("top_index"),
        "n": n,
        "d": d,
        "c": c,
        "generators": generators,
        "rows": rows,
        "codes": codes,
        "ranks": ranks,
        "parents": parents,
        "letters": letters,
        "next": nxt,
        "previous": previous,
        "identity": identity,
        "representative_indices": [position[row] for row in representatives],
        "centralizers": centralizers,
        "class_code": class_code,
    }


def emit_module(module: str, data: dict, input_name: str) -> str:
    n, d, c = data["n"], data["d"], data["c"]
    next_expr = (f"({lookup([lean_array(row) for row in data['next']])} : "
                 f"Array (Fin {n}))[j.val]!")
    previous_expr = (f"({lookup([lean_array(row) for row in data['previous']])} : "
                     f"Array (Fin {n}))[j.val]!")
    text = f"""import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.FiniteConjugacyGeneratorInvariant
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCardinalCover
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected eight-frame row {data['source_row']}: executable top {data['top_index']}

Generated by `emit_lean_frames8_selected_top.py` from the explicit selected
input `{input_name}`.  The source JSON is not a proof premise.  The Cayley
transitions, class invariant, literal centralizer cardinalities and exact
class-size exhaustion are all rechecked by Lean.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{module}

"""
    for j, generator in enumerate(data["generators"]):
        text += permutation_def(f"generator{j}", generator)
    text += f"""def generators (j : Fin {d}) : Equiv.Perm (Fin {WIDTH}) :=
  {lookup([f'generator{j}' for j in range(d)], 'j.val')}

private def codes (i : Fin {n}) : Fin ({WIDTH}^{WIDTH}) :=
  {lookup(data['codes'])}

private def ranks (i : Fin {n}) : ℕ :=
  {lookup(data['ranks'])}

private def parents (i : Fin {n}) : Fin {n} :=
  {lookup(data['parents'])}

private def letters (i : Fin {n}) : Fin {d} :=
  {lookup(data['letters'])}

private def nextRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {next_expr}

def previousRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {previous_expr}

private theorem parent_lt_checked : ∀ i : Fin {n},
    i ≠ {data['identity']} → ranks (parents i) < ranks i :=
  {finite_checks(n)}

private theorem parent_next_checked : ∀ i : Fin {n},
    i ≠ {data['identity']} → nextRow (parents i) (letters i) = i :=
  {finite_checks(n)}

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) {n} where
  rows := codes
  identity := {data['identity']}
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := {finite_checks(n)}
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

theorem rows_injective : Function.Injective certificate.rows :=
  by native_decide

theorem previous_checked : ∀ i j,
    certificate.next (previousRow i j) j = i :=
  {finite_checks(n)}

@[reducible] def group : Group (FiniteGroupRow {n}) :=
  certificate.rowGroup rows_injective previousRow previous_checked

abbrev Source := FiniteGroupRow {n}
local instance selectedSourceGroup : Group Source := group

def originalEquiv : Source ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective previousRow previous_checked

/-- The forward map of the finite-row equivalence is the literal decoded
permutation stored in that row.  Exposing this computational half avoids
unfolding the noncomputable inverse when downstream certificates check a
point-stabilizer predicate. -/
@[simp] theorem originalEquiv_apply (s : Source) :
    ((originalEquiv s : Subgroup.closure (Set.range generators)) :
      Equiv.Perm (Fin 8)) = certificate.toCayley.elements s.index :=
  rfl

def ambient (j : Fin {d}) : Source :=
  ⟨certificate.next certificate.identity j⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  certificate.row_generators_full rows_injective previousRow previous_checked

theorem source_card : Nat.card Source = {n} := by
  rw [Nat.card_eq_fintype_card]
  rfl

private def representativeRows (i : Fin {c}) : Fin {n} :=
  {lookup(data['representative_indices'])}

def representative (i : Fin {c}) : Source := ⟨representativeRows i⟩

private def classCodeRows (i : Fin {n}) : Fin {c} :=
  {lookup(data['class_code'])}

private def classCode (x : Source) : Fin {c} := classCodeRows x.index

def classInvariant : FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin {c}
  code := classCode
  generator_invariant := by
    intro i x
    rcases x with ⟨j⟩
    fin_cases i <;> fin_cases j <;> native_decide
  representative_injective := by decide +kernel

private def centralizerCard (i : Fin {c}) : ℕ :=
  {lookup(data['centralizers'])}

private theorem centralizer_card : ∀ i : Fin {c},
    Nat.card (Subgroup.centralizer ({{representative i}} : Set Source)) =
      centralizerCard i := by
  intro i
  letI : DecidablePred (fun x : Source =>
      x ∈ Subgroup.centralizer ({{representative i}} : Set Source)) :=
    fun x => decidable_of_iff (x * representative i = representative i * x)
      Subgroup.mem_centralizer_singleton_iff.symm
  fin_cases i <;>
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] <;>
    native_decide

private theorem class_card_sum :
    (∑ i : Fin {c}, Nat.card Source / centralizerCard i) =
      Nat.card Source := by
  rw [source_card]
  norm_num [centralizerCard, Fin.sum_univ_succ]

/-- Complete conjugacy cover of the selected literal top. -/
noncomputable def conjugacy :
    FiniteConjugacyCentralizerCardinalCover representative where
  separated := classInvariant.separated ambient_full
  centralizerCard := centralizerCard
  centralizer_card := centralizer_card
  class_card_sum := class_card_sum

end SymmetricSubgroupAsymptotics.{module}

end
"""
    return text


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output ceiling reached")
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
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None,
            "invalid Lean module name")
    data = validate(read_input(args.input))
    payload = emit_module(args.module, data, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; row {data['source_row']}; "
          f"top {data['top_index']}; order {data['n']}; classes {data['c']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
