#!/usr/bin/env python3
"""Render one grouped eight-frame point-stabilizer normal table in Lean.

The input is produced by
``prepare_frames8_selected_stabilizer_normal_table.py``.  The generated file
uses one stabilizer conjugacy cover and one normal-join word registry for all
listed row kernels, then invokes ``GeneratedSourceLocalNormalTable`` to obtain
the exact local quotient catalogue.  It never invokes Lean or a subprocess.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import tempfile


SCHEMA = "frames8-selected-stabilizer-normal-table-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def balanced(values: list[str], variable: str, start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{balanced(values[:middle], variable, start)} else "
            f"{balanced(values[middle:], variable, start + middle)})")


def lean_generator_word(word: object) -> str:
    require(isinstance(word, dict), "generator word is not an object")
    tag = word.get("tag")
    if tag == "one":
        return "FiniteGeneratorWord.one"
    if tag == "generator":
        return f"FiniteGeneratorWord.generator {word['index']}"
    if tag == "inv":
        return f"FiniteGeneratorWord.inv ({lean_generator_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteGeneratorWord.mul ({lean_generator_word(word['left'])}) "
                f"({lean_generator_word(word['right'])})")
    raise Refused(f"unsupported generator-word tag {tag!r}")


def lean_join_word(word: object) -> str:
    require(isinstance(word, dict), "join word is not an object")
    tag = word.get("tag")
    if tag == "one":
        return "FiniteNormalJoinWord.one"
    if tag == "parent":
        return f"FiniteNormalJoinWord.parent {word['index']}"
    if tag == "conjugate":
        return ("FiniteNormalJoinWord.conjugate "
                f"(({lean_generator_word(word['conjugator'])}).eval ambient)")
    if tag == "inv":
        return f"FiniteNormalJoinWord.inv ({lean_join_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteNormalJoinWord.mul ({lean_join_word(word['left'])}) "
                f"({lean_join_word(word['right'])})")
    raise Refused(f"unsupported join-word tag {tag!r}")


def read_and_validate(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared stabilizer table")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared stabilizer table ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared stabilizer-table schema")
    n = len(value.get("classification", []))
    c = len(value.get("class_representative_indices", []))
    a = value.get("ambient_count")
    k = value.get("normal_generator_width")
    r = len(value.get("source_rows", []))
    top_order = value.get("top_order")
    require(1 <= n <= 256 and 1 <= c <= 144 and 1 <= r <= 16,
            "invalid grouped table dimensions")
    require(type(a) is int and 1 <= a <= 32 and
            type(k) is int and 1 <= k <= 16 and
            type(top_order) is int and 1 <= top_order <= 1152,
            "invalid grouped generator dimensions")
    require(len(value.get("ambient_indices", [])) == a and
            len(value.get("centralizer_orders", [])) == c and
            len(value.get("class_code", [])) == top_order,
            "invalid grouped conjugacy data")
    require(len(value.get("normal_generators", [])) == n and
            all(len(row) == k for row in value["normal_generators"]),
            "invalid grouped normal generators")
    require(len(value.get("normal_orders", [])) == n and
            len(value.get("state_words", [])) == n and
            all(len(row) == top_order for row in value["state_words"]),
            "invalid grouped explicit-state data")
    require(len(value.get("normality", [])) == n and
            len(value.get("children", [])) == n and
            len(value.get("transitions", [])) == n,
            "invalid grouped normal registry")
    require(len(value.get("kernel_states", [])) == r,
            "invalid grouped kernel-state data")
    for i in range(n):
        require(len(value["children"][i]) == c and
                len(value["transitions"][i]) == c,
                "normal transition width mismatch")
        normality = value["normality"][i]
        require(set(normality) == {"positive", "negative"},
                "invalid normality record")
        for sign in ("positive", "negative"):
            require(len(normality[sign]) == a and
                    all(len(row) == k for row in normality[sign]),
                    "normality word width mismatch")
        for child, transition in zip(value["children"][i],
                                     value["transitions"][i]):
            require(type(child) is int and 0 <= child < n,
                    "normal child index out of range")
            require(set(transition) == {"parent_to_child",
                                        "representative_word",
                                        "child_to_join"} and
                    len(transition["parent_to_child"]) == k and
                    len(transition["child_to_join"]) == k,
                    "invalid normal transition record")
    for item in value["classification"]:
        require(isinstance(item, dict) and
                item.get("tag") in {"row", "irrelevant", "commutative-six"},
                "invalid normal-state classification")
        if item["tag"] == "row":
            require(type(item.get("row")) is int and 0 <= item["row"] < r,
                    "classified row index out of range")
    return value


def element(top_order: int, index: int) -> str:
    require(type(index) is int and 0 <= index < top_order,
            "source element index out of range")
    return (f"(⟨(⟨{index}⟩ : Top.ModelGroup), by native_decide +revert⟩ : "
            "Top.sourceStabilizer)")


def emit(module: str, table_module: str, top_data: str,
         stabilizer_module: str, row_data: list[str], data: dict,
         input_name: str) -> str:
    n = len(data["classification"])
    c = len(data["class_representative_indices"])
    a = data["ambient_count"]
    k = data["normal_generator_width"]
    r = len(row_data)
    top_order = data["top_order"]
    stabilizer_order = data["stabilizer_order"]

    representative_values = [element(top_order, x)
                             for x in data["class_representative_indices"]]
    state_names = [f"state{i}Generators" for i in range(n)]
    class_codes = [str(x) for x in data["class_code"]]
    centralizers = [str(x) for x in data["centralizer_orders"]]
    normal_orders = [str(x) for x in data["normal_orders"]]

    text = f"""import SymmetricSubgroupAsymptotics.{table_module}
import SymmetricSubgroupAsymptotics.{stabilizer_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.FiniteConjugacyGeneratorInvariant
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates
import Mathlib.Tactic.FinCases

/-!
# Grouped eight-frame top {data['top_index']}: point-stabilizer normal table

Generated by `emit_lean_frames8_grouped_stabilizer_normals.py` from the
explicit selected input `{input_name}`.  One checked stabilizer normal lattice
serves source rows {data['source_rows']}.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace {module}

abbrev Top : GeneratedTopData := {top_data}

def ambient : Fin {a} → Top.sourceStabilizer :=
  {stabilizer_module}.generators

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  {stabilizer_module}.generators_full

private def representative : Fin {c} → Top.sourceStabilizer :=
  {fin_cases_chain(representative_values)}

private def classCodeRows (i : Fin {top_order}) : Fin {c} :=
  {balanced(class_codes, 'i.val')}

private def classCode (x : Top.sourceStabilizer) : Fin {c} :=
  classCodeRows x.1.index

private def classInvariant :
    FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin {c}
  code := classCode
  generator_invariant := by native_decide +revert
  representative_injective := by native_decide +revert

private def centralizerCard (i : Fin {c}) : ℕ :=
  {balanced(centralizers, 'i.val')}

private theorem source_card : Nat.card Top.sourceStabilizer =
    {stabilizer_order} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  native_decide +revert

private theorem centralizer_card : ∀ i : Fin {c},
    Nat.card (Subgroup.centralizer ({{representative i}} :
      Set Top.sourceStabilizer)) = centralizerCard i := by
  intro i
  letI : DecidablePred (fun x : Top.sourceStabilizer =>
      x ∈ Subgroup.centralizer
        ({{representative i}} : Set Top.sourceStabilizer)) :=
    fun x => decidable_of_iff
      (x * representative i = representative i * x)
      Subgroup.mem_centralizer_singleton_iff.symm
  fin_cases i <;>
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] <;>
    native_decide +revert

private theorem class_card_sum :
    (∑ i : Fin {c}, Nat.card Top.sourceStabilizer / centralizerCard i) =
      Nat.card Top.sourceStabilizer := by
  rw [source_card]
  norm_num [centralizerCard, Fin.sum_univ_succ]

noncomputable def conjugacy :
    FiniteConjugacyCentralizerCardinalCover representative where
  separated := classInvariant.separated ambient_full
  centralizerCard := centralizerCard
  centralizer_card := centralizer_card
  class_card_sum := class_card_sum

"""

    for i, indices in enumerate(data["normal_generators"]):
        text += f"""private def {state_names[i]} : Fin {k} →
    Top.sourceStabilizer :=
  {fin_cases_chain([element(top_order, x) for x in indices])}

"""

    text += f"""def stateGenerators : Fin {n} → Fin {k} →
    Top.sourceStabilizer :=
  {fin_cases_chain(state_names)}

private def child : Fin {n} → Fin {c} → Fin {n} :=
  {fin_cases_chain([fin_cases_chain([str(x) for x in row])
                    for row in data['children']])}

"""

    for i in range(n):
        normal = data["normality"][i]
        positive = [fin_cases_chain([lean_generator_word(w) for w in row])
                    for row in normal["positive"]]
        negative = [fin_cases_chain([lean_generator_word(w) for w in row])
                    for row in normal["negative"]]
        text += f"""namespace N{i}

private def positiveWords : Fin {a} → Fin {k} →
    FiniteGeneratorWord (Fin {k}) :=
  {fin_cases_chain(positive)}

private def negativeWords : Fin {a} → Fin {k} →
    FiniteGeneratorWord (Fin {k}) :=
  {fin_cases_chain(negative)}

def normality : FiniteNormalityWordCertificate ambient
    (stateGenerators {i}) where
  positiveWords := positiveWords
  positiveEquations := by native_decide +revert
  negativeWords := negativeWords
  negativeEquations := by native_decide +revert

"""
        transition_names = []
        for j in range(c):
            record = data["transitions"][i][j]
            transition_names.append(f"T{j}.certificate")
            text += f"""namespace T{j}

private def parentWords : Fin {k} → FiniteGeneratorWord (Fin {k}) :=
  {fin_cases_chain([lean_generator_word(w)
                    for w in record['parent_to_child']])}

private def childWords : Fin {k} →
    FiniteNormalJoinWord (Fin {k}) Top.sourceStabilizer :=
  {fin_cases_chain([lean_join_word(w)
                    for w in record['child_to_join']])}

private def representativeWord : FiniteGeneratorWord (Fin {k}) :=
  {lean_generator_word(record['representative_word'])}

def certificate : FiniteNormalJoinTransitionCertificate
    (stateGenerators {i}) (representative {j})
    (stateGenerators (child {i} {j})) where
  parentToChild := {{
    words := parentWords
    equations := by native_decide +revert }}
  representativeWord := representativeWord
  representativeEquation := by native_decide +revert
  childWords := childWords
  childEquations := by native_decide +revert

end T{j}

"""
        text += f"""def transition : ∀ j : Fin {c},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators {i}) (representative j)
      (stateGenerators (child {i} j)) :=
  {fin_cases_chain(transition_names)}

end N{i}

"""

    text += f"""noncomputable def normality : ∀ i : Fin {n},
    FiniteNormalityWordCertificate ambient (stateGenerators i) :=
  {fin_cases_chain([f'N{i}.normality' for i in range(n)])}

noncomputable def transition : ∀ i : Fin {n}, ∀ j : Fin {c},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (representative j)
      (stateGenerators (child i j)) :=
  {fin_cases_chain([f'N{i}.transition' for i in range(n)])}

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

noncomputable def registry : FiniteNormalJoinWordRegistryData
    conjugacy.toCardinalCover ambient stateGenerators where
  ambient_full := ambient_full
  normality := normality
  bottom := 0
  bottom_eq := bottom_eq
  child := child
  transition := transition

"""

    # Explicit decidable state subgroups and checked member words.  These
    # avoid asking native_decide to evaluate the abstract closure operation.
    for i, words in enumerate(data["state_words"]):
        members = ["true" if word is not None else "false" for word in words]
        word_values = ["FiniteGeneratorWord.one" if word is None
                       else lean_generator_word(word) for word in words]
        text += f"""private def stateMember{i} (j : Fin {top_order}) : Bool :=
  {balanced(members, 'j.val')}

private def stateWord{i} (x : Top.sourceStabilizer) :
    FiniteGeneratorWord (Fin {k}) :=
  {balanced(word_values, 'x.1.index.val')}

"""

    text += f"""private def stateMember : Fin {n} → Fin {top_order} → Bool :=
  {fin_cases_chain([f'stateMember{i}' for i in range(n)])}

private def stateWord : ∀ s : Fin {n}, Top.sourceStabilizer →
    FiniteGeneratorWord (Fin {k}) :=
  {fin_cases_chain([f'stateWord{i}' for i in range(n)])}

private def stateSubgroup (s : Fin {n}) : Subgroup Top.sourceStabilizer where
  carrier := {{x | stateMember s x.1.index = true}}
  one_mem' := by fin_cases s <;> native_decide +revert
  mul_mem' := by intro x y hx hy; fin_cases s <;> native_decide +revert
  inv_mem' := by intro x hx; fin_cases s <;> native_decide +revert

private theorem stateWord_checked : ∀ (s : Fin {n})
    (x : Top.sourceStabilizer), x ∈ stateSubgroup s →
      (stateWord s x).eval (stateGenerators s) = x := by
  intro s x hx
  fin_cases s <;> native_decide +revert

private theorem state_generated (s : Fin {n}) :
    Subgroup.closure (Set.range (stateGenerators s)) = stateSubgroup s := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases s <;> fin_cases j <;> native_decide +revert
  · intro x hx
    rw [← stateWord_checked s x hx]
    exact (stateWord s x).eval_mem_closure (stateGenerators s)

private def stateOrder (s : Fin {n}) : ℕ :=
  {balanced(normal_orders, 's.val')}

private theorem stateSubgroup_card (s : Fin {n}) :
    Nat.card (stateSubgroup s) = stateOrder s := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases s <;> native_decide +revert

private def stateIndex (s : Fin {n}) : ℕ :=
  {balanced([str(stabilizer_order // x) for x in data['normal_orders']], 's.val')}

private theorem stateSubgroup_index (s : Fin {n}) :
    (stateSubgroup s).index = stateIndex s := by
  have h := (stateSubgroup s).card_mul_index
  rw [stateSubgroup_card, source_card] at h
  fin_cases s <;> norm_num [stateOrder, stateIndex] at h ⊢ <;> omega

noncomputable def rowData : Fin {r} → GeneratedRowData Top :=
  {fin_cases_chain(row_data)}

"""

    classification_proofs = []
    for state_index, item in enumerate(data["classification"]):
        if item["tag"] == "row":
            row = item["row"]
            row_expr = row_data[row]
            proof = f"""(by
      apply Or.inl
      refine ⟨{row}, ?_⟩
      rw [state_generated]
      ext x
      change stateMember {state_index} x.1.index = true ↔
        ({row_expr}).sourceLocalMap x = 1
      simp only [{row_expr}]
      native_decide +revert)"""
        elif item["tag"] == "irrelevant":
            proof = f"""(by
      apply Or.inr
      apply Or.inl
      constructor <;>
        rw [state_generated, stateSubgroup_index] <;>
        norm_num [stateIndex])"""
        else:
            proof = f"""(by
      apply Or.inr
      apply Or.inr
      have hnormal :
          (Subgroup.closure (Set.range (stateGenerators {state_index}))).Normal :=
        (normality {state_index}).normal ambient_full
      refine ⟨?_, hnormal, ?_⟩
      · rw [state_generated, stateSubgroup_index]
        norm_num [stateIndex]
      · letI :
            (Subgroup.closure (Set.range
              (stateGenerators {state_index}))).Normal := hnormal
        apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        apply commutator_le_of_generator_commutators _ ambient ambient_full
        intro i j
        rw [state_generated]
        change stateMember {state_index}
          (⁅ambient i, ambient j⁆ : Top.sourceStabilizer).1.index = true
        native_decide +revert)"""
        classification_proofs.append(proof)

    text += f"""private theorem classify : ∀ s : Fin {n},
    (∃ r, Subgroup.closure (Set.range (stateGenerators s)) =
      (rowData r).sourceLocalMap.ker) ∨
    ((Subgroup.closure (Set.range (stateGenerators s))).index ≠ 3 ∧
      (Subgroup.closure (Set.range (stateGenerators s))).index ≠ 6) ∨
    ((Subgroup.closure (Set.range (stateGenerators s))).index = 6 ∧
      ∃ _normal :
        (Subgroup.closure (Set.range (stateGenerators s))).Normal,
        IsMulCommutative
          (Top.sourceStabilizer ⧸
            Subgroup.closure (Set.range (stateGenerators s)))) :=
  {fin_cases_chain(classification_proofs)}

/-- One complete source-local normal table shared by all grouped rows. -/
noncomputable def localNormalTable : GeneratedSourceLocalNormalTable Top :=
  GeneratedSourceLocalNormalTable.ofWordRegistry Top
    conjugacy.toCardinalCover ambient stateGenerators registry rowData classify

/-- Exact local quotient catalogue recovered from the checked normal table. -/
noncomputable def table : GeneratedTopTable Top :=
  localNormalTable.toTopTable

end {module}
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

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
    parser.add_argument("--table-module", required=True)
    parser.add_argument("--top-data", required=True)
    parser.add_argument("--stabilizer-module", required=True)
    parser.add_argument("--row-data", required=True, action="append")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.table_module, args.stabilizer_module):
        require(MODULE_RE.fullmatch(name) is not None,
                f"invalid Lean module name {name!r}")
    for name in [args.top_data] + args.row_data:
        require(NAME_RE.fullmatch(name) is not None,
                f"invalid Lean declaration name {name!r}")
    data = read_and_validate(args.input)
    require(len(args.row_data) == len(data["source_rows"]),
            "row-data count does not match prepared grouped rows")
    payload = emit(args.module, args.table_module, args.top_data,
                   args.stabilizer_module, args.row_data, data,
                   args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; top {data['top_index']}; "
          f"{len(data['classification'])} normal states; "
          f"{len(args.row_data)} grouped rows")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
