#!/usr/bin/env python3
"""Emit the one-general three-normal-chain pilot for action 023.

This is a deliberately hard-whitelisted pilot.  It accepts exactly action
023, one complete selected class chunk, and one complete selected normal
chunk.  There is no range, directory-scan, chunk-selection, or all-actions
mode, and this script never invokes Lean, a subprocess, or another exporter.

The JSON and pinned catalogue select and validate the intended pilot only.
The emitted Lean file proves the three normal-state equations from the
literal generators and the checked normal registry.  A four-row literal
Cayley certificate proves that the middle state is proper; no declared JSON
order or character field is turned into a proof hypothesis.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile


sys.dont_write_bytecode = True


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/six_block.json.gz"
DATA_SHA256 = "446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3"
ACTION = 23
ACTION_COUNT = 182
ACTION_ORDER = 12
AMBIENT_COUNT = 3
CLASS_COUNT = 4
NORMAL_COUNT = 3
NORMAL_WIDTH = 3
MIDDLE_ORDER = 4
CLASS_RANGE = [1, 4]
NORMAL_RANGE = [1, 3]
WIDTH = 12
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
INPUT_LIMIT = 256 * 1024
OUTPUT_LIMIT = 96 * 1024
EXPECTED_MODULE = "PrimitiveAffineDegreeTwoSixPairAction023OneGeneralPilot"
EXPECTED_ACTION_MODULE = "PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow"
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    require(len(a) == len(b), "permutation widths differ")
    return tuple(a[b[x]] for x in range(len(a)))


def packed(row: tuple[int, ...]) -> int:
    return sum(x * WIDTH ** i for i, x in enumerate(row))


def permutation(value: object) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == WIDTH,
            "invalid degree-twelve permutation")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(WIDTH)),
            "invalid degree-twelve permutation")
    return row


def enumerate_positive(generators: list[tuple[int, ...]]) -> dict:
    """Enumerate by right positive generators, retaining short words."""
    require(generators, "empty selected generator family")
    one = tuple(range(WIDTH))
    rows = [one]
    position = {one: 0}
    words: list[list[int]] = [[]]
    cursor = 0
    while cursor < len(rows):
        require(len(rows) <= ACTION_ORDER,
                "action023 generated-row ceiling reached")
        current = rows[cursor]
        for letter, generator in enumerate(generators):
            target = compose(current, generator)
            if target not in position:
                position[target] = len(rows)
                rows.append(target)
                words.append(words[cursor] + [letter])
        cursor += 1
    transitions = [
        [position[compose(row, generator)] for generator in generators]
        for row in rows
    ]
    return {
        "rows": rows,
        "position": position,
        "words": words,
        "transitions": transitions,
    }


def enumerate_source_rows(generators: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    """Match the packed row order used by the checked class-base emitter."""
    enumeration = enumerate_positive(generators)
    return sorted(enumeration["rows"], key=packed)


def read_pinned_data() -> dict:
    require(DATA.is_file() and not DATA.is_symlink(),
            "missing or redirected six-block data")
    compressed = DATA.read_bytes()
    require(len(compressed) <= COMPRESSED_DATA_LIMIT,
            "compressed six-block data ceiling reached")
    require(digest(compressed) == DATA_SHA256,
            "six-block data digest changed")
    raw = gzip.decompress(compressed)
    require(len(raw) <= DECOMPRESSED_DATA_LIMIT,
            "decompressed six-block data ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema_version") == 1,
            "unexpected six-block schema")
    require(len(value.get("actions", [])) == ACTION_COUNT,
            "six-block action count changed")
    return value


def read_selected_chunk(path: Path, stage: str) -> dict:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected {stage} input")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, f"{stage} input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), f"{stage} input is not an object")
    require(value.get("schema_version") == 1,
            f"unexpected {stage} input schema")
    require(value.get("source_sha256") == DATA_SHA256,
            f"{stage} source digest changed")
    require(value.get("action") == ACTION,
            f"{stage} input is not action023")
    require(value.get("stage") == stage,
            f"expected a {stage} selected chunk")
    require(value.get("chunk") == 0,
            f"action023 {stage} pilot requires chunk zero")
    require(value.get("action_order") == ACTION_ORDER,
            f"action023 {stage} action order changed")
    require(value.get("ambient_generator_count") == AMBIENT_COUNT,
            f"action023 {stage} ambient width changed")
    return value


def validate_and_prepare(class_chunk: dict, normal_chunk: dict,
                         data: dict) -> dict:
    require(class_chunk.get("range") == CLASS_RANGE,
            "action023 pilot requires the complete class chunk")
    require(normal_chunk.get("range") == NORMAL_RANGE,
            "action023 pilot requires the complete normal chunk")
    class_content = class_chunk.get("content")
    normal_content = normal_chunk.get("content")
    require(isinstance(class_content, dict) and
            isinstance(class_content.get("rows"), list),
            "missing action023 class rows")
    require(isinstance(normal_content, dict) and
            isinstance(normal_content.get("rows"), list),
            "missing action023 normal rows")
    require([row.get("class_index") for row in class_content["rows"]] ==
            list(range(1, CLASS_COUNT + 1)),
            "action023 class rows are not the complete ordered range")
    require([row.get("normal_index") for row in normal_content["rows"]] ==
            list(range(1, NORMAL_COUNT + 1)),
            "action023 normal rows are not the complete ordered range")

    action = data["actions"][ACTION - 1]
    ambient = [permutation(row) for row in action.get("generators", [])]
    require(action.get("order") == ACTION_ORDER,
            "pinned action023 order changed")
    require(len(ambient) == AMBIENT_COUNT,
            "pinned action023 ambient width changed")
    require(len(action.get("class_representatives", [])) == CLASS_COUNT,
            "pinned action023 class count changed")
    normals = action.get("normals")
    require(isinstance(normals, list) and len(normals) == NORMAL_COUNT,
            "pinned action023 normal count changed")

    # These catalogue fields select the intended chain.  They are not emitted
    # as Lean assumptions: bottom/top are literal equations, middle properness
    # is a finite Cayley-cardinality proof, and completeness comes from the
    # kernel-checked normal registry.
    expected_orders = [1, MIDDLE_ORDER, ACTION_ORDER]
    expected_widths = [0, 2, AMBIENT_COUNT]
    expected_characters = [[1], [2], []]
    for index, normal in enumerate(normals):
        require(normal.get("order") == expected_orders[index],
                f"pinned action023 normal order {index} changed")
        require(normal.get("kind") == "characters" and
                normal.get("characters") == expected_characters[index],
                f"pinned action023 character row {index} changed")
        require(len(normal.get("generators", [])) == expected_widths[index],
                f"pinned action023 normal width {index} changed")
        require(normal_content["rows"][index].get("declared_order") ==
                expected_orders[index],
                f"selected action023 declared normal order {index} changed")
    require(normals[2].get("generators") == action.get("generators"),
            "pinned action023 top generators no longer match the ambient tuple")
    require(action.get("character_kernels") == [[1, 3], [2, 1], [3, 1]],
            "pinned action023 character-kernel shape changed")

    source_rows = enumerate_source_rows(ambient)
    require(len(source_rows) == ACTION_ORDER,
            "literal action023 enumeration no longer has order twelve")
    source_position = {row: index for index, row in enumerate(source_rows)}
    middle_generators = [permutation(row) for row in normals[1]["generators"]]
    padded_middle_generators = middle_generators + [tuple(range(WIDTH))]
    require(len(padded_middle_generators) == NORMAL_WIDTH,
            "action023 padded middle width changed")
    middle = enumerate_positive(padded_middle_generators)
    require(len(middle["rows"]) == MIDDLE_ORDER,
            "literal action023 middle subgroup no longer has four rows")
    require(all(row in source_position for row in middle["rows"]),
            "middle row escaped the literal action")
    return {
        "source_indices": [source_position[row] for row in middle["rows"]],
        "middle_generator_indices": [source_position[row]
                                     for row in padded_middle_generators],
        "middle_next": middle["transitions"],
        "middle_words": middle["words"],
    }


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def lean_fin_list(word: list[int]) -> str:
    if not word:
        return "([] : List (Fin 3))"
    return ("([" + ", ".join(str(letter) for letter in word) +
            "] : List (Fin 3))")


def emit_module(module: str, action_module: str, prepared: dict,
                class_input_name: str, normal_input_name: str) -> str:
    source_values = [f"(⟨{index}⟩ : ClassPilot.Source)"
                     for index in prepared["source_indices"]]
    generator_values = [f"(⟨{index}⟩ : ClassPilot.Source)"
                        for index in prepared["middle_generator_indices"]]
    next_rows = [fin_cases_chain([str(value) for value in row])
                 for row in prepared["middle_next"]]
    word_values = [lean_fin_list(word) for word in prepared["middle_words"]]
    middle_source_elements = fin_cases_chain(source_values)
    middle_source_generators = fin_cases_chain(generator_values)
    middle_next = fin_cases_chain(next_rows)
    middle_words = fin_cases_chain(word_values)

    return f"""import SymmetricSubgroupAsymptotics.{action_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralRows
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 023: three-normal-chain pilot

Generated by `emit_lean_six_pair_selected_one_general_chain_pilot.py` from
the explicit selected inputs `{class_input_name}` and `{normal_input_name}`.
Both inputs point to the pinned six-block source digest `{DATA_SHA256}`.

The JSON character and order fields are not proof premises.  State zero and
state two are proved bottom and top by literal generator equations.  A
four-row `FiniteCayleyCertificate` proves the middle state is proper, while
the checked normal registry proves these three states exhaust every normal
subgroup.  The generic chain helper then supplies exactly the bottom,
middle, and top quotient socle-generator rows.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.{module}

open Non2UnipotentPrefixFiniteMenu
namespace ClassPilot := PrimitiveAffineDegreeTwoSixPairAction023ClassPilot
namespace CatalogueRow := PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow

private abbrev Original := CatalogueRow.Original

private def stateZero :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨0, by change 0 < 3; norm_num⟩

private def stateMiddle :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨1, by change 1 < 3; norm_num⟩

private def stateTop :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨2, by change 2 < 3; norm_num⟩

private def genZero :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalGeneratorWidth :=
  ⟨0, by change 0 < 3; norm_num⟩

private def genOne :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalGeneratorWidth :=
  ⟨1, by change 1 < 3; norm_num⟩

private def genTwo :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalGeneratorWidth :=
  ⟨2, by change 2 < 3; norm_num⟩

private theorem state_zero_eq_bot :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1 =
      ⊥ := by
  change Subgroup.closure (Set.range (CatalogueRow.stateGenerators 0)) = ⊥
  exact CatalogueRow.normalRegistry.bottom_eq

private theorem state_top_generator (j : Fin 3) :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop j =
      CatalogueRow.ambient j := by
  fin_cases j
  · change CatalogueRow.stateGenerators 2 0 = CatalogueRow.ambient 0
    exact congrArg ClassPilot.originalEquiv (by native_decide)
  · change CatalogueRow.stateGenerators 2 1 = CatalogueRow.ambient 1
    exact congrArg ClassPilot.originalEquiv (by native_decide)
  · change CatalogueRow.stateGenerators 2 2 = CatalogueRow.ambient 2
    exact congrArg ClassPilot.originalEquiv (by native_decide)

private theorem state_top_generator_range :
    Set.range
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop) =
      Set.range CatalogueRow.ambient := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, state_top_generator j⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (state_top_generator j).symm⟩

private theorem state_top_eq_top :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1 =
      ⊤ := by
  change Subgroup.closure
    (Set.range
      (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop)) = ⊤
  rw [state_top_generator_range]
  exact CatalogueRow.normalRegistry.ambient_full

private def middleSourceElement : Fin 4 → ClassPilot.Source :=
  {middle_source_elements}

private def middleSourceGenerator : Fin 3 → ClassPilot.Source :=
  {middle_source_generators}

private def middleNext : Fin 4 → Fin 3 → Fin 4 :=
  {middle_next}

private def middleWords : Fin 4 → List (Fin 3) :=
  {middle_words}

private theorem middle_generator_source (j : Fin 3) :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateMiddle j =
      ClassPilot.originalEquiv (middleSourceGenerator j) := by
  fin_cases j
  · change CatalogueRow.stateGenerators 1 0 =
      ClassPilot.originalEquiv (middleSourceGenerator 0)
    exact congrArg ClassPilot.originalEquiv (by native_decide)
  · change CatalogueRow.stateGenerators 1 1 =
      ClassPilot.originalEquiv (middleSourceGenerator 1)
    exact congrArg ClassPilot.originalEquiv (by native_decide)
  · change CatalogueRow.stateGenerators 1 2 =
      ClassPilot.originalEquiv (middleSourceGenerator 2)
    exact congrArg ClassPilot.originalEquiv (by native_decide)

private theorem middle_source_identity : middleSourceElement 0 = 1 := by
  native_decide

private theorem middle_source_next (i : Fin 4) (j : Fin 3) :
    middleSourceElement (middleNext i j) =
      middleSourceElement i * middleSourceGenerator j := by
  fin_cases i <;> fin_cases j <;> native_decide

private theorem middle_source_words (i : Fin 4) :
    middleSourceElement i =
      ((middleWords i).map middleSourceGenerator).prod := by
  fin_cases i <;> native_decide

private theorem middle_source_injective :
    Function.Injective middleSourceElement := by
  intro i j h
  fin_cases i <;> fin_cases j <;> native_decide

private noncomputable def middleElements (i : Fin 4) : Original :=
  ClassPilot.originalEquiv (middleSourceElement i)

private theorem middle_word_map (w : List (Fin 3)) :
    ClassPilot.originalEquiv
        ((w.map middleSourceGenerator).prod) =
      (w.map
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
          stateMiddle)).prod := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, map_one]
  | cons j w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ClassPilot.originalEquiv.map_mul, ← middle_generator_source j, ih]

private noncomputable def middleCertificate :
    FiniteCayleyCertificate
      (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateMiddle) 4
    where
  elements := middleElements
  identity := 0
  identity_eq := by
    calc
      middleElements 0 = ClassPilot.originalEquiv 1 :=
        congrArg ClassPilot.originalEquiv middle_source_identity
      _ = 1 := map_one ClassPilot.originalEquiv
  next := middleNext
  next_eq := by
    intro i j
    rw [middle_generator_source, ← ClassPilot.originalEquiv.map_mul]
    exact congrArg ClassPilot.originalEquiv (middle_source_next i j)
  words := middleWords
  words_eq := by
    intro i
    calc
      middleElements i =
          ClassPilot.originalEquiv
            (((middleWords i).map middleSourceGenerator).prod) :=
        congrArg ClassPilot.originalEquiv (middle_source_words i)
      _ = ((middleWords i).map
            (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
              stateMiddle)).prod := middle_word_map (middleWords i)

private theorem middleElements_injective :
    Function.Injective middleElements :=
  ClassPilot.originalEquiv.injective.comp middle_source_injective

private theorem middle_card :
    Nat.card
      ((degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1) = 4 := by
  change Nat.card
    (Subgroup.closure
      (Set.range
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators
          stateMiddle))) = 4
  exact middleCertificate.card_closure middleElements_injective

private theorem original_card : Nat.card Original = 12 := by
  calc
    Nat.card Original = Nat.card ClassPilot.Source :=
      Nat.card_congr ClassPilot.originalEquiv.symm.toEquiv
    _ = 12 := ClassPilot.source_card

private theorem top_card : Nat.card (⊤ : Subgroup Original) = 12 := by
  calc
    Nat.card (⊤ : Subgroup Original) = Nat.card Original :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = 12 := original_card

private theorem middle_ne_top :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊤ := by
  intro h
  have hcard := congrArg Nat.card h
  rw [middle_card, top_card] at hcard
  norm_num at hcard

private theorem middle_generator_ne_one :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
      stateMiddle genZero ≠ 1 := by
  rw [middle_generator_source]
  intro h
  have hsource : middleSourceGenerator genZero = 1 := by
    apply ClassPilot.originalEquiv.injective
    simpa only [map_one] using h
  native_decide at hsource

private theorem middle_generator_mem :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
        stateMiddle genZero ∈
      (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1 := by
  exact Subgroup.subset_closure (Set.mem_range_self genZero)

private theorem middle_ne_bot :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊥ := by
  intro h
  apply middle_generator_ne_one
  apply Subgroup.mem_bot.mp
  rw [← h]
  exact middle_generator_mem

private theorem normal_eq_bot_or_middle_or_top
    (N : Subgroup Original) (hN : N.Normal) :
    N = ⊥ ∨
      N = (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1 ∨ N = ⊤ := by
  letI : N.Normal := hN
  obtain ⟨i, hi⟩ := CatalogueRow.normal_complete N
  fin_cases i
  · have hiZero :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1 =
          N := by
      change Subgroup.closure (Set.range (CatalogueRow.stateGenerators 0)) = N
      exact hi
    exact Or.inl (hiZero.symm.trans state_zero_eq_bot)
  · have hiMiddle :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
          stateMiddle).1 = N := by
      change Subgroup.closure (Set.range (CatalogueRow.stateGenerators 1)) = N
      exact hi
    exact Or.inr (Or.inl hiMiddle.symm)
  · have hiTop :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1 =
          N := by
      change Subgroup.closure (Set.range (CatalogueRow.stateGenerators 2)) = N
      exact hi
    exact Or.inr (Or.inr (hiTop.symm.trans state_top_eq_top))

private noncomputable def chainData :
    FiniteThreeNormalChainData Original where
  middle :=
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1
  middle_normal := inferInstance
  middle_ne_bot := middle_ne_bot
  middle_ne_top := middle_ne_top
  normal_eq_bot_or_middle_or_top := normal_eq_bot_or_middle_or_top
  generator :=
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
      stateMiddle genZero
  generator_mem := middle_generator_mem
  generator_ne_one := middle_generator_ne_one

private noncomputable def state_zero_socleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1) 1 := by
  rw [state_zero_eq_bot]
  exact chainData.bottomQuotientSocleGenerator

private noncomputable def state_middle_socleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
          stateMiddle).1) 1 :=
  chainData.middleQuotientSocleGenerator

private noncomputable def state_top_socleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1) 1 := by
  rw [state_top_eq_top]
  exact chainData.topQuotientSocleGenerator

/-- The three checked normal states assembled into the reusable literal
finite row consumed by both character and B6 dispatchers. -/
noncomputable def degreeTwoSixPairAction023OneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData where
  literal := degreeTwoSixPairAction023CheckedLiteral
  socleGenerator i := by
    fin_cases i
    · simpa [stateZero] using state_zero_socleGenerator
    · simpa [stateMiddle] using state_middle_socleGenerator
    · simpa [stateTop] using state_top_socleGenerator

/-- The complete literal quotient package after applying the published
Zmud input. -/
noncomputable def degreeTwoSixPairAction023CheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  degreeTwoSixPairAction023OneGeneralFiniteRowData
    |>.toCheckedLiteralQuotientAction hZmud

/-- The action-023 B6 certificate on the same literal degree-twelve action. -/
noncomputable def degreeTwoSixPairAction023B6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate degreeTwoSixPairAction023CheckedLiteral.G :=
  degreeTwoSixPairAction023OneGeneralFiniteRowData
    |>.toB6ActionCertificate hZmud

end SymmetricSubgroupAsymptotics.{module}

end
"""


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
    parser.add_argument("--action", required=True, type=int)
    parser.add_argument("--class-input", required=True, type=Path)
    parser.add_argument("--normal-input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--action-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(args.action == ACTION, "this pilot accepts only --action 23")
    require(args.module == EXPECTED_MODULE and
            MODULE_RE.fullmatch(args.module) is not None,
            f"pilot module must be {EXPECTED_MODULE}")
    require(args.action_module == EXPECTED_ACTION_MODULE and
            MODULE_RE.fullmatch(args.action_module) is not None,
            f"action module must be {EXPECTED_ACTION_MODULE}")
    require(args.class_input != args.normal_input,
            "class and normal inputs must be distinct")
    class_chunk = read_selected_chunk(args.class_input, "classes")
    normal_chunk = read_selected_chunk(args.normal_input, "normals")
    prepared = validate_and_prepare(class_chunk, normal_chunk,
                                    read_pinned_data())
    payload = emit_module(args.module, args.action_module, prepared,
                          args.class_input.name,
                          args.normal_input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action 23; "
          "three-state chain; middle rows 4")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
