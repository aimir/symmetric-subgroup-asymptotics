#!/usr/bin/env python3
"""Emit the split three-normal-chain quotient pilot for action 169.

This producer is hard-whitelisted to the explicit action-169 class and normal
chunks.  It has no action selector, range mode, directory scan, subprocess,
or Lean invocation.  The selected normal chunk supplies compact words from
the literal top-state generators to the ambient generators and finite parity
metadata.  The emitted Lean modules recheck every word equation, generator
inequality, and pair-top sign against the executable row group.

The output is split at the proof boundaries which remained small for the
action-023 recovery: literal state bounds, the exhaustive normal-chain datum,
and the final generic variable-state assembly.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile


sys.dont_write_bytecode = True


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/six_block.json.gz"
DATA_SHA256 = "446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3"
ACTION = 169
ACTION_COUNT = 182
ACTION_ORDER = 120
AMBIENT_COUNT = 4
CLASS_COUNT = 7
NORMAL_COUNT = 3
NORMAL_WIDTH = 2
CLASS_RANGE = [1, 7]
NORMAL_RANGE = [1, 3]
WIDTH = 12
PAIR_COUNT = 6
INPUT_LIMIT = 256 * 1024
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 96 * 1024

CLASS_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169ClassPilot"
NORMAL_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169Normals"
CATALOGUE_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169CatalogueRow"
BOUNDS_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169NormalStateBounds"
CHAIN_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169NormalChain"
PILOT_MODULE = "PrimitiveAffineDegreeTwoSixPairAction169OneGeneralPilot"
NAMESPACE = (
    "SymmetricSubgroupAsymptotics."
    "PrimitiveAffineDegreeTwoSixPairAction169ThreeNormalChain"
)


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


def inverse(a: tuple[int, ...]) -> tuple[int, ...]:
    require(sorted(a) == list(range(len(a))), "invalid permutation")
    result = [0] * len(a)
    for x, y in enumerate(a):
        result[y] = x
    return tuple(result)


def permutation(value: object, width: int = WIDTH) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid permutation row width")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def pair_top(row: tuple[int, ...]) -> tuple[int, ...]:
    result = []
    for i in range(PAIR_COUNT):
        a, b = row[2 * i], row[2 * i + 1]
        require(a // 2 == b // 2,
                "literal generator does not preserve the standard pairs")
        result.append(a // 2)
    require(sorted(result) == list(range(PAIR_COUNT)),
            "invalid pair-top permutation")
    return tuple(result)


def permutation_sign(row: tuple[int, ...]) -> int:
    inversions = sum(
        row[i] > row[j]
        for i in range(len(row)) for j in range(i + 1, len(row))
    )
    return -1 if inversions % 2 else 1


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


def read_chunk(path: Path, stage: str) -> dict:
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
            f"{stage} input is not action169")
    require(value.get("stage") == stage,
            f"expected a {stage} selected chunk")
    require(value.get("chunk") == 0,
            f"action169 {stage} pilot requires chunk zero")
    require(value.get("action_order") == ACTION_ORDER,
            f"action169 {stage} action order changed")
    require(value.get("ambient_generator_count") == AMBIENT_COUNT,
            f"action169 {stage} ambient width changed")
    return value


def eval_word(word: object, generators: list[tuple[int, ...]],
              *, depth: int = 0) -> tuple[int, ...]:
    require(depth <= 256, "word depth ceiling reached")
    require(isinstance(word, dict), "word is not an object")
    tag = word.get("tag")
    if tag == "one":
        require(set(word) == {"tag"}, "unexpected one-word field")
        return tuple(range(WIDTH))
    if tag == "generator":
        require(set(word) == {"tag", "index"},
                "unexpected generator-word field")
        index = word["index"]
        require(type(index) is int and 0 <= index < len(generators),
                "word generator index out of range")
        return generators[index]
    if tag == "inv":
        require(set(word) == {"tag", "word"},
                "unexpected inverse-word field")
        return inverse(eval_word(word["word"], generators, depth=depth + 1))
    if tag == "mul":
        require(set(word) == {"tag", "left", "right"},
                "unexpected product-word field")
        return compose(
            eval_word(word["left"], generators, depth=depth + 1),
            eval_word(word["right"], generators, depth=depth + 1),
        )
    raise Refused("unsupported generator-word tag")


def lean_gen_word(word: object) -> str:
    require(isinstance(word, dict), "Lean word is not an object")
    tag = word.get("tag")
    if tag == "one":
        return "FiniteGeneratorWord.one"
    if tag == "generator":
        return f"FiniteGeneratorWord.generator {word['index']}"
    if tag == "inv":
        return f"FiniteGeneratorWord.inv ({lean_gen_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteGeneratorWord.mul ({lean_gen_word(word['left'])}) "
                f"({lean_gen_word(word['right'])})")
    raise Refused("unsupported Lean generator-word tag")


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def validate_and_prepare(class_chunk: dict, normal_chunk: dict,
                         data: dict) -> dict:
    require(class_chunk.get("range") == CLASS_RANGE,
            "action169 requires the complete class chunk")
    require(normal_chunk.get("range") == NORMAL_RANGE,
            "action169 requires the complete normal chunk")
    class_content = class_chunk.get("content")
    normal_content = normal_chunk.get("content")
    require(isinstance(class_content, dict) and
            isinstance(class_content.get("rows"), list),
            "missing action169 class rows")
    require(isinstance(normal_content, dict) and
            isinstance(normal_content.get("rows"), list),
            "missing action169 normal rows")
    require([row.get("class_index") for row in class_content["rows"]] ==
            list(range(1, CLASS_COUNT + 1)),
            "action169 class rows are not the complete ordered range")
    require([row.get("normal_index") for row in normal_content["rows"]] ==
            list(range(1, NORMAL_COUNT + 1)),
            "action169 normal rows are not the complete ordered range")

    action = data["actions"][ACTION - 1]
    ambient = [permutation(row) for row in action.get("generators", [])]
    normals = action.get("normals")
    require(action.get("order") == ACTION_ORDER,
            "pinned action169 order changed")
    require(len(ambient) == AMBIENT_COUNT,
            "pinned action169 ambient width changed")
    require(len(action.get("class_representatives", [])) == CLASS_COUNT,
            "pinned action169 class count changed")
    require(isinstance(normals, list) and len(normals) == NORMAL_COUNT,
            "pinned action169 normal count changed")

    expected_orders = [1, 60, ACTION_ORDER]
    expected_widths = [0, NORMAL_WIDTH, NORMAL_WIDTH]
    expected_characters = [[1], [4], []]
    for index, normal in enumerate(normals):
        require(normal.get("order") == expected_orders[index],
                f"pinned action169 normal order {index} changed")
        require(normal.get("kind") == "characters" and
                normal.get("characters") == expected_characters[index],
                f"pinned action169 character row {index} changed")
        require(len(normal.get("generators", [])) == expected_widths[index],
                f"pinned action169 normal width {index} changed")
        require(normal_content["rows"][index].get("declared_order") ==
                expected_orders[index],
                f"selected action169 declared normal order {index} changed")

    chain = normal_content.get("three_normal_chain")
    require(isinstance(chain, dict),
            "missing selected three-normal-chain fields")
    require(chain.get("bottom_index") == 1 and
            chain.get("middle_index") == 2 and
            chain.get("top_index") == 3,
            "action169 normal-state order changed")
    middle_generators = [
        permutation(row) for row in normals[1].get("generators", [])
    ]
    top_generators = [
        permutation(row) for row in normals[2].get("generators", [])
    ]
    middle_generator = chain.get("middle_nonidentity_generator")
    require(type(middle_generator) is int and
            1 <= middle_generator <= len(middle_generators),
            "invalid action169 middle nonidentity generator")
    require(middle_generators[middle_generator - 1] != tuple(range(WIDTH)),
            "selected middle generator is the identity")
    middle_signs = [permutation_sign(pair_top(row))
                    for row in middle_generators]
    require(chain.get("middle_pair_top_signs") == middle_signs == [1, 1],
            "action169 middle pair-top signs changed")
    odd_ambient = chain.get("odd_ambient_generator")
    require(type(odd_ambient) is int and 1 <= odd_ambient <= len(ambient),
            "missing action169 odd ambient generator")
    require(permutation_sign(pair_top(ambient[odd_ambient - 1])) == -1,
            "selected action169 ambient generator is not odd")
    top_words = chain.get("top_ambient_words")
    require(isinstance(top_words, list) and len(top_words) == len(ambient),
            "action169 top-to-ambient word width changed")
    for index, word in enumerate(top_words):
        require(eval_word(word, top_generators) == ambient[index],
                f"action169 top ambient word {index} failed")
    return {
        "middle_generator": middle_generator - 1,
        "odd_ambient": odd_ambient - 1,
        "top_words": top_words,
    }


def emit_bounds(prepared: dict, class_name: str, normal_name: str) -> str:
    top_words = fin_cases_chain(
        [lean_gen_word(word) for word in prepared["top_words"]]
    )
    middle_generator = prepared["middle_generator"]
    odd_ambient = prepared["odd_ambient"]
    return f"""import SymmetricSubgroupAsymptotics.{CATALOGUE_MODULE}
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairNormalStateQuotients
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistryTransport
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: literal normal-state bounds

Generated by `emit_lean_six_pair_selected_action169_three_normal_chain.py`
from `{class_name}` and `{normal_name}`, both tied to the pinned six-block
digest `{DATA_SHA256}`.  Compact top words and pair-top signs are checked
against the executable source; JSON metadata is not used as a hypothesis.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical

namespace {NAMESPACE}

open Non2UnipotentPrefixFiniteMenu

abbrev Original := {CATALOGUE_MODULE}.Original

def stateZero :
    Fin degreeTwoSixPairAction169CheckedLiteral.normalCount :=
  ⟨0, by change 0 < 3; norm_num⟩

def stateMiddle :
    Fin degreeTwoSixPairAction169CheckedLiteral.normalCount :=
  ⟨1, by change 1 < 3; norm_num⟩

def stateTop :
    Fin degreeTwoSixPairAction169CheckedLiteral.normalCount :=
  ⟨2, by change 2 < 3; norm_num⟩

def middleGenerator :
    Fin degreeTwoSixPairAction169CheckedLiteral.normalGeneratorWidth :=
  ⟨{middle_generator}, by change {middle_generator} < 2; norm_num⟩

def oddAmbient :
    Fin degreeTwoSixPairAction169CheckedLiteral.ambientCount :=
  ⟨{odd_ambient}, by change {odd_ambient} < 4; norm_num⟩

theorem stateZero_eq_bot :
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateZero).1 =
      ⊥ := by
  change Subgroup.closure
    (Set.range ({CATALOGUE_MODULE}.stateGenerators 0)) = ⊥
  exact {CATALOGUE_MODULE}.normalRegistry.bottom_eq

private def topAmbientWords : Fin 4 → FiniteGeneratorWord (Fin 2) :=
  {top_words}

private def topAmbientSourceCertificate :
    FiniteGeneratorWordCertificate
      {CLASS_MODULE}.ambient
      ({NORMAL_MODULE}.stateGenerators 2) where
  words := topAmbientWords
  equations := by
    intro i
    fin_cases i <;> native_decide

private noncomputable def topAmbientCertificate :
    FiniteGeneratorWordCertificate
      {CATALOGUE_MODULE}.ambient
      ({CATALOGUE_MODULE}.stateGenerators 2) :=
  topAmbientSourceCertificate.mapEquiv
    {CLASS_MODULE}.originalEquiv

theorem stateTop_eq_top :
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateTop).1 =
      ⊤ := by
  change Subgroup.closure
    (Set.range ({CATALOGUE_MODULE}.stateGenerators 2)) = ⊤
  apply top_unique
  rw [← {CATALOGUE_MODULE}.normalRegistry.ambient_full]
  exact topAmbientCertificate.closure_le

private def pairTopSign : Original →* ℤˣ :=
  Equiv.Perm.sign.comp
    ({CLASS_MODULE}.pairTop.comp
      {CLASS_MODULE}.originalEquiv.symm.toMonoidHom)

private theorem middleSourceGenerator_sign (j : Fin 2) :
    Equiv.Perm.sign
        ({CLASS_MODULE}.pairTop
          ({NORMAL_MODULE}.stateGenerators 1 j)) = 1 := by
  fin_cases j <;> native_decide

private theorem middleGenerator_sign (j : Fin 2) :
    pairTopSign ({CATALOGUE_MODULE}.stateGenerators 1 j) = 1 := by
  change Equiv.Perm.sign
    ({CLASS_MODULE}.pairTop
      ({CLASS_MODULE}.originalEquiv.symm
        ({CLASS_MODULE}.originalEquiv
          ({NORMAL_MODULE}.stateGenerators 1 j)))) = 1
  rw [{CLASS_MODULE}.originalEquiv.symm_apply_apply]
  exact middleSourceGenerator_sign j

private theorem middle_le_pairTopSign_ker :
    Subgroup.closure
        (Set.range ({CATALOGUE_MODULE}.stateGenerators 1)) ≤
      pairTopSign.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  change pairTopSign ({CATALOGUE_MODULE}.stateGenerators 1 j) = 1
  exact middleGenerator_sign j

private theorem oddAmbientSource_sign :
    Equiv.Perm.sign
        ({CLASS_MODULE}.pairTop
          ({CLASS_MODULE}.ambient oddAmbient)) ≠ 1 := by
  native_decide

private theorem oddAmbient_sign :
    pairTopSign ({CATALOGUE_MODULE}.ambient oddAmbient) ≠ 1 := by
  change Equiv.Perm.sign
    ({CLASS_MODULE}.pairTop
      ({CLASS_MODULE}.originalEquiv.symm
        ({CLASS_MODULE}.originalEquiv
          ({CLASS_MODULE}.ambient oddAmbient)))) ≠ 1
  rw [{CLASS_MODULE}.originalEquiv.symm_apply_apply]
  exact oddAmbientSource_sign

theorem stateMiddle_ne_top :
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊤ := by
  change Subgroup.closure
    (Set.range ({CATALOGUE_MODULE}.stateGenerators 1)) ≠ ⊤
  intro htop
  have hmem : {CATALOGUE_MODULE}.ambient oddAmbient ∈
      Subgroup.closure
        (Set.range ({CATALOGUE_MODULE}.stateGenerators 1)) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hsign := middle_le_pairTopSign_ker hmem
  change pairTopSign ({CATALOGUE_MODULE}.ambient oddAmbient) = 1 at hsign
  exact oddAmbient_sign hsign

private theorem middleSourceGenerator_ne_one :
    {NORMAL_MODULE}.stateGenerators 1 middleGenerator ≠ 1 := by
  native_decide

theorem middleGenerator_ne_one :
    degreeTwoSixPairAction169CheckedLiteral.stateGenerators
      stateMiddle middleGenerator ≠ 1 := by
  intro h
  apply middleSourceGenerator_ne_one
  apply {CLASS_MODULE}.originalEquiv.injective
  simpa only [map_one] using h

theorem middleGenerator_mem :
    degreeTwoSixPairAction169CheckedLiteral.stateGenerators
        stateMiddle middleGenerator ∈
      (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex
        stateMiddle).1 := by
  exact Subgroup.subset_closure (Set.mem_range_self middleGenerator)

theorem stateMiddle_ne_bot :
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊥ := by
  intro hbot
  apply middleGenerator_ne_one
  apply Subgroup.mem_bot.mp
  rw [← hbot]
  exact middleGenerator_mem

end {NAMESPACE}

end
"""


def emit_chain(bounds_name: str) -> str:
    return f"""import SymmetricSubgroupAsymptotics.{BOUNDS_MODULE}
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: checked three-state normal chain

This module combines the literal sign bounds with the surjective checked
normal registry.  It exports only the reusable chain datum.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section

namespace {NAMESPACE}

open Non2UnipotentPrefixFiniteMenu

private theorem normal_eq_bot_or_middle_or_top
    (N : Subgroup Original) (hN : N.Normal) :
    N = ⊥ ∨
      N = (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex
        stateMiddle).1 ∨ N = ⊤ := by
  letI : N.Normal := hN
  obtain ⟨i, hi⟩ := {CATALOGUE_MODULE}.normal_complete N
  fin_cases i
  · have hiZero :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateZero).1 =
          N := by
      change Subgroup.closure
        (Set.range ({CATALOGUE_MODULE}.stateGenerators 0)) = N
      exact hi
    exact Or.inl (hiZero.symm.trans stateZero_eq_bot)
  · have hiMiddle :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex
          stateMiddle).1 = N := by
      change Subgroup.closure
        (Set.range ({CATALOGUE_MODULE}.stateGenerators 1)) = N
      exact hi
    exact Or.inr (Or.inl hiMiddle.symm)
  · have hiTop :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateTop).1 =
          N := by
      change Subgroup.closure
        (Set.range ({CATALOGUE_MODULE}.stateGenerators 2)) = N
      exact hi
    exact Or.inr (Or.inr (hiTop.symm.trans stateTop_eq_top))

noncomputable def chainData : FiniteThreeNormalChainData Original where
  middle :=
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateMiddle).1
  middle_normal := inferInstance
  middle_ne_bot := stateMiddle_ne_bot
  middle_ne_top := stateMiddle_ne_top
  normal_eq_bot_or_middle_or_top := normal_eq_bot_or_middle_or_top
  generator :=
    degreeTwoSixPairAction169CheckedLiteral.stateGenerators
      stateMiddle middleGenerator
  generator_mem := middleGenerator_mem
  generator_ne_one := middleGenerator_ne_one

end {NAMESPACE}

end
"""


def emit_pilot(chain_name: str) -> str:
    return f"""import SymmetricSubgroupAsymptotics.{CHAIN_MODULE}
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairThreeNormalChainRows

/-!
# Selected six-pair action 169: variable-state one-general pilot

The action-specific source ends at the checked three-normal-chain datum.
The common variable-state assembler supplies every literal quotient row.
-/

set_option autoImplicit false
noncomputable section

namespace {NAMESPACE}

open Non2UnipotentPrefixFiniteMenu

noncomputable def degreeTwoSixPairAction169ThreeNormalChainFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData where
  literal := degreeTwoSixPairAction169CheckedLiteral
  chain := chainData

noncomputable def degreeTwoSixPairAction169OneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toOneGeneralFiniteRowData

noncomputable def degreeTwoSixPairAction169CheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toCheckedLiteralQuotientAction hZmud

noncomputable def degreeTwoSixPairAction169B6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate degreeTwoSixPairAction169CheckedLiteral.G :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toB6ActionCertificate hZmud

end {NAMESPACE}

end
"""


def write_atomic(path: Path, text: str, force: bool) -> None:
    payload = text.encode()
    require(len(payload) <= OUTPUT_LIMIT,
            f"Lean output byte ceiling reached: {path.name}")
    require(force or not path.exists(), f"output exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "wb", delete=False, dir=path.parent,
        prefix=path.name + ".", suffix=".partial"
    ) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--class-input", required=True, type=Path)
    parser.add_argument("--normal-input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    class_chunk = read_chunk(args.class_input, "classes")
    normal_chunk = read_chunk(args.normal_input, "normals")
    prepared = validate_and_prepare(
        class_chunk, normal_chunk, read_pinned_data())
    outputs = [
        (args.output_dir / f"{BOUNDS_MODULE}.lean",
         emit_bounds(prepared, args.class_input.name, args.normal_input.name)),
        (args.output_dir / f"{CHAIN_MODULE}.lean",
         emit_chain(f"{BOUNDS_MODULE}.lean")),
        (args.output_dir / f"{PILOT_MODULE}.lean",
         emit_pilot(f"{CHAIN_MODULE}.lean")),
    ]
    require(args.force or all(not path.exists() for path, _ in outputs),
            "one or more action169 outputs exist; use --force")
    for path, text in outputs:
        write_atomic(path, text, args.force)
        print(path)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
