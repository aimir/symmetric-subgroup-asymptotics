#!/usr/bin/env python3
"""Emit the one-general quotient pilot for selected six-pair action 147.

This is deliberately not a catalogue emitter.  It accepts exactly action
147, one complete selected class chunk, and one complete selected normal
chunk.  There is no range, chunk, directory-scan, or all-actions mode, and it
never invokes Lean, a subprocess, or another exporter.

The JSON and pinned dataset are used only to refuse the wrong pilot inputs.
The emitted Lean module does not import their declarations as hypotheses:
it proves the bottom and top normal-state equations in the checked literal
action, obtains the two-point normal lattice from ``normal_complete``, and
derives the two ``SocleNormalGeneratorBound`` values in the kernel.
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
CLASS_INPUT_SHA256 = (
    "8453a4f31a8180b83a4211ce5b2a3391a28aa9da0b1f07f5265d706bc829d632"
)
NORMAL_INPUT_SHA256 = (
    "707e908355ba73475bf880098131625550c01a4dcd636480cc4b396463e38e8e"
)
ACTION = 147
ACTION_COUNT = 182
ACTION_ORDER = 60
AMBIENT_COUNT = 2
CLASS_COUNT = 5
NORMAL_COUNT = 2
CLASS_RANGE = [1, 5]
NORMAL_RANGE = [1, 2]
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
INPUT_LIMIT = 256 * 1024
OUTPUT_LIMIT = 64 * 1024
EXPECTED_MODULE = "PrimitiveAffineDegreeTwoSixPairAction147OneGeneralPilot"
EXPECTED_ACTION_MODULE = "PrimitiveAffineDegreeTwoSixPairAction147CatalogueRow"
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


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


def read_selected_chunk(path: Path, stage: str, expected_sha256: str) -> dict:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected {stage} input")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, f"{stage} input ceiling reached")
    require(digest(raw) == expected_sha256,
            f"action147 {stage} pilot input digest changed")
    value = json.loads(raw)
    require(isinstance(value, dict), f"{stage} input is not an object")
    require(value.get("schema_version") == 1,
            f"unexpected {stage} input schema")
    require(value.get("source_sha256") == DATA_SHA256,
            f"{stage} source digest changed")
    require(value.get("action") == ACTION,
            f"{stage} input is not action147")
    require(value.get("stage") == stage,
            f"expected a {stage} selected chunk")
    require(value.get("chunk") == 0,
            f"action147 {stage} pilot requires chunk zero")
    require(value.get("action_order") == ACTION_ORDER,
            f"action147 {stage} action order changed")
    require(value.get("ambient_generator_count") == AMBIENT_COUNT,
            f"action147 {stage} ambient width changed")
    return value


def validate_selected_inputs(class_chunk: dict, normal_chunk: dict,
                             data: dict) -> None:
    require(class_chunk.get("range") == CLASS_RANGE,
            "action147 pilot requires the complete class chunk")
    require(normal_chunk.get("range") == NORMAL_RANGE,
            "action147 pilot requires the complete normal chunk")
    class_content = class_chunk.get("content")
    normal_content = normal_chunk.get("content")
    require(isinstance(class_content, dict) and
            isinstance(class_content.get("rows"), list),
            "missing action147 class rows")
    require(isinstance(normal_content, dict) and
            isinstance(normal_content.get("rows"), list),
            "missing action147 normal rows")
    require([row.get("class_index") for row in class_content["rows"]] ==
            list(range(1, CLASS_COUNT + 1)),
            "action147 class rows are not the complete ordered range")
    require([row.get("normal_index") for row in normal_content["rows"]] ==
            list(range(1, NORMAL_COUNT + 1)),
            "action147 normal rows are not the complete ordered range")

    action = data["actions"][ACTION - 1]
    require(action.get("order") == ACTION_ORDER,
            "pinned action147 order changed")
    require(len(action.get("generators", [])) == AMBIENT_COUNT,
            "pinned action147 ambient width changed")
    require(len(action.get("class_representatives", [])) == CLASS_COUNT,
            "pinned action147 class count changed")
    normals = action.get("normals")
    require(isinstance(normals, list) and len(normals) == NORMAL_COUNT,
            "pinned action147 normal count changed")

    # These fields select the intended pilot rows only.  They never occur in
    # the emitted proof term: Lean recovers bottom/top from literal generator
    # equations and the already checked normal registry.
    require(normals[0].get("generators") == [] and
            normals[0].get("order") == 1 and
            normals[0].get("kind") == "characters" and
            normals[0].get("characters") == [1],
            "pinned action147 bottom character row changed")
    require(normals[1].get("generators") == action["generators"][::-1] and
            normals[1].get("order") == ACTION_ORDER and
            normals[1].get("kind") == "characters" and
            normals[1].get("characters") == [],
            "pinned action147 top character row changed")
    require(action.get("character_kernels") ==
            [[1, 3], [1, 4], [1, 5], [2, 1]],
            "pinned action147 character-kernel shape changed")


def emit_module(module: str, action_module: str,
                class_input_name: str, normal_input_name: str) -> str:
    return f"""import SymmetricSubgroupAsymptotics.{action_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralRows
import SymmetricSubgroupAsymptotics.FiniteTwoNormalSocleGenerators
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: one-general quotient pilot

Generated by `emit_lean_six_pair_selected_one_general_pilot.py` from the
explicit selected inputs `{class_input_name}` and `{normal_input_name}`.
Both inputs point to the pinned six-block source digest `{DATA_SHA256}`.

The JSON character and order fields are not proof premises.  The proofs
below use the checked literal action, kernel-checked generator equations,
and the surjective normal registry.  State zero is the bottom subgroup;
state one is the top subgroup; hence the two quotients are simple and
trivial respectively.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.{module}

open Non2UnipotentPrefixFiniteMenu

private abbrev Original := {action_module}.Original

private def stateZero :
    Fin degreeTwoSixPairAction147CheckedLiteral.normalCount :=
  ⟨0, by change 0 < 2; norm_num⟩

private def stateOne :
    Fin degreeTwoSixPairAction147CheckedLiteral.normalCount :=
  ⟨1, by change 1 < 2; norm_num⟩

private def genZero :
    Fin degreeTwoSixPairAction147CheckedLiteral.normalGeneratorWidth :=
  ⟨0, by change 0 < 2; norm_num⟩

private def genOne :
    Fin degreeTwoSixPairAction147CheckedLiteral.normalGeneratorWidth :=
  ⟨1, by change 1 < 2; norm_num⟩

private theorem state_zero_eq_bot :
    (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateZero).1 =
      ⊥ := by
  change Subgroup.closure
    (Set.range ({action_module}.stateGenerators 0)) = ⊥
  exact {action_module}.normalRegistry.bottom_eq

private theorem state_one_generator_zero :
    degreeTwoSixPairAction147CheckedLiteral.stateGenerators stateOne genZero =
      {action_module}.ambient 1 := by
  change PrimitiveAffineDegreeTwoSixPairAction147CatalogueRow.stateGenerators 1 0 =
    PrimitiveAffineDegreeTwoSixPairAction147CatalogueRow.ambient 1
  exact congrArg PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.originalEquiv
    (by native_decide)

private theorem state_one_generator_one :
    degreeTwoSixPairAction147CheckedLiteral.stateGenerators stateOne genOne =
      {action_module}.ambient 0 := by
  change PrimitiveAffineDegreeTwoSixPairAction147CatalogueRow.stateGenerators 1 1 =
    PrimitiveAffineDegreeTwoSixPairAction147CatalogueRow.ambient 0
  exact congrArg PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.originalEquiv
    (by native_decide)

private theorem state_one_generator_range :
    Set.range
      (degreeTwoSixPairAction147CheckedLiteral.stateGenerators stateOne) =
      Set.range {action_module}.ambient := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact ⟨1, state_one_generator_zero.symm⟩
    · exact ⟨0, state_one_generator_one.symm⟩
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact ⟨genOne, state_one_generator_one⟩
    · exact ⟨genZero, state_one_generator_zero⟩

private theorem state_one_eq_top :
    (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateOne).1 =
      ⊤ := by
  change Subgroup.closure
    (Set.range
      (degreeTwoSixPairAction147CheckedLiteral.stateGenerators stateOne)) = ⊤
  rw [state_one_generator_range]
  exact {action_module}.normalRegistry.ambient_full

private theorem original_card : Nat.card Original = 60 := by
  calc
    Nat.card Original =
        Nat.card PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.Source :=
      Nat.card_congr
        PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.originalEquiv.symm.toEquiv
    _ = 60 := PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.source_card

private noncomputable instance original_nontrivial : Nontrivial Original :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    rw [original_card]
    norm_num)

/-- The checked two-state normal registry proves simplicity of the literal
action without an identification with `A5`. -/
private noncomputable instance original_isSimpleGroup :
    IsSimpleGroup Original where
  toNontrivial := original_nontrivial
  eq_bot_or_eq_top_of_normal N hN := by
    letI : N.Normal := hN
    obtain ⟨i, hi⟩ := {action_module}.normal_complete N
    fin_cases i
    · have hiZero :
          (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateZero).1 =
            N := by
        change Subgroup.closure
          (Set.range ({action_module}.stateGenerators 0)) = N
        exact hi
      exact Or.inl (hiZero.symm.trans state_zero_eq_bot)
    · have hiOne :
          (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateOne).1 =
            N := by
        change Subgroup.closure
          (Set.range ({action_module}.stateGenerators 1)) = N
        exact hi
      exact Or.inr (hiOne.symm.trans state_one_eq_top)

private noncomputable def state_zero_quotient_equiv :
    (degreeTwoSixPairAction147CheckedLiteral.G ⧸
      (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateZero).1) ≃*
        Original :=
  (QuotientGroup.quotientMulEquivOfEq state_zero_eq_bot).trans
    QuotientGroup.quotientBot

/-- The bottom-state quotient inherits the checked two-normal-state
simplicity and therefore needs one socle normal generator. -/
noncomputable def state_zero_socleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction147CheckedLiteral.G ⧸
        (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateZero).1) 1 := by
  letI : IsSimpleGroup
      (degreeTwoSixPairAction147CheckedLiteral.G ⧸
        (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateZero).1) :=
    state_zero_quotient_equiv.isSimpleGroup
  exact socleNormalGeneratorBound_one_of_isSimpleGroup _

private noncomputable instance state_one_quotient_subsingleton :
    Subsingleton
      (degreeTwoSixPairAction147CheckedLiteral.G ⧸
        (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateOne).1) := by
  letI : Subsingleton
      (degreeTwoSixPairAction147CheckedLiteral.G ⧸
        (⊤ : Subgroup degreeTwoSixPairAction147CheckedLiteral.G)) :=
    QuotientGroup.subsingleton_quotient_top
  exact
    (QuotientGroup.quotientMulEquivOfEq state_one_eq_top).toEquiv.subsingleton

/-- The top-state quotient is trivial, so its padded one-position socle
witness is the identity. -/
noncomputable def state_one_socleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction147CheckedLiteral.G ⧸
        (degreeTwoSixPairAction147CheckedLiteral.normalStateIndex stateOne).1) 1 :=
  socleNormalGeneratorBound_one_of_subsingleton _

/-- Both checked normal states assembled into the reusable literal finite
row consumed by the character and B6 dispatchers. -/
noncomputable def degreeTwoSixPairAction147OneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData where
  literal := degreeTwoSixPairAction147CheckedLiteral
  socleGenerator i := by
    fin_cases i
    · simpa [stateZero] using state_zero_socleGenerator
    · simpa [stateOne] using state_one_socleGenerator

/-- The complete literal quotient package after applying the published
Zmud input. -/
noncomputable def degreeTwoSixPairAction147CheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  degreeTwoSixPairAction147OneGeneralFiniteRowData
    |>.toCheckedLiteralQuotientAction hZmud

/-- The action-147 B6 certificate on the same literal degree-twelve action. -/
noncomputable def degreeTwoSixPairAction147B6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate degreeTwoSixPairAction147CheckedLiteral.G :=
  degreeTwoSixPairAction147OneGeneralFiniteRowData
    |>.toB6ActionCertificate hZmud

end SymmetricSubgroupAsymptotics.{module}

end
"""


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
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
    parser.add_argument("--action", required=True, type=int)
    parser.add_argument("--class-input", required=True, type=Path)
    parser.add_argument("--normal-input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--action-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    require(args.action == ACTION,
            "this pilot emitter accepts only --action 147")
    require(MODULE_RE.fullmatch(args.module) is not None,
            "invalid Lean module name")
    require(MODULE_RE.fullmatch(args.action_module) is not None,
            "invalid action module name")
    require(args.module == EXPECTED_MODULE,
            f"pilot module must be {EXPECTED_MODULE}")
    require(args.action_module == EXPECTED_ACTION_MODULE,
            f"action module must be {EXPECTED_ACTION_MODULE}")
    require(args.output.name == EXPECTED_MODULE + ".lean",
            "unexpected pilot output filename")

    class_chunk = read_selected_chunk(
        args.class_input, "classes", CLASS_INPUT_SHA256)
    normal_chunk = read_selected_chunk(
        args.normal_input, "normals", NORMAL_INPUT_SHA256)
    validate_selected_inputs(class_chunk, normal_chunk, read_pinned_data())
    payload = emit_module(
        args.module, args.action_module,
        args.class_input.name, args.normal_input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action 147; "
          "normal states 2; one-general pilot")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, EOFError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
