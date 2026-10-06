#!/usr/bin/env python3
"""Emit the literal-action adapter for one checked six-pair action.

The class and normal modules are generated and kernel-checked separately.
This narrow emitter only transports those certificates from their executable
row group to the literal twelve-point permutation subgroup, installs the
adjacent binary-pair frame, and packages the result as one
``PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction``.

Every input and the output are explicit.  There is no action range, directory
scan, bulk mode, subprocess, exporter invocation, or Lean invocation.
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
ACTION_COUNT = 182
INPUT_LIMIT = 256 * 1024
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 256 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_pinned_data() -> dict:
    require(DATA.is_file() and not DATA.is_symlink(),
            "missing or redirected six-block data")
    compressed = DATA.read_bytes()
    require(len(compressed) <= COMPRESSED_DATA_LIMIT,
            "compressed data ceiling reached")
    require(digest(compressed) == DATA_SHA256,
            "six-block data digest changed")
    raw = gzip.decompress(compressed)
    require(len(raw) <= DECOMPRESSED_DATA_LIMIT,
            "decompressed data ceiling reached")
    data = json.loads(raw)
    require(data.get("schema_version") == 1, "unexpected six-block schema")
    require(len(data.get("actions", [])) == ACTION_COUNT,
            "action count changed")
    return data


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
    require(value.get("stage") == stage, f"expected a {stage} chunk")
    return value


def selected_shape(action_number: int, class_chunk: dict,
                   normal_chunks: list[dict], data: dict) -> dict:
    require(1 <= action_number <= ACTION_COUNT,
            "selected action number out of range")
    require(class_chunk.get("action") == action_number,
            "class chunk action mismatch")
    require(normal_chunks and
            all(chunk.get("action") == action_number for chunk in normal_chunks),
            "normal chunk action mismatch")
    action = data["actions"][action_number - 1]
    order = action.get("order")
    ambient_count = len(action.get("generators", []))
    class_count = len(action.get("class_representatives", []))
    normals = action.get("normals", [])
    normal_count = len(normals)
    normal_width = max(1, max(len(normal.get("generators", []))
                              for normal in normals))
    require(type(order) is int and 2 <= order <= 46_080,
            "selected action order outside the narrow ceiling")
    require(1 <= ambient_count <= 16,
            "selected ambient width outside the narrow ceiling")
    require(1 <= class_count <= 128,
            "selected class count outside the narrow ceiling")
    require(1 <= normal_count <= 64,
            "selected normal count outside the narrow ceiling")
    require(1 <= normal_width <= 16,
            "selected normal generator width outside the narrow ceiling")
    require(class_chunk.get("action_order") == order,
            "class action order mismatch")
    require(class_chunk.get("range") == [1, class_count],
            "adapter requires the full selected class chunk")
    require(all(chunk.get("action_order") == order for chunk in normal_chunks),
            "normal action order mismatch")
    normal_indices = []
    for chunk in normal_chunks:
        content = chunk.get("content")
        require(isinstance(content, dict) and
                isinstance(content.get("rows"), list),
                "missing normal chunk rows")
        normal_indices.extend(row.get("normal_index") for row in content["rows"])
    require(sorted(normal_indices) == list(range(1, normal_count + 1)),
            "normal chunks are not a complete exact partition")
    return {
        "order": order,
        "ambient_count": ambient_count,
        "class_count": class_count,
        "normal_count": normal_count,
        "normal_width": normal_width,
    }


def emit_module(module: str, class_module: str, normal_module: str,
                action_number: int, shape: dict, input_names: list[str]) -> str:
    order = shape["order"]
    ambient_count = shape["ambient_count"]
    class_count = shape["class_count"]
    normal_count = shape["normal_count"]
    normal_width = shape["normal_width"]
    checked_name = f"degreeTwoSixPairAction{action_number:03d}CheckedLiteral"
    return f"""import SymmetricSubgroupAsymptotics.{normal_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSelectedWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinateTransport
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistryTransport

/-!
# Selected six-pair action {action_number}: literal checked action

Generated by `emit_lean_six_pair_selected_action_adapter.py` from the explicit
selected inputs `{', '.join(input_names)}` and the pinned six-block source
digest `{DATA_SHA256}`.  This module transports the separately checked row,
class, centralizer and normal-registry certificates to the literal subgroup
of `S_12` and records the actual adjacent-pair block system.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module}

local instance selectedSourceGroup : Group {class_module}.Source :=
  {class_module}.group

abbrev Original : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range {class_module}.generators)

def frame : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6))
    (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private theorem frame_checked : ∀ i : Fin {order}, ∀ p : Fin 6 × ZMod 2,
    (frame.symm
      (finFunctionFinEquiv.symm ({class_module}.certificate.rows i)
        (frame p))).1 =
      {class_module}.pairTop (⟨i⟩ : {class_module}.Source) p.1 := by
  native_decide

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofEquiv {class_module}.originalEquiv
    {class_module}.pairTop frame (by
      intro u p
      change (frame.symm
        ({class_module}.certificate.toCayley.elements u.index (frame p))).1 =
          {class_module}.pairTop u p.1
      rw [binaryPair_source_row_apply]
      exact frame_checked u.index p)

def ambient (j : Fin {ambient_count}) : Original :=
  {class_module}.originalEquiv ({class_module}.ambient j)

def representative (i : Fin {class_count}) : Original :=
  {class_module}.originalEquiv ({class_module}.representative i)

def stateGenerators (i : Fin {normal_count}) (j : Fin {normal_width}) : Original :=
  {class_module}.originalEquiv ({normal_module}.stateGenerators i j)

noncomputable def conjugacy :
    FiniteConjugacyCentralizerCoordinateChunk representative 6 :=
  {class_module}.conjugacyChunk.mapEquiv {class_module}.originalEquiv

noncomputable def normalRegistry : FiniteNormalJoinWordRegistryData
    conjugacy.toCardinalCover ambient stateGenerators :=
  {normal_module}.normalRegistry.mapEquiv {class_module}.originalEquiv
    conjugacy.toCardinalCover

private theorem row_centralizer_top (i : Fin {class_count}) :
    ({class_module}.conjugacyChunk.centralizer i).top =
      {class_module}.pairTop.comp
        (Subgroup.centralizer
          ({{{class_module}.representative i}} :
            Set {class_module}.Source)).subtype := by
  fin_cases i <;> rfl

private theorem centralizer_top (i : Fin {class_count}) :
    (conjugacy.centralizer i).top =
      pairFrame.top.comp
        (Subgroup.centralizer
          ({{representative i}} : Set Original)).subtype := by
  apply MonoidHom.ext
  intro x
  simp only [conjugacy,
    FiniteConjugacyCentralizerCoordinateChunk.mapEquiv,
    FinitePairCentralizerCoordinateCertificate.mapCentralizerEquiv,
    pairFrame, BinaryPairFrame.ofEquiv, representative,
    centralizerSingletonMulEquiv]
  rw [row_centralizer_top]
  rfl

noncomputable def selectedWitness :
    PrimitiveAffineDegreeTwoSixPairSelectedWitness
      Original ambient representative stateGenerators where
  pairFrame := pairFrame
  conjugacy := conjugacy
  centralizer_top := centralizer_top
  normalRegistry := normalRegistry

theorem normal_complete (N : Subgroup Original) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  selectedWitness.normal_complete N

end SymmetricSubgroupAsymptotics.{module}

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The completed structural part of selected catalogue action
{action_number}. -/
noncomputable def {checked_name} :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction where
  G := {module}.Original
  ambientCount := {ambient_count}
  classCount := {class_count}
  normalCount := {normal_count}
  normalGeneratorWidth := {normal_width}
  ambient := {module}.ambient
  representative := {module}.representative
  stateGenerators := {module}.stateGenerators
  checked := {module}.selectedWitness

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
"""


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
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
    parser.add_argument("--action", required=True, type=int)
    parser.add_argument("--class-input", required=True, type=Path)
    parser.add_argument("--normal-input", required=True, action="append", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--class-module", required=True)
    parser.add_argument("--normal-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.class_module, args.normal_module):
        require(MODULE_RE.fullmatch(name) is not None,
                "invalid Lean module name")
    require(len(set(args.normal_input)) == len(args.normal_input),
            "duplicate normal input")
    class_chunk = read_chunk(args.class_input, "classes")
    normal_chunks = [read_chunk(path, "normals") for path in args.normal_input]
    shape = selected_shape(args.action, class_chunk, normal_chunks,
                           read_pinned_data())
    input_names = [args.class_input.name] + [path.name for path in args.normal_input]
    payload = emit_module(args.module, args.class_module, args.normal_module,
                          args.action, shape, input_names).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action {args.action}; "
          f"order {shape['order']}; classes {shape['class_count']}; "
          f"normal states {shape['normal_count']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
