#!/usr/bin/env python3
"""Render the shared Lean assembly for one grouped eight-frame top.

The inputs are the checked prepared row certificates for a single literal
transitive top.  Top, stabilizer, normal-lattice, and transport proofs are
shared; this renderer only binds the generated declarations and emits the one
public table theorem used by every row in the group.  Lean checks the output.
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


def read(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected prepared row {path}")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared row ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            f"unexpected prepared-row schema in {path}")
    return value


def write_atomic(path: Path, text: str, force: bool) -> None:
    payload = text.encode()
    require(len(payload) <= OUTPUT_LIMIT, "generated Lean source too large")
    require(force or not path.exists(), f"output exists: {path}; use --force")
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


def row_prefix(row: int) -> str:
    return f"PrimitiveAffineEightFrameRow{row}"


def emit_data(top_id: int, rows: list[dict]) -> str:
    first = rows[0]
    source_rows = [value["source_row"] for value in rows]
    representative = source_rows[0]
    top_prefix = f"PrimitiveAffineEightFrameTop{top_id}"
    module = top_prefix + "GeneratedData"
    rep_induced = row_prefix(representative) + "InducedBinding"
    imports = [
        "import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable",
        f"import SymmetricSubgroupAsymptotics.{top_prefix}TopRegistry",
    ]
    for row in source_rows:
        prefix = row_prefix(row)
        imports.extend([
            f"import SymmetricSubgroupAsymptotics.{prefix}InducedBinding",
            f"import SymmetricSubgroupAsymptotics.{prefix}ModuleRegistry",
        ])
    row_list = ", ".join(map(str, source_rows))
    text = "\n".join(imports) + f"""

/-!
# Shared generated data for eight-frame top {top_id}

Rows {row_list} share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace {module}

abbrev Source := {top_prefix}TopCertificate.Source
local instance sourceGroup : Group Source :=
  {top_prefix}TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range {top_prefix}TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  {rep_induced}.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable ({rep_induced}.inStabilizer x.index)
  unfold {rep_induced}.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      (((({top_prefix}TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change {rep_induced}.inStabilizer x.index ↔ _
  simp only [{top_prefix}TopCertificate.originalEquiv_apply]
  unfold {rep_induced}.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction {top_prefix}TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := {top_prefix}TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction {top_prefix}TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin {len(first['generators'])}
  ambient := {top_prefix}TopCertificate.ambient
  ambient_full := {top_prefix}TopCertificate.ambient_full
  representative := {rep_induced}.representative
  representative_factor := {rep_induced}.representative_factor
  next := {rep_induced}.next
  twist := {rep_induced}.twist
  representative_mul_generator := {rep_induced}.representative_mul_generator
  classCount := {len(first['class_representatives'])}
  conjugacyRepresentative := {top_prefix}TopCertificate.representative
  conjugacyCover := {top_prefix}TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin {len(first['normal_generators'])}
  NormalGeneratorIndex := Fin {first['normal_generator_width']}
  stateGenerators := {top_prefix}NormalCertificate.stateGenerators
  topRegistry := {top_prefix}TopRegistry.registry

"""
    for value in rows:
        row = value["source_row"]
        prefix = row_prefix(row)
        induced = prefix + "InducedBinding"
        order = value["module_certificate"]["local_quotient_order"]
        require(order in (3, 6), f"invalid local quotient order in row {row}")
        side = "Or.inl" if order == 3 else "Or.inr"
        text += f"""noncomputable def row{row}Data : GeneratedRowData topData where
  LocalTarget := {induced}.LocalTarget
  sourceLocalMap := {induced}.sourceLocalMap
  sourceLocalMap_surjective := {induced}.sourceLocalMap_surjective
  local_card := {side} {induced}.localTarget_card
  localRepresentation := {induced}.localRepresentation
  localRepresentation_injective := {induced}.localRepresentation_injective
  modelRepresentation := {prefix}ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    {induced}.representation_generator_formula
  moduleRegistry := {prefix}ModuleRegistry.registry

"""
    text += f"""end {module}
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
"""
    return text


def emit_table(top_id: int, rows: list[dict]) -> str:
    source_rows = [value["source_row"] for value in rows]
    top_prefix = f"PrimitiveAffineEightFrameTop{top_id}"
    data_module = top_prefix + "GeneratedData"
    normal_module = top_prefix + "LocalNormalTable"
    module = top_prefix + "GeneratedTable"
    row_list = ", ".join(map(str, source_rows))
    return f"""import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.{normal_module}

/-!
# Rows {row_list} through one generated top table

The rows share their Cayley model, point stabilizer, conjugacy cover and
complete normal-subgroup catalogue.  The local quotient is selected by the
checked table before the generic induced-module transport is applied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace {module}

abbrev topData := {data_module}.topData

variable {{w : ℕ}} {{U : PreE7NonPairActionClass w}}
  {{basePoint : Fin w}}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The complete finite-frame bound for every row over this literal top. -/
noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        topData.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
  GeneratedTopTable.bounds block P topData {normal_module}.table
    pointEquiv conjugator hconjugated hr hD hs

end {module}
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--top-id", required=True, type=int)
    parser.add_argument("--row-input", required=True, action="append", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(1 <= args.top_id <= 10_000, "invalid top id")
    rows = [read(path) for path in args.row_input]
    require(rows, "no grouped row inputs")
    top_index = rows[0].get("top_index")
    top_order = rows[0].get("top_order")
    require(all(value.get("top_index") == top_index and
                value.get("top_order") == top_order for value in rows),
            "grouped rows do not share one top")
    source_rows = [value.get("source_row") for value in rows]
    require(all(type(row) is int and row >= 0 for row in source_rows) and
            len(set(source_rows)) == len(source_rows),
            "invalid or repeated source rows")
    top_prefix = f"PrimitiveAffineEightFrameTop{args.top_id}"
    for suffix, text in (
        ("GeneratedData", emit_data(args.top_id, rows)),
        ("GeneratedTable", emit_table(args.top_id, rows)),
    ):
        module = top_prefix + suffix
        require(MODULE_RE.fullmatch(module) is not None, "invalid module name")
        output = args.output_dir / f"{module}.lean"
        write_atomic(output, text, args.force)
        print(f"{output}: {len(text.encode())} bytes; rows {source_rows}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
