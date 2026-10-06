#!/usr/bin/env python3
"""Render the matrix representation and five invariant charts of one row.

The input is one selected prepared eight-frame certificate.  The renderer is
bounded, performs no directory scan, and invokes no subprocess.  Lean checks
the inverse matrices, Cayley transition law, reversible coordinates, and
stability under the literal top generators.
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


def lookup(values: list[str], variable: str = "i.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{lookup(values[:middle], variable, start)} else "
            f"{lookup(values[middle:], variable, start + middle)})")


def lean_array(values: list[int]) -> str:
    return "#[" + ",".join(map(str, values)) + "]"


def finite_checks(n: int) -> str:
    require(n >= 1, "empty finite check")
    if n <= 12:
        return "(by native_decide)"
    left = n // 2
    return (f"(Fin.addCases (m := {left}) (n := {n-left}) "
            f"{finite_checks(left)} {finite_checks(n-left)})")


def matrix_apply(columns: list[int], value: int) -> int:
    result = 0
    for j, column in enumerate(columns):
        if (value >> j) & 1:
            result ^= column
    return result


def matrix_mul(left: list[int], right: list[int]) -> list[int]:
    return [matrix_apply(left, column) for column in right]


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    module = value.get("module_certificate")
    require(isinstance(module, dict) and
            module.get("source_row") == value.get("source_row") and
            module.get("top_order") == value.get("top_order"),
            "module/top mismatch")
    forward = module.get("generator_matrices")
    inverse = module.get("inverse_generator_matrices")
    require(isinstance(forward, list) and len(forward) == 3 and
            isinstance(inverse, list) and len(inverse) == 3 and
            all(isinstance(row, list) and len(row) == 16 and
                all(type(x) is int and 0 <= x < 2**16 for x in row)
                for row in forward + inverse),
            "invalid generator matrix rows")
    modules = module.get("modules")
    duals = module.get("module_coordinate_masks")
    positive = module.get("module_generator_coordinates")
    negative = module.get("module_inverse_generator_coordinates")
    require(isinstance(modules, list) and len(modules) == 5 and
            isinstance(duals, list) and len(duals) == 5 and
            isinstance(positive, list) and len(positive) == 5 and
            isinstance(negative, list) and len(negative) == 5,
            "invalid module-state rows")
    for basis, dual, pos, neg in zip(modules, duals, positive, negative):
        d = len(basis)
        require(d <= 16 and len(dual) == d and len(pos) == len(neg) == 3 and
                all(type(x) is int and 0 <= x < 2**16 for x in basis + dual) and
                all(len(row) == d for row in pos + neg),
                "invalid module coordinate row")
    cayley = value.get("cayley")
    require(isinstance(cayley, dict), "missing Cayley rows")
    words = cayley.get("words")
    nxt = cayley.get("next")
    identity = cayley.get("identity")
    n = value["top_order"]
    require(isinstance(words, list) and len(words) == n and
            all(isinstance(word, list) and
                all(type(x) is int and 0 <= x < 3 for x in word)
                for word in words), "invalid Cayley words")
    require(isinstance(nxt, list) and len(nxt) == n and
            all(isinstance(row, list) and len(row) == 3 and
                all(type(x) is int and 0 <= x < n for x in row)
                for row in nxt), "invalid Cayley transition table")
    require(type(identity) is int and 0 <= identity < n,
            "invalid Cayley identity")
    one = [1 << i for i in range(16)]
    row_forward, row_inverse = [], []
    for word in words:
        fwd, inv = one, one
        for letter in word:
            fwd = matrix_mul(fwd, forward[letter])
            inv = matrix_mul(inverse[letter], inv)
        require(matrix_mul(fwd, inv) == one and
                matrix_mul(inv, fwd) == one,
                "computed Cayley-row matrix is not invertible")
        row_forward.append(fwd)
        row_inverse.append(inv)
    require(row_forward[identity] == one, "identity row matrix mismatch")
    for i in range(n):
        for j in range(3):
            require(row_forward[nxt[i][j]] ==
                    matrix_mul(row_forward[i], forward[j]),
                    "Cayley-row matrix transition mismatch")
    return {
        "source_row": value["source_row"],
        "top_order": value["top_order"],
        "forward": forward,
        "inverse": inverse,
        "modules": modules,
        "duals": duals,
        "dimensions": [len(row) for row in modules],
        "identity": identity,
        "row_forward": row_forward,
        "row_inverse": row_inverse,
    }


def emit(module_name: str, top_module: str, data: dict, input_name: str) -> str:
    forward = lookup([lean_array(row) for row in data["forward"]], "g.val")
    inverse = lookup([lean_array(row) for row in data["inverse"]], "g.val")
    row_forward = lookup([lean_array(row) for row in data["row_forward"]], "i.val")
    row_inverse = lookup([lean_array(row) for row in data["row_inverse"]], "i.val")
    text = f"""import SymmetricSubgroupAsymptotics.{top_module}
import SymmetricSubgroupAsymptotics.FiniteCayleyMatrixRepresentation
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry

/-!
# Selected eight-frame row {data['source_row']}: matrix module and invariant states

Generated by `emit_lean_frames8_selected_module_representation.py` from
`{input_name}`.  Lean checks the three matrix units, all Cayley transitions,
the five reversible coordinate charts, and positive/negative generator
stability.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.{module_name}

abbrev Source := {top_module}.Source
local instance sourceGroup : Group Source := {top_module}.group
abbrev ModelModule := Fin 16 → ZMod 2

private def forwardColumns (g : Fin 3) (j : Fin 16) : ℕ :=
  ({forward} : Array ℕ)[j.val]!

private def inverseColumns (g : Fin 3) (j : Fin 16) : ℕ :=
  ({inverse} : Array ℕ)[j.val]!

def forwardMatrix (g : Fin 3) : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  binaryMatrixOfColumnMasks 16 (forwardColumns g)

def inverseMatrix (g : Fin 3) : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  binaryMatrixOfColumnMasks 16 (inverseColumns g)

def images (g : Fin 3) : Units (Matrix (Fin 16) (Fin 16) (ZMod 2)) :=
  checkedMatrixUnit (forwardMatrix g) (inverseMatrix g)
    (by fin_cases g <;> native_decide)
    (by fin_cases g <;> native_decide)

private def rowForwardColumns (i : Fin {data['top_order']}) (j : Fin 16) : ℕ :=
  ({row_forward} : Array ℕ)[j.val]!

private def rowInverseColumns (i : Fin {data['top_order']}) (j : Fin 16) : ℕ :=
  ({row_inverse} : Array ℕ)[j.val]!

def rowForwardMatrix (i : Fin {data['top_order']}) :
    Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  binaryMatrixOfColumnMasks 16 (rowForwardColumns i)

def rowInverseMatrix (i : Fin {data['top_order']}) :
    Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  binaryMatrixOfColumnMasks 16 (rowInverseColumns i)

private theorem row_forward_inverse : ∀ i,
    rowForwardMatrix i * rowInverseMatrix i = 1 :=
  {finite_checks(data['top_order'])}

private theorem row_inverse_forward : ∀ i,
    rowInverseMatrix i * rowForwardMatrix i = 1 :=
  {finite_checks(data['top_order'])}

def rowUnits (i : Fin {data['top_order']}) :
    Units (Matrix (Fin 16) (Fin 16) (ZMod 2)) :=
  checkedMatrixUnit (rowForwardMatrix i) (rowInverseMatrix i)
    (row_forward_inverse i) (row_inverse_forward i)

private theorem matrix_step : ∀ i j,
    rowUnits ({top_module}.certificate.next i j) = rowUnits i * images j :=
  {finite_checks(data['top_order'])}

private theorem matrix_identity :
    rowUnits {top_module}.certificate.identity = 1 := by native_decide

/-- Literal sixteen-dimensional representation of the executable top. -/
def representation : Representation (ZMod 2) Source ModelModule :=
  matrixUnitRepresentation
    ({top_module}.certificate.checkedHom rowUnits images matrix_step
      {top_module}.rows_injective {top_module}.previousRow
      {top_module}.previous_checked matrix_identity)

@[simp] theorem representation_apply (g : Source) (v : ModelModule) :
    representation g v =
      ((rowUnits g.index : Units (Matrix (Fin 16) (Fin 16) (ZMod 2))) :
          Matrix (Fin 16) (Fin 16) (ZMod 2)).mulVec v := rfl

"""
    for i, (basis, dual) in enumerate(zip(data["modules"], data["duals"])):
        d = len(basis)
        basis_expr = lookup([str(x) for x in basis], "j.val") if basis else "0"
        dual_expr = lookup([str(x) for x in dual], "j.val") if dual else "0"
        text += f"""private def basis{i} (j : Fin {d}) : ℕ :=
  {basis_expr}

private def dual{i} (j : Fin {d}) : ℕ :=
  {dual_expr}

def chart{i} : BinaryCoordinateSpace 16 {d} :=
  binaryCoordinateSpaceOfMasks 16 {d} basis{i} dual{i} (by native_decide)

private theorem positive{i} : ∀ g j,
    representation ({top_module}.ambient g)
      (chart{i}.inclusion (Pi.single j 1)) ∈ chart{i}.space := by
  native_decide

private theorem negative{i} : ∀ g j,
    representation ({top_module}.ambient g)⁻¹
      (chart{i}.inclusion (Pi.single j 1)) ∈ chart{i}.space := by
  native_decide

def state{i} : Subrepresentation representation :=
  chart{i}.subrepresentationOfGenerators representation
    {top_module}.ambient {top_module}.ambient_full positive{i} negative{i}

"""
    state_values = [f"state{i}" for i in range(5)]
    chart_values = [f"⟨{d}, chart{i}⟩" for i, d in enumerate(data["dimensions"])]
    text += f"""def states (i : Fin 5) : Subrepresentation representation :=
  {lookup(state_values)}

def charts (i : Fin 5) : Σ d, BinaryCoordinateSpace 16 d :=
  {lookup(chart_values)}

theorem states_space (i : Fin 5) :
    (states i).toSubmodule = (charts i).2.space := by
  fin_cases i <;> rfl

theorem model_finrank_eq_sixteen :
    Module.finrank (ZMod 2) ModelModule = 16 := by simp

end SymmetricSubgroupAsymptotics.{module_name}

end
"""
    return text


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
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module")
    require(MODULE_RE.fullmatch(args.top_module) is not None, "invalid top module")
    data = read_input(args.input)
    payload = emit(args.module, args.top_module, data, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; dimensions {data['dimensions']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
