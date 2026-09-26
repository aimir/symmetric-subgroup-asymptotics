#!/usr/bin/env python3
"""Emit one original-master centralizer/rank certificate, never a batch.

  python3 -B computations/python/export_lean_carrier_rank.py \
    --master 1082 --write --report /private/path/carrier-rank-1082.json
  python3 -B computations/python/export_lean_carrier_rank.py --master 1082 --check

The default searches and prints a summary without writing. --write installs
one canonical Lean source; --check compares exact bytes without writing and
cannot be combined with --report. Reports must be outside this repository.

The selected original JSON generators must match their literal Lean tuple.
The bounded derived-word search is reused, and its canonical derived-order
source must already exist with exactly the expected bytes. That prerequisite
is never written here. Only its at-most-64 derived rows are scanned against
one fixed original conjugator; the ambient group and its normals are not
enumerated. The emitted proof checks all commuting-row implications on the
original sixteen points with decide +kernel. Search is not a Lean proof.

Resource limits are cooperative, with independent state/word/output caps;
the time budget is not an RSS limit or hard preemption guarantee. No compiler,
external process, network request, or private search input is used.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse
import hashlib
import json
import math
from pathlib import Path
import time

import export_lean_derived_group_words as derived

square = derived.square
ROOT = square.ROOT
OUT = square.OUT
MAX_ROWS = 64
MAX_OPERATIONS = 100_000
MAX_SECONDS = 5.0
MAX_OUTPUT_BYTES = 262_144
require = square.require

# Positive words in the exact existing Lean generator tuple, not JSON order.
# Values are (conjugator word, centralizer cardinal cap, derived-normal rank cap).
SPECS = {
    1082: ((3,), 8, 3),
    1083: ((2,), 8, 3),
    1084: ((2,), 8, 3),
    1332: ((2,), 16, 4),
    1547: ((0, 3), 8, 3),
}


def centralizer_code(master: int, generators: list[square.Perm], rows: list[square.Perm],
                     budget: square.Budget) -> dict:
    """Recover every commuting row; no exact-centralizer-size claim is needed."""
    letters, cap, rank = SPECS[master]
    require(cap == 2 ** rank and cap > 0, "invalid fixed rank/cardinal cap")
    require(0 < len(rows) <= budget.max_states, "selected derived-row ceiling reached")
    require(rows[0] == tuple(range(16)), "derived row zero is not identity")
    require(len(set(rows)) == len(rows), "derived rows are duplicated")
    conjugator = tuple(range(16))
    for j in letters:
        require(0 <= j < len(generators), "fixed conjugator index is out of range")
        budget.operation()
        conjugator = square.mul(conjugator, generators[j])
    commuting = []
    for i, row in enumerate(rows):
        budget.operation()
        left = square.mul(row, conjugator)
        budget.operation()
        right = square.mul(conjugator, row)
        if left == right:
            commuting.append(i)
    require(bool(commuting) and commuting[0] == 0, "identity must commute")
    require(len(commuting) <= cap, "fixed centralizer cap is exceeded")
    select = commuting + [commuting[0]] * (cap - len(commuting))
    code = [0] * len(rows)
    for j, i in enumerate(commuting):
        code[i] = j
    for i in commuting:
        budget.operation()
        require(select[code[i]] == i, "commuting-row code does not recover its row")
    budget.time_check()
    return {"conjugator_word": list(letters), "conjugator": conjugator,
            "commuting_rows": commuting, "select": select, "code": code,
            "centralizer_cap": cap, "rank_cap": rank}


TEMPLATE = r'''import SymmetricSubgroupAsymptotics.DerivedWordCentralizerCertificate
import SymmetricSubgroupAsymptotics.PrimeNormalHeadCentralizer
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T@MASTER@

/-! A selected centralizer inside the actual derived subgroup bounds the
relative heads of all original normal subgroups in that derived subgroup.
The original conjugator uses Lean tuple indices @WORD@. The checked
derived-word certificate supplies every actual derived row; the finite
implication below covers every row commuting with that same conjugator.
No normal subgroup enumeration or ambient-group table is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRank16T@MASTER@

abbrev Original := BinaryCarrierDerivedOrder16T@MASTER@.Original

def conjugator : Original :=
  @CONJUGATOR@

private def ambientConjugator : Equiv.Perm (Fin 16) :=
  @AMBIENT_CONJUGATOR@

private theorem conjugator_coe :
    (conjugator : Equiv.Perm (Fin 16)) = ambientConjugator := rfl

private def select (j : Fin @CAP@) : Fin @ROWS@ :=
@SELECT@ j

private def code (i : Fin @ROWS@) : Fin @CAP@ :=
@CODE@ i

private theorem row_cover : ∀ i : Fin @ROWS@,
    (∀ x : Fin 16,
      BinaryCarrierDerivedOrder16T@MASTER@.ambientRows i (ambientConjugator x) =
        ambientConjugator (BinaryCarrierDerivedOrder16T@MASTER@.ambientRows i x)) →
    select (code i) = i := by
  decide +kernel

/-- This is the literal centralizer intersection inside the original action. -/
theorem centralizer_card_le :
    Nat.card ↥(commutator Original ⊓
      Subgroup.centralizer ({conjugator} : Set Original)) ≤ @CAP@ := by
  apply BinaryCarrierDerivedOrder16T@MASTER@.certificate.card_centralizer_le_of_pointwise_row_code
    conjugator select code
  intro i hi
  apply row_cover i
  intro x
  simpa only [BinaryCarrierDerivedOrder16T@MASTER@.certificate_elements_coe,
    conjugator_coe] using hi x

/-- The maximum includes every subgroup normal under the whole original group. -/
theorem derivedNormalRank_le : primeDerivedNormalRank 2 Original ≤ @RANK@ := by
  apply primeDerivedNormalRank_le_of_centralizer_card_le 2 conjugator @RANK@
  simpa only [show (2 : ℕ) ^ @RANK@ = @CAP@ from by decide] using centralizer_card_le

end SymmetricSubgroupAsymptotics.BinaryCarrierRank16T@MASTER@
'''


def emit(master: int, row_count: int, result: dict) -> bytes:
    letters, cap, rank = SPECS[master]
    require(result["conjugator_word"] == list(letters)
            and result["centralizer_cap"] == cap and result["rank_cap"] == rank,
            "selected centralizer specification changed")
    require(len(result["select"]) == cap and len(result["code"]) == row_count,
            "selected centralizer code size mismatch")
    require(all(type(i) is int and 0 <= i < row_count for i in result["select"])
            and all(type(j) is int and 0 <= j < cap for j in result["code"]),
            "selected centralizer code index out of range")
    lifted = [f"closureGenerators BinaryActionData16.node{master}Generators {j}" for j in letters]
    ambient = [f"BinaryActionData16.node{master}Generators {j}" for j in letters]
    replacements = {
        "@MASTER@": str(master), "@WORD@": str(list(letters)),
        "@CAP@": str(cap), "@RANK@": str(rank), "@ROWS@": str(row_count),
        "@CONJUGATOR@": " * ".join(lifted),
        "@AMBIENT_CONJUGATOR@": " * ".join(ambient),
        "@SELECT@": derived.lean_vector(list(map(str, result["select"])), 8),
        "@CODE@": derived.lean_vector(list(map(str, result["code"])), 8),
    }
    text = TEMPLATE
    for token, value in replacements.items():
        text = text.replace(token, value)
    require("@" not in text, "unexpanded Lean template token")
    content = text.encode("utf-8")
    require(len(content) <= MAX_OUTPUT_BYTES, "Lean output byte ceiling reached")
    return content


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--master", required=True, type=int, choices=SPECS)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--report", type=Path, help="optional private JSON, outside publication")
    parser.add_argument("--max-rows", type=int, default=MAX_ROWS)
    parser.add_argument("--max-operations", type=int, default=MAX_OPERATIONS)
    parser.add_argument("--seconds", type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    if not (1 <= args.max_rows <= MAX_ROWS and 1 <= args.max_operations <= MAX_OPERATIONS
            and math.isfinite(args.seconds) and 0 < args.seconds <= MAX_SECONDS):
        parser.error("immutable ceilings: 64 derived rows, 100000 operations, 5 seconds")
    if args.check and args.report is not None:
        parser.error("--check is strictly read-only and cannot be combined with --report")
    report_path = None
    if args.report is not None:
        require(not args.report.is_symlink(), "private report must not be a symlink")
        report_path = args.report.resolve()
        require(not report_path.is_relative_to(ROOT), "--report must be outside publication")
        require(report_path.suffix == ".json" and report_path.parent.is_dir(),
                "--report requires a .json path in an existing private directory")

    budget = square.Budget(args.max_rows, args.max_operations, args.seconds, time.monotonic())
    generators, snapshots = square.selected_generators(args.master)
    for producer_path in (Path(__file__).resolve(), Path(derived.__file__).resolve(),
                          Path(square.__file__).resolve()):
        snapshots[producer_path] = square.bounded_read(producer_path)
    budget.time_check()
    derived_result = derived.search(generators, budget)
    prerequisite = OUT / f"BinaryCarrierDerivedOrder16T{args.master}.lean"
    require(OUT.resolve().is_relative_to(ROOT) and not prerequisite.is_symlink(),
            "derived prerequisite path escapes publication")
    require(prerequisite.is_file(), f"selected derived prerequisite is missing: {prerequisite.name}")
    prerequisite_bytes = square.bounded_read(prerequisite)
    require(prerequisite_bytes == derived.emit(args.master, derived_result),
            f"selected derived prerequisite differs from its canonical producer: {prerequisite.name}")
    snapshots[prerequisite] = prerequisite_bytes
    result = centralizer_code(args.master, generators, derived_result["rows"], budget)
    content = emit(args.master, len(derived_result["rows"]), result)
    target = OUT / f"BinaryCarrierRank16T{args.master}.lean"
    require(not target.is_symlink(), "canonical output must not be a symlink")
    summary = {
        "master": args.master, "derived_rows": len(derived_result["rows"]),
        "commuting_rows": len(result["commuting_rows"]),
        "centralizer_cap": result["centralizer_cap"], "rank_cap": result["rank_cap"],
        "conjugator_word": result["conjugator_word"], "operations": budget.operations,
        "seconds": time.monotonic() - budget.start,
        "module": str(target.relative_to(ROOT)), "module_sha256": hashlib.sha256(content).hexdigest(),
        "prerequisite": str(prerequisite.relative_to(ROOT)),
        "prerequisite_sha256": hashlib.sha256(prerequisite_bytes).hexdigest(),
        "checked_bytes": args.check, "write_requested": args.write,
    }
    report_content = None
    if report_path is not None:
        chunk, order = square.SPECS[args.master]
        report = {**summary, "chunk": chunk, "lean_to_original_generator_indices": list(order),
                  "source_sha256": {str(source_path.relative_to(ROOT)):
                                    hashlib.sha256(source_bytes).hexdigest()
                                    for source_path, source_bytes in snapshots.items()},
                  "limits": {"rows": args.max_rows, "operations": args.max_operations,
                             "seconds": args.seconds, "basis": derived.MAX_BASIS,
                             "basis_word_nodes": derived.MAX_WORD_NODES,
                             "basis_word_depth": derived.MAX_WORD_DEPTH,
                             "row_word_length": derived.MAX_ROW_WORD_LENGTH,
                             "total_row_word_letters": derived.MAX_TOTAL_ROW_LETTERS,
                             "input_bytes": square.MAX_INPUT_BYTES, "output_bytes": MAX_OUTPUT_BYTES},
                  "certificate": result,
                  "scope": "Untrusted selected commuting-row code only; Lean checking remains required. "
                           "No normal catalogue or complete carrier-row coverage claim."}
        report_content = (json.dumps(report, indent=2) + "\n").encode("utf-8")
        require(len(report_content) <= MAX_OUTPUT_BYTES, "private report byte ceiling reached")
    for source_path, source_bytes in snapshots.items():
        require(square.bounded_read(source_path) == source_bytes, "input changed during production")
    budget.time_check()
    if args.check:
        require(target.is_file(), f"selected canonical Lean module is missing: {target.name}")
        require(square.bounded_read(target) == content, f"selected Lean bytes differ: {target.name}")
    elif args.write:
        if not target.is_file() or square.bounded_read(target) != content:
            square.atomic_write(target, content)
    if report_path is not None:
        square.atomic_write(report_path, report_content)
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (square.CertificateError, OSError, UnicodeError, RecursionError,
            json.JSONDecodeError) as error:
        print(f"selected carrier-rank certificate: {error}", file=sys.stderr)
        raise SystemExit(2)
