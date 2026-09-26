#!/usr/bin/env python3
"""Emit one small actual derived-group certificate, never a catalogue batch.

  python3 -B computations/python/export_lean_derived_group_words.py \
    --master 1082 --write --report /private/path/derived-order-1082.json
  python3 -B computations/python/export_lean_derived_group_words.py --master 1082 --check

The default searches and prints a compact summary without writing. --write
installs one canonical Lean source. --check compares exact bytes, performs no
writes, and cannot be combined with --report. Reports must be outside this
repository. The original source group and its normal menu are never enumerated:
only a bounded closure of explicit derived words is visited. Exhaustion is an
error, not a proof of coverage. All group claims require the emitted Lean check.

Resource limits are cooperative, with independent finite state/word/output caps;
the time budget is not a process-level RSS limit or hard preemption guarantee.
No compiler, GAP, external process, or network request is invoked.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse
from collections import deque
import hashlib
import json
import math
from pathlib import Path
import time

import export_lean_derived_square_words as square

ROOT = square.ROOT
OUT = square.OUT
MAX_ROWS = 64
MAX_OPERATIONS = 100_000
MAX_SECONDS = 5.0
MAX_BASIS = 16
MAX_WORD_NODES = 256
MAX_WORD_DEPTH = 16
MAX_ROW_WORD_LENGTH = 64
MAX_TOTAL_ROW_LETTERS = 4096
MAX_OUTPUT_BYTES = 262_144
require = square.require


def bounded_word(tag: str, *args: int | square.Word) -> square.Word:
    result = square.word(tag, *args)
    require(result.nodes <= MAX_WORD_NODES, "derived basis word node ceiling reached")
    require(result.depth <= MAX_WORD_DEPTH, "derived basis word depth ceiling reached")
    return result


def search(g: list[square.Perm], budget: square.Budget) -> dict:
    identity = tuple(range(16))
    basis: list[square.Perm] = []
    basis_words: list[square.Word] = []
    rows = [identity]
    row_words: list[list[int]] = [[]]
    indices = {identity: 0}

    def multiply(a: square.Perm, b: square.Perm) -> square.Perm:
        budget.operation()
        return square.mul(a, b)

    inverses = []
    for a in g:
        budget.operation()
        inverses.append(square.inv(a))

    def commutator(i: int, j: int) -> square.Perm:
        return multiply(multiply(multiply(g[i], g[j]), inverses[i]), inverses[j])

    def close() -> None:
        nonlocal rows, row_words, indices
        rows, row_words, indices = [identity], [[]], {identity: 0}
        queue = deque([0])
        total_letters = 0
        while queue:
            i = queue.popleft()
            for j, b in enumerate(basis):
                product = multiply(rows[i], b)
                if product in indices:
                    continue
                require(len(rows) < budget.max_states, "selected derived-row ceiling reached")
                length = len(row_words[i]) + 1
                require(length <= MAX_ROW_WORD_LENGTH, "positive row word length ceiling reached")
                total_letters += length
                require(total_letters <= MAX_TOTAL_ROW_LETTERS, "total row word letters ceiling reached")
                indices[product] = len(rows)
                rows.append(product)
                row_words.append(row_words[i] + [j])
                queue.append(len(rows) - 1)

    def add(permutation: square.Perm, tag: str, *args: int | square.Word) -> None:
        budget.time_check()
        if permutation in indices:
            return
        require(len(basis) < MAX_BASIS, "derived basis size ceiling reached")
        expression = bounded_word(tag, *args)
        basis.append(permutation)
        basis_words.append(expression)
        close()

    for i in range(len(g)):
        for j in range(len(g)):
            add(commutator(i, j), "comm", i, j)

    k = 0
    while k < len(basis):
        permutation, expression = basis[k], basis_words[k]
        for i, a in enumerate(g):
            add(multiply(multiply(a, permutation), inverses[i]), "conj", i, expression)
            add(multiply(multiply(inverses[i], permutation), a), "conjInv", i, expression)
        k += 1
    require(bool(basis), "selected derived group is trivial; this nonempty-basis template is inapplicable")

    # Account for the bounded syntax traversal and check every chosen basis value.
    for permutation, expression in zip(basis, basis_words):
        for _ in range(expression.nodes):
            budget.operation()
        require(square.evaluate(expression, g) == permutation,
                "derived basis word evaluation mismatch")
    for i, letters in enumerate(row_words):
        value = identity
        for j in letters:
            value = multiply(value, basis[j])
        require(value == rows[i], "positive derived-row word evaluation mismatch")

    def row_index(permutation: square.Perm) -> int:
        require(permutation in indices, "derived closure misses a required original equation")
        return indices[permutation]

    next_rows = [[row_index(multiply(row, b)) for b in basis] for row in rows]
    positive = [[row_index(multiply(multiply(a, b), inverses[i])) for b in basis]
                for i, a in enumerate(g)]
    commutators = [[row_index(commutator(i, j)) for j in range(len(g))]
                   for i in range(len(g))]
    noncentral = None
    for j, b in enumerate(basis):
        for i in range(len(g)):
            budget.operation()
            conjugated = rows[positive[i][j]]
            if conjugated == b:
                continue
            for point in range(16):
                budget.operation()
                if conjugated[point] != b[point]:
                    noncentral = {"basis": j, "original_generator": i, "point": point,
                                  "conjugated_value": conjugated[point], "basis_value": b[point]}
                    break
            require(noncentral is not None, "noncentrality point selection failed")
            break
        if noncentral is not None:
            break
    budget.time_check()
    return {"basis_words": basis_words, "rows": rows, "row_words": row_words,
            "next": next_rows, "positive": positive, "commutators": commutators,
            "noncentral_witness": noncentral}


def lean_vector(values: list[str], per_line: int, indent: str = "  ") -> str:
    require(bool(values), "empty literal vector is unsupported")
    groups = [", ".join(values[i:i + per_line]) for i in range(0, len(values), per_line)]
    return indent + "![" + (",\n" + indent + "  ").join(groups) + "]"


def lean_matrix(rows: list[list[int]], per_line: int) -> str:
    return lean_vector(["![" + ",".join(map(str, row)) + "]" for row in rows], per_line)


# The checked-pilot proof template is embedded below. It is not loaded from an
# existing output, so --check cannot accidentally accept an edited template.
TEMPLATE = r'''import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk@CHUNK@

/-! Selected @ROWS@-row certificate for the derived subgroup of the literal
16T@MASTER@ action. Displayed original derived words generate the candidate;
all transitions, conjugates and original commutators are checked on the
sixteen original points. No ambient-group enumeration is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T@MASTER@

abbrev Original :=
  Subgroup.closure (Set.range BinaryActionData16.node@MASTER@Generators)

def basisWords : Fin @BASIS@ → DerivedGeneratorWord (Fin @GENERATORS@) :=
@BASIS_WORDS@

private def ambientBasis (j : Fin @BASIS@) : Equiv.Perm (Fin 16) :=
  (basisWords j).eval BinaryActionData16.node@MASTER@Generators

private def rowWords (i : Fin @ROWS@) : List (Fin @BASIS@) :=
@ROW_WORDS@ i

def ambientRows (i : Fin @ROWS@) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientBasis).prod

private def elements (i : Fin @ROWS@) : Original :=
  ((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords)).prod

private theorem basis_coe (j : Fin @BASIS@) :
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords j :
      Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe BinaryActionData16.node@MASTER@Generators (basisWords j)

private theorem elements_coe (i : Fin @ROWS@) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords)).prod) = _
  have hf : Original.subtype ∘
      derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords = ambientBasis := by
    funext j
    exact basis_coe j
  rw [map_list_prod, List.map_map, hf]
  rfl

private def next (i : Fin @ROWS@) (j : Fin @BASIS@) : Fin @ROWS@ :=
@NEXT@ i j

private def conjugateRow (i : Fin @GENERATORS@) (j : Fin @BASIS@) : Fin @ROWS@ :=
@CONJUGATES@ i j

private def commutatorRow (i j : Fin @GENERATORS@) : Fin @ROWS@ :=
@COMMUTATORS@ i j

private theorem identity_pointwise : ∀ x : Fin 16, ambientRows 0 x = x := by
  decide +kernel

private theorem next_pointwise : ∀ (i : Fin @ROWS@) (j : Fin @BASIS@) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientBasis j) x := by
  decide +kernel

private theorem conjugate_pointwise : ∀ (i : Fin @GENERATORS@) (j : Fin @BASIS@) (x : Fin 16),
    ambientRows (conjugateRow i j) x =
      (BinaryActionData16.node@MASTER@Generators i * ambientBasis j *
        (BinaryActionData16.node@MASTER@Generators i)⁻¹) x := by
  decide +kernel

private theorem commutator_pointwise : ∀ (i j : Fin @GENERATORS@) (x : Fin 16),
    ambientRows (commutatorRow i j) x =
      ⁅BinaryActionData16.node@MASTER@Generators i,
        BinaryActionData16.node@MASTER@Generators j⁆ x := by
  decide +kernel

private theorem pointwise_rows_injective : ∀ i j : Fin @ROWS@,
    (∀ x : Fin 16, ambientRows i x = ambientRows j x) → i = j := by
  decide +kernel

private def cayley : FiniteCayleyCertificate
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords) @ROWS@ where
  elements := elements
  identity := 0
  identity_eq := by
    apply Subtype.ext
    change (elements 0 : Equiv.Perm (Fin 16)) = 1
    rw [elements_coe]
    exact Equiv.ext identity_pointwise
  next := next
  next_eq := by
    intro i j
    apply Subtype.ext
    change (elements (next i j) : Equiv.Perm (Fin 16)) =
      (elements i : Equiv.Perm (Fin 16)) *
        (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords j :
          Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, basis_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

/-- Every row equation is on the same original action and the same displayed
derived words. The generic consumer supplies all derived-group reasoning. -/
def certificate : DerivedWordFiniteCertificate
    BinaryActionData16.node@MASTER@Generators basisWords @ROWS@ where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he : (elements i : Equiv.Perm (Fin 16)) =
        (elements j : Equiv.Perm (Fin 16)) := congrArg Subtype.val h
    rw [elements_coe, elements_coe] at he
    exact pointwise_rows_injective i j (fun x => congrArg (fun f => f x) he)
  conjugateRow := conjugateRow
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements (conjugateRow i j) : Equiv.Perm (Fin 16)) =
      BinaryActionData16.node@MASTER@Generators i *
        (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords j :
          Equiv.Perm (Fin 16)) * (BinaryActionData16.node@MASTER@Generators i)⁻¹
    rw [elements_coe, basis_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  commutatorRow := commutatorRow
  commutator_eq := by
    intro i j
    apply Subtype.ext
    change (elements (commutatorRow i j) : Equiv.Perm (Fin 16)) =
      ⁅BinaryActionData16.node@MASTER@Generators i, BinaryActionData16.node@MASTER@Generators j⁆
    rw [elements_coe]
    exact Equiv.ext (commutator_pointwise i j)

/-- Public literal row binding for subsequent original-point centralizer checks. -/
theorem certificate_elements_coe (i : Fin @ROWS@) :
    (certificate.cayley.elements i : Equiv.Perm (Fin 16)) = ambientRows i :=
  elements_coe i

theorem card_commutator : Nat.card (commutator Original) = @ROWS@ :=
  certificate.card_commutator

private theorem noncentral_point :
    (BinaryActionData16.node@MASTER@Generators @WITNESS_GENERATOR@ * ambientBasis @WITNESS_BASIS@ *
      (BinaryActionData16.node@MASTER@Generators @WITNESS_GENERATOR@)⁻¹) (@WITNESS_POINT@ : Fin 16) ≠
        ambientBasis @WITNESS_BASIS@ (@WITNESS_POINT@ : Fin 16) := by
  decide +kernel

/-- A displayed original conjugation moves a displayed derived element.
This is whole-original-group noncentrality, not internal noncommutativity. -/
theorem commutator_not_le_center : ¬ commutator Original ≤ Subgroup.center Original := by
  intro h
  let d : Original := derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords @WITNESS_BASIS@
  let u : Original := closureGenerators BinaryActionData16.node@MASTER@Generators @WITNESS_GENERATOR@
  have hd : d ∈ commutator Original :=
    (basisWords @WITNESS_BASIS@).eval_mem_commutator (closureGenerators BinaryActionData16.node@MASTER@Generators)
  have he : u * d = d * u := Subgroup.mem_center_iff.mp (h hd) u
  have hc : u * d * u⁻¹ = d := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have hp := congrArg Subtype.val hc
  change BinaryActionData16.node@MASTER@Generators @WITNESS_GENERATOR@ *
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords @WITNESS_BASIS@ :
      Equiv.Perm (Fin 16)) * (BinaryActionData16.node@MASTER@Generators @WITNESS_GENERATOR@)⁻¹ =
    (derivedWordGenerators BinaryActionData16.node@MASTER@Generators basisWords @WITNESS_BASIS@ :
      Equiv.Perm (Fin 16)) at hp
  rw [basis_coe] at hp
  exact noncentral_point (congrArg (fun f : Equiv.Perm (Fin 16) => f @WITNESS_POINT@) hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T@MASTER@
'''


def emit(master: int, result: dict) -> bytes:
    chunk, order = square.SPECS[master]
    rows, words = result["rows"], result["basis_words"]
    replacements = {
        "@MASTER@": str(master), "@CHUNK@": f"{chunk:03d}",
        "@GENERATORS@": str(len(order)), "@BASIS@": str(len(words)), "@ROWS@": str(len(rows)),
        "@BASIS_WORDS@": lean_vector([square.lean_word(w) for w in words], 4),
        "@ROW_WORDS@": lean_vector(["[" + ",".join(map(str, w)) + "]"
                                    for w in result["row_words"]], 8),
        "@NEXT@": lean_matrix(result["next"], 4),
        "@CONJUGATES@": lean_matrix(result["positive"], 3),
        "@COMMUTATORS@": lean_matrix(result["commutators"], 3),
    }
    text = TEMPLATE
    if len(rows) == 64:
        text = text.replace(
            "import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate\n",
            "import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate\n"
            "import Mathlib.Tactic.FinCases\n", 1)
        # Keep each kernel decision local to one fixed first index. Elab.async
        # is disabled in the template, so these proof tasks remain sequential.
        for theorem in ("conjugate_pointwise", "commutator_pointwise"):
            start = text.index(f"private theorem {theorem} :")
            end = text.index("\n\n", start)
            block = text[start:end]
            suffix = "  decide +kernel"
            require(block.endswith(suffix), "unexpected finite-decision template")
            block = block[:-len(suffix)] + "  intro i\n  fin_cases i <;> decide +kernel"
            text = text[:start] + block + text[end:]
        # Separate declarations reset the default heartbeat budget for each
        # concrete row, unlike 64 branches inside one large declaration.
        for theorem in ("next_pointwise", "pointwise_rows_injective"):
            start = text.index(f"private theorem {theorem} :")
            end = text.index("\n\n", start)
            block = text[start:end]
            suffix = "  decide +kernel"
            require(block.endswith(suffix), "unexpected row-decision template")
            lemmas = []
            branches = []
            for i in range(len(rows)):
                name = f"{theorem}_row{i:03d}"
                if theorem == "next_pointwise":
                    statement = (
                        f"private theorem {name} : ∀ (j : Fin @BASIS@) (x : Fin 16),\n"
                        f"    ambientRows (next ({i} : Fin @ROWS@) j) x =\n"
                        f"      (ambientRows ({i} : Fin @ROWS@) * ambientBasis j) x := by\n")
                else:
                    statement = (
                        f"private theorem {name} : ∀ j : Fin @ROWS@,\n"
                        f"    (∀ x : Fin 16, ambientRows ({i} : Fin @ROWS@) x = ambientRows j x) →\n"
                        f"      ({i} : Fin @ROWS@) = j := by\n")
                lemmas.append(statement + "  decide +kernel")
                branches.append(f"  · exact {name}")
            assembly = (block[:-len(suffix)] + "  intro i\n  fin_cases i\n" +
                        "\n".join(branches))
            text = text[:start] + "\n\n".join(lemmas + [assembly]) + text[end:]
    witness = result["noncentral_witness"]
    marker = "private theorem noncentral_point :"
    if witness is None:
        text = text[:text.index(marker)] + (
            "end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T@MASTER@\n")
    else:
        replacements.update({"@WITNESS_BASIS@": str(witness["basis"]),
                             "@WITNESS_GENERATOR@": str(witness["original_generator"]),
                             "@WITNESS_POINT@": str(witness["point"])})
    for token, value in replacements.items():
        text = text.replace(token, value)
    require("@" not in text, "unexpanded Lean template token")
    content = text.encode("utf-8")
    require(len(content) <= MAX_OUTPUT_BYTES, "Lean output byte ceiling reached")
    return content


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--master", required=True, type=int, choices=square.SPECS)
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
        parser.error("immutable ceilings: 64 rows, 100000 operations, 5 seconds")
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
    for producer_path in (Path(__file__).resolve(), Path(square.__file__).resolve()):
        snapshots[producer_path] = square.bounded_read(producer_path)
    budget.time_check()
    result = search(generators, budget)
    content = emit(args.master, result)
    target = OUT / f"BinaryCarrierDerivedOrder16T{args.master}.lean"
    require(OUT.resolve().is_relative_to(ROOT) and not target.is_symlink(),
            "canonical output directory or file escapes publication")
    chunk, order = square.SPECS[args.master]
    summary = {
        "master": args.master, "rows": len(result["rows"]), "basis": len(result["basis_words"]),
        "operations": budget.operations, "seconds": time.monotonic() - budget.start,
        "module": str(target.relative_to(ROOT)), "module_sha256": hashlib.sha256(content).hexdigest(),
        "checked_bytes": args.check, "write_requested": args.write,
        "noncentral_witness": result["noncentral_witness"],
    }
    report_content = None
    if report_path is not None:
        report = {**summary, "chunk": chunk, "lean_to_original_generator_indices": list(order),
                  "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(b).hexdigest()
                                    for p, b in snapshots.items()},
                  "limits": {"rows": args.max_rows, "operations": args.max_operations,
                             "seconds": args.seconds, "basis": MAX_BASIS,
                             "basis_word_nodes": MAX_WORD_NODES, "basis_word_depth": MAX_WORD_DEPTH,
                             "row_word_length": MAX_ROW_WORD_LENGTH,
                             "total_row_word_letters": MAX_TOTAL_ROW_LETTERS,
                             "input_bytes": square.MAX_INPUT_BYTES, "output_bytes": MAX_OUTPUT_BYTES},
                  "basis_words": [square.json_word(x) for x in result["basis_words"]],
                  "lean_basis_words": [square.lean_word(x) for x in result["basis_words"]],
                  **{k: v for k, v in result.items() if k != "basis_words"},
                  "scope": "Untrusted selected derived-group words only; actual Lean checking remains required."}
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
        print(f"selected derived-group certificate: {error}", file=sys.stderr)
        raise SystemExit(2)
