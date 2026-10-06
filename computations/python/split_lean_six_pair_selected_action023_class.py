#!/usr/bin/env python3
"""Split only the emitted action023 four-class certificate.

The older selected-class splitter is intentionally frozen around the
five-class action147 pilot.  This postprocessor accepts exactly the action023
module and separates its Cayley base, pair-top action, class invariant, four
centralizer rows, and final class-cover assembly.  It performs no catalogue
scan or mathematical computation and never invokes Lean or a subprocess.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import tempfile


INPUT_LIMIT = 256 * 1024
MODULE = "PrimitiveAffineDegreeTwoSixPairAction023ClassPilot"
PREFIX = "PrimitiveAffineDegreeTwoSixPairAction023"
CLASS_COUNT = 4


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def unique_index(text: str, needle: str) -> int:
    require(text.count(needle) == 1, f"expected one marker: {needle}")
    return text.index(needle)


def atomic_write(path: Path, text: str, force: bool) -> None:
    require(force or not path.exists(), f"output exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", delete=False, dir=path.parent,
        prefix=path.name + ".", suffix=".partial"
    ) as stream:
        temporary = Path(stream.name)
        stream.write(text)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def wrapper(title: str, imports: list[str], body: str) -> str:
    namespace = f"SymmetricSubgroupAsymptotics.{MODULE}"
    return (
        "\n".join(f"import {name}" for name in imports)
        + f"\n\n/-!\n# {title}\n\n"
        + "This is a resource-bounded split of the selected action-23 "
          "certificate.\nAll finite equations remain kernel checked.\n-/\n\n"
        + "set_option autoImplicit false\n"
          "set_option maxRecDepth 100000\n"
          "set_option maxHeartbeats 0\n"
          "noncomputable section\n\n"
        + f"namespace {namespace}\n\n{body.strip()}\n"
        + f"end {namespace}\n\nend\n"
    )


def split(input_path: Path, output_dir: Path, force: bool) -> list[Path]:
    require(input_path.is_file() and not input_path.is_symlink(),
            "missing or redirected action023 Lean input")
    raw = input_path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "action023 Lean input byte ceiling reached")
    text = raw.decode("utf-8")

    namespace_marker = f"namespace SymmetricSubgroupAsymptotics.{MODULE}"
    body_start = unique_index(text, namespace_marker) + len(namespace_marker)
    top_start = unique_index(text, "\nprivate def topRow0")
    class_start = unique_index(text, "\nprivate def representativeRows")
    centralizer_starts = [unique_index(text, f"\nnamespace C{i}\n")
                          for i in range(CLASS_COUNT)]
    centralizer_ends = [
        unique_index(text, f"\nend C{i}\n") + len(f"\nend C{i}\n")
        for i in range(CLASS_COUNT)
    ]
    assembly_start = unique_index(text, "\nnoncomputable def centralizer : ∀")
    body_end = unique_index(
        text, f"\nend SymmetricSubgroupAsymptotics.{MODULE}\n")

    require(body_start < top_start < class_start < centralizer_starts[0],
            "unexpected action023 certificate section order")
    for i in range(CLASS_COUNT - 1):
        require(centralizer_starts[i] < centralizer_ends[i] <=
                centralizer_starts[i + 1],
                "overlapping action023 centralizer sections")
    require(centralizer_starts[-1] < centralizer_ends[-1] <=
            assembly_start < body_end,
            "unexpected action023 certificate assembly order")

    base_body = text[body_start:top_start].replace(
        "local instance selectedSourceGroup : Group Source := group",
        "instance selectedSourceGroup : Group Source := group")
    pair_body = text[top_start:class_start]
    class_body = text[class_start:centralizer_starts[0]]
    centralizer_bodies = []
    for i in range(CLASS_COUNT):
        piece = text[centralizer_starts[i]:centralizer_ends[i]]
        piece = piece.replace("private def kernelRows (j : Fin 1)",
                              "private def kernelRows (_j : Fin 1)")
        piece = piece.replace(
            "  kernel_centralizes := by\n    intro j\n"
            "    apply Subgroup.mem_centralizer_singleton_iff.mpr\n"
            "    fin_cases j <;> decide +kernel",
            "  kernel_centralizes := by\n    intro j\n"
            "    apply Subgroup.mem_centralizer_singleton_iff.mpr\n"
            "    fin_cases j; decide +kernel")
        centralizer_bodies.append(piece)
    assembly_body = text[assembly_start:body_end]

    base_imports = [
        "SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks",
        "SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates",
        "SymmetricSubgroupAsymptotics.FinitePermutationEncoding",
        "Mathlib.Order.Fin.Basic",
        "Mathlib.Tactic.FinCases",
    ]
    pieces: list[tuple[str, str]] = [
        (f"{PREFIX}ClassBase.lean", wrapper(
            "Selected six-pair action 23: Cayley base", base_imports,
            base_body)),
        (f"{PREFIX}PairTop.lean", wrapper(
            "Selected six-pair action 23: pair-top action",
            [f"SymmetricSubgroupAsymptotics.{PREFIX}ClassBase",
             "Mathlib.Tactic.FinCases"], pair_body)),
        (f"{PREFIX}ClassInvariant.lean", wrapper(
            "Selected six-pair action 23: class invariant",
            [f"SymmetricSubgroupAsymptotics.{PREFIX}PairTop",
             "Mathlib.Tactic.FinCases"], class_body)),
    ]
    for i, body in enumerate(centralizer_bodies):
        pieces.append((f"{PREFIX}Centralizer{i}.lean", wrapper(
            f"Selected six-pair action 23: centralizer row {i}",
            [f"SymmetricSubgroupAsymptotics.{PREFIX}ClassInvariant",
             "Mathlib.Tactic.FinCases"], body)))
    pieces.append((f"{MODULE}.lean", wrapper(
        "Selected six-pair action 23: complete class cover",
        [f"SymmetricSubgroupAsymptotics.{PREFIX}Centralizer{i}"
         for i in range(CLASS_COUNT)], assembly_body)))

    outputs = []
    for name, payload in pieces:
        path = output_dir / name
        atomic_write(path, payload, force)
        outputs.append(path)
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(args.module == MODULE, f"module must be {MODULE}")
    for path in split(args.input, args.output_dir, args.force):
        print(path)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
