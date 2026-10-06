#!/usr/bin/env python3
"""Split one emitted six-pair class certificate into bounded Lean modules.

The input is one file produced by ``emit_lean_six_pair_selected_class_pilot.py``.
This postprocessor performs no dataset scan and no mathematical computation;
it only separates the Cayley base, pair-top action, class invariant, and each
centralizer row so that Lean can check them under the workspace resource cap.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import tempfile


INPUT_LIMIT = 2 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
SELECTED_MODULE_RE = re.compile(
    r"PrimitiveAffineDegreeTwoSixPairAction([0-9]+)ClassPilot\Z")


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


def wrapper(module: str, title: str, imports: list[str], body: str,
            action_number: int) -> str:
    namespace = f"SymmetricSubgroupAsymptotics.{module}"
    return (
        "\n".join(f"import {name}" for name in imports)
        + f"\n\n/-!\n# {title}\n\n"
        + f"This is a resource-bounded split of the selected action-{action_number} "
          "certificate.\nAll finite equations remain kernel checked.\n-/\n\n"
        + "set_option autoImplicit false\n"
          "set_option maxRecDepth 100000\n"
          "set_option maxHeartbeats 0\n"
          "noncomputable section\n\n"
        + f"namespace {namespace}\n\n{body.strip()}\n"
        + f"end {namespace}\n\nend\n"
    )


def split(input_path: Path, output_dir: Path, module: str, force: bool) -> list[Path]:
    selected_match = SELECTED_MODULE_RE.fullmatch(module)
    require(selected_match is not None,
            "module must end in Action<number>ClassPilot")
    action_number = int(selected_match.group(1))
    split_module = module.removesuffix("ClassPilot")
    require(input_path.is_file() and not input_path.is_symlink(),
            "missing or redirected Lean input")
    raw = input_path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "Lean input byte ceiling reached")
    text = raw.decode("utf-8")

    namespace_marker = f"namespace SymmetricSubgroupAsymptotics.{module}"
    body_start = unique_index(text, namespace_marker) + len(namespace_marker)
    top_start = unique_index(text, "\nprivate def topRow0")
    class_start = unique_index(text, "\nprivate def representativeRows")
    centralizer_indices = [
        int(match.group(1))
        for match in re.finditer(r"(?m)^namespace C([0-9]+)$", text)
    ]
    require(centralizer_indices,
            "selected certificate has no centralizer sections")
    require(centralizer_indices == list(range(len(centralizer_indices))),
            "centralizer sections are not a contiguous zero-based range")
    centralizer_count = len(centralizer_indices)
    centralizer_starts = [
        unique_index(text, f"\nnamespace C{i}\n")
        for i in range(centralizer_count)
    ]
    centralizer_ends = [
        unique_index(text, f"\nend C{i}\n") + len(f"\nend C{i}\n")
        for i in range(centralizer_count)
    ]
    assembly_start = unique_index(text, "\nnoncomputable def centralizer : ∀")
    body_end = unique_index(text, f"\nend SymmetricSubgroupAsymptotics.{module}\n")

    require(body_start < top_start < class_start < centralizer_starts[0],
            "unexpected selected-certificate section order")
    for i in range(centralizer_count - 1):
        require(centralizer_starts[i] < centralizer_ends[i] <= centralizer_starts[i + 1],
                "overlapping centralizer sections")
    require(centralizer_starts[-1] < centralizer_ends[-1] <= assembly_start < body_end,
            "unexpected selected-certificate assembly order")

    base_body = text[body_start:top_start].replace(
        "local instance selectedSourceGroup : Group Source := group",
        "instance selectedSourceGroup : Group Source := group")
    pair_body = text[top_start:class_start]
    class_body = text[class_start:centralizer_starts[0]]
    centralizer_bodies = []
    for i in range(centralizer_count):
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

    imports_base = [
        "SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks",
        "SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates",
        "SymmetricSubgroupAsymptotics.FinitePermutationEncoding",
        "Mathlib.Order.Fin.Basic",
        "Mathlib.Tactic.FinCases",
    ]
    pieces: list[tuple[str, str]] = []
    title_prefix = f"Selected six-pair action {action_number}"
    pieces.append((f"{split_module}ClassBase.lean", wrapper(
        module, f"{title_prefix}: Cayley base", imports_base, base_body,
        action_number)))
    pieces.append((f"{split_module}PairTop.lean", wrapper(
        module, f"{title_prefix}: pair-top action",
        [f"SymmetricSubgroupAsymptotics.{split_module}ClassBase", "Mathlib.Tactic.FinCases"],
        pair_body, action_number)))
    pieces.append((f"{split_module}ClassInvariant.lean", wrapper(
        module, f"{title_prefix}: class invariant",
        [f"SymmetricSubgroupAsymptotics.{split_module}PairTop", "Mathlib.Tactic.FinCases"],
        class_body, action_number)))
    for i, body in enumerate(centralizer_bodies):
        pieces.append((f"{split_module}Centralizer{i}.lean", wrapper(
            module, f"{title_prefix}: centralizer row {i}",
            [f"SymmetricSubgroupAsymptotics.{split_module}ClassInvariant",
             "Mathlib.Tactic.FinCases"], body, action_number)))
    pieces.append((f"{module}.lean", wrapper(
        module, f"{title_prefix}: complete class cover",
        [f"SymmetricSubgroupAsymptotics.{split_module}Centralizer{i}"
         for i in range(centralizer_count)],
        assembly_body, action_number)))

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
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module name")
    outputs = split(args.input, args.output_dir, args.module, args.force)
    for path in outputs:
        print(path)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
