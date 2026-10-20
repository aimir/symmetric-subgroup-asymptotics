#!/usr/bin/env python3
"""Emit bounded literal pair-top interfaces from the pinned action alphabet.

This producer does no group enumeration and reads no compressed certificate
file.  It translates one requested count-sixteen family from the committed,
SHA-pinned action alphabet into literal Lean permutations and installs the
census-free semantic normal/module registries.  The already checked shared
top for ``zero16-1`` is reused instead of re-emitted.

Run one family at a time.  The output parent must already exist and output is
capped at 2 MiB.  Lean compilation remains a separate primary-agent step.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ACTIONS = ROOT / "certificates/data/pair_top_actions.json"
ACTIONS_SHA256 = "0b6faa0cbb65ab790915de720f80ed62676fa8369aa003d3a4aaf209d6fd0493"
INPUT_LIMIT = 256 * 1024
OUTPUT_LIMIT = 2 * 1024 * 1024

FAMILIES = {
    "zero16": (29, "DegreeTwoZeroSixteenInterfaces"),
    "two_affine16": (15, "DegreeTwoTwoAffineSixteenInterfaces"),
    "primitive16": (20, "DegreeTwoPrimitiveSixteenInterfaces"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def inverse(row: list[int]) -> list[int]:
    result = [0] * len(row)
    for source, target in enumerate(row):
        result[target - 1] = source + 1
    return result


def lean_array(row: list[int]) -> str:
    return "#[" + ", ".join(str(x - 1) for x in row) + "]"


def imports(family: str) -> list[str]:
    result = [
        "import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues"
    ]
    if family == "zero16":
        result.append(
            "import SymmetricSubgroupAsymptotics."
            "PrimitiveAffineSixteenFrameRow1NormalCertificate"
        )
    return result


def reused_zero_one() -> list[str]:
    return [
        "noncomputable def row1 : DegreeTwoPairTopFiniteInterface 16 := by",
        "  letI : Group PrimitiveAffineSixteenFrameRow1TopCertificate.Source :=",
        "    PrimitiveAffineSixteenFrameRow1TopCertificate.group",
        "  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv",
        "    PrimitiveAffineSixteenFrameRow1NormalCertificate.topConjugacy.toCardinalCover",
        "    PrimitiveAffineSixteenFrameRow1NormalCertificate.topAmbient",
        "    PrimitiveAffineSixteenFrameRow1NormalCertificate.stateGenerators",
        "    PrimitiveAffineSixteenFrameRow1NormalCertificate.data",
        "    (Subgroup.closure",
        "      (Set.range PrimitiveAffineSixteenFrameRow1TopCertificate.generators))",
        "    PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv",
        "",
    ]


def literal_row(index: int, generators: list[list[int]]) -> list[str]:
    lines: list[str] = []
    for j, row in enumerate(generators):
        inv = inverse(row)
        lines.extend([
            f"private def row{index}Generator{j} : Equiv.Perm (Fin 16) where",
            f"  toFun x := ({lean_array(row)} : Array (Fin 16))[x.val]!",
            f"  invFun x := ({lean_array(inv)} : Array (Fin 16))[x.val]!",
            "  left_inv := by decide +kernel",
            "  right_inv := by decide +kernel",
            "",
        ])
    entries = ", ".join(
        f"row{index}Generator{j}" for j in range(len(generators))
    )
    lines.extend([
        f"def row{index}Generators : Fin {len(generators)} → Equiv.Perm (Fin 16) :=",
        f"  ![{entries}]",
        "",
        f"abbrev Row{index}Top : Subgroup (Equiv.Perm (Fin 16)) :=",
        f"  Subgroup.closure (Set.range row{index}Generators)",
        "",
        f"noncomputable def row{index} : DegreeTwoPairTopFiniteInterface 16 :=",
        "  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries",
        f"    Row{index}Top",
        "",
    ])
    return lines


def dispatch(count: int) -> list[str]:
    expression = "Fin.cases row1 "
    for index in range(2, count + 1):
        expression += f"<| Fin.cases row{index} "
    expression += "Fin.elim0"
    return [
        f"noncomputable def interface : Fin {count} →",
        "    DegreeTwoPairTopFiniteInterface 16 :=",
        "  " + expression,
        "",
    ]


def render(family: str, rows: list[dict]) -> str:
    expected, namespace = FAMILIES[family]
    require(len(rows) == expected, f"{family} row count changed")
    require([row["index"] for row in rows] == list(range(1, expected + 1)),
            f"{family} indices changed")
    lines = imports(family) + [
        "",
        "/-! Generated literal interfaces for the pinned pair-top action family.",
        "The generator arrays are theorem data; registry completeness is",
        "semantic and does not trust a JSON census flag. -/",
        "",
        "set_option autoImplicit false",
        "noncomputable section",
        "open scoped Classical",
        "",
        "namespace SymmetricSubgroupAsymptotics",
        "namespace Non2UnipotentPrefixFiniteMenu",
        "namespace PrimitiveAffineImprimitiveBlockTransfer",
        f"namespace {namespace}",
        "",
    ]
    for row in rows:
        require(row["degree"] == 16 and row["family"] == family,
                f"malformed {row.get('id')}")
        if family == "zero16" and row["index"] == 1:
            lines.extend(reused_zero_one())
        else:
            lines.extend(literal_row(row["index"], row["generators"]))
    lines.extend(dispatch(expected))
    lines.extend([
        f"end {namespace}",
        "end PrimitiveAffineImprimitiveBlockTransfer",
        "end Non2UnipotentPrefixFiniteMenu",
        "end SymmetricSubgroupAsymptotics",
        "",
        "end",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(args.output.parent.exists(), "output parent must already exist")
    require(ACTIONS.is_file() and not ACTIONS.is_symlink(),
            "missing or redirected action alphabet")
    raw = ACTIONS.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "action alphabet input ceiling reached")
    require(hashlib.sha256(raw).hexdigest() == ACTIONS_SHA256,
            "action alphabet digest changed")
    data = json.loads(raw)
    require(data.get("schema_version") == 1, "unexpected action schema")
    rows = [row for row in data.get("actions", [])
            if row.get("family") == args.family]
    output = render(args.family, rows).encode()
    require(len(output) <= OUTPUT_LIMIT, "output ceiling reached")
    args.output.write_bytes(output)
    print(f"WROTE {args.family}: {args.output} ({len(output)} bytes)")


if __name__ == "__main__":
    main()
