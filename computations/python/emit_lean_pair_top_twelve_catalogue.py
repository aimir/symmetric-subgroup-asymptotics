#!/usr/bin/env python3
"""Emit the bounded 301-row count-twelve pair-top catalogue.

The script checks the committed action and module digests, joins rows by
their exact ordered identifiers/generators, and emits only literal
permutations plus the already-recorded branch, kappa, and section-cap
scalars.  It performs no group enumeration.  Registry completeness in the
resulting Lean source comes from the canonical semantic constructors.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data"
ACTIONS = DATA / "pair_top_actions.json"
MODULES = DATA / "pair_top_modules.jsonl.gz"
ACTIONS_SHA256 = "0b6faa0cbb65ab790915de720f80ed62676fa8369aa003d3a4aaf209d6fd0493"
MODULES_SHA256 = "ed80738802abd966f67bc2c1643556e87fd640357f3dcc6518fbbb561522816b"
INPUT_LIMIT = 256 * 1024
DECOMPRESSED_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 2 * 1024 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def pinned(path: Path, digest: str) -> bytes:
    require(path.is_file() and not path.is_symlink(),
            f"missing or redirected input: {path.name}")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, f"input ceiling reached: {path.name}")
    require(hashlib.sha256(raw).hexdigest() == digest,
            f"digest changed: {path.name}")
    return raw


def inverse(row: list[int]) -> list[int]:
    result = [0] * len(row)
    for source, target in enumerate(row):
        result[target - 1] = source + 1
    return result


def lean_array(row: list[int]) -> str:
    return "#[" + ", ".join(str(x - 1) for x in row) + "]"


def literal_interface(prefix: str, degree: int,
                      generators: list[list[int]]) -> list[str]:
    lines: list[str] = []
    for j, row in enumerate(generators):
        lines.extend([
            f"private def {prefix}Generator{j} : Equiv.Perm (Fin {degree}) where",
            f"  toFun x := ({lean_array(row)} : Array (Fin {degree}))[x.val]!",
            f"  invFun x := ({lean_array(inverse(row))} : Array (Fin {degree}))[x.val]!",
            "  left_inv := by decide +kernel",
            "  right_inv := by decide +kernel",
            "",
        ])
    entries = ", ".join(
        f"{prefix}Generator{j}" for j in range(len(generators))
    )
    title = prefix[0].upper() + prefix[1:]
    lines.extend([
        f"def {prefix}Generators : Fin {len(generators)} → Equiv.Perm (Fin {degree}) :=",
        f"  ![{entries}]",
        "",
        f"abbrev {title}Top : Subgroup (Equiv.Perm (Fin {degree})) :=",
        f"  Subgroup.closure (Set.range {prefix}Generators)",
        "",
        f"noncomputable def {prefix}Interface : DegreeTwoPairTopFiniteInterface {degree} :=",
        "  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries",
        f"    {title}Top",
        "",
    ])
    return lines


def fin_cases(values: list[str]) -> str:
    result = ""
    for value in values:
        result += f"Fin.cases {value} <| "
    return result + "Fin.elim0"


def render(actions: list[dict], modules: list[dict]) -> str:
    module_by_id = {row["id"]: row for row in modules}
    twelve = [row for row in actions if row.get("family") == "twelve"]
    paired6 = [row for row in actions if row.get("family") == "paired6"]
    require(len(twelve) == 301 and len(paired6) == 2,
            "count-twelve domain changed")
    require([row["index"] for row in twelve] == list(range(1, 302)),
            "count-twelve indices changed")
    require([row["index"] for row in paired6] == [1, 2],
            "paired-six indices changed")
    for row in twelve + paired6:
        module = module_by_id.get(row["id"])
        require(module is not None, f"missing module row: {row['id']}")
        require(module["generators"] == row["generators"],
                f"generator mismatch: {row['id']}")

    lines = [
        "import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues",
        "",
        "/-! Generated literal count-twelve pair-top catalogue from the pinned",
        "action/module alphabet.  Completeness of each registry is semantic. -/",
        "",
        "set_option autoImplicit false",
        "noncomputable section",
        "open scoped Classical",
        "",
        "namespace SymmetricSubgroupAsymptotics",
        "namespace Non2UnipotentPrefixFiniteMenu",
        "namespace PrimitiveAffineImprimitiveBlockTransfer",
        "namespace DegreeTwoTwelvePairFiniteCatalogue",
        "",
    ]
    for row in twelve:
        lines.extend(literal_interface(
            f"row{row['index']}", 12, row["generators"]))
    for row in paired6:
        lines.extend(literal_interface(
            f"pairedSix{row['index']}", 6, row["generators"]))

    branches = [f".{row['branch']}" for row in twelve]
    kappas = [str(row["kappa"]) for row in twelve]
    caps = [str(module_by_id[row["id"]]["section_cap"]) for row in twelve]
    interfaces = [f"row{row['index']}Interface" for row in twelve]
    lines.extend([
        "def branch : Fin 301 → DegreeTwoTwelvePairTopBranch :=",
        "  " + fin_cases(branches),
        "",
        "def kappa : Fin 301 → ℕ :=",
        "  " + fin_cases(kappas),
        "",
        "def sectionCap : Fin 301 → ℕ :=",
        "  " + fin_cases(caps),
        "",
        "noncomputable def finiteInterface : Fin 301 →",
        "    DegreeTwoPairTopFiniteInterface 12 :=",
        "  " + fin_cases(interfaces),
        "",
        "noncomputable def row (j : Fin 301) : DegreeTwoTwelvePairTopRow where",
        "  finite := finiteInterface j",
        "  branch := branch j",
        "  kappa := kappa j",
        "  sectionCap := sectionCap j",
        "  expectedProfiles :=",
        "    match branch j with",
        "    | .joint => degreeTwoTwelvePairJointProfiles (kappa j) (sectionCap j)",
        "    | .core => degreeTwoTwelvePairExceptionalProfiles",
        "    | .ternary => ∅",
        "    | .paired => degreeTwoTwelvePairExceptionalProfiles",
        "  expectedProfiles_eq := rfl",
        "",
        "noncomputable def pairedSix : Fin 2 → DegreeTwoPairTopFiniteInterface 6 :=",
        "  Fin.cases pairedSix1Interface <| Fin.cases pairedSix2Interface Fin.elim0",
        "",
        "private def pairedPosition : Fin 2 → Fin 301 := ![194, 235]",
        "",
        "private def pairedForward",
        "    (j : {j : Fin 301 // (row j).branch = .paired}) : Fin 2 :=",
        "  if j.1.val = 194 then 0 else 1",
        "",
        "private def pairedBackward",
        "    (i : Fin 2) : {j : Fin 301 // (row j).branch = .paired} :=",
        "  ⟨pairedPosition i, by fin_cases i <;> native_decide⟩",
        "",
        "private def pairedBinding :",
        "    {j : Fin 301 // (row j).branch = .paired} ≃ Fin 2 where",
        "  toFun := pairedForward",
        "  invFun := pairedBackward",
        "  left_inv := by native_decide +revert",
        "  right_inv := by native_decide +revert",
        "",
        "noncomputable def catalogue : DegreeTwoTwelvePairTopFiniteCatalogue where",
        "  row := row",
        "  pairedSix := pairedSix",
        "  pairedSixBinding := pairedBinding",
        "  joint_count := by native_decide",
        "  core_count := by native_decide",
        "  ternary_count := by native_decide",
        "  paired_count := by native_decide",
        "",
        "end DegreeTwoTwelvePairFiniteCatalogue",
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
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(args.output.parent.exists(), "output parent must already exist")
    action_raw = pinned(ACTIONS, ACTIONS_SHA256)
    module_compressed = pinned(MODULES, MODULES_SHA256)
    module_raw = gzip.decompress(module_compressed)
    require(len(module_raw) <= DECOMPRESSED_LIMIT,
            "module decompression ceiling reached")
    action_data = json.loads(action_raw)
    require(action_data.get("schema_version") == 1,
            "unexpected action schema")
    modules = [json.loads(line) for line in module_raw.splitlines()
               if line.strip()]
    output = render(action_data.get("actions", []), modules).encode()
    require(len(output) <= OUTPUT_LIMIT, "output ceiling reached")
    args.output.write_bytes(output)
    print(f"WROTE twelve: {args.output} ({len(output)} bytes)")


if __name__ == "__main__":
    main()
