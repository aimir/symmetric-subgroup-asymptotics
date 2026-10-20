#!/usr/bin/env python3
"""Prepare one exact sixteen-point registry reuse from pinned Git source.

This is a source preparation tool, not a proof checker. It restores only the
selected owner's missing split normal-registry sources, changes exactly three
top proof blocks, and renders one quotient-socle adapter and finite package.
The existing literal data is preserved. No group, vector, submodule, or full
dataset is enumerated. No Lean, exporter, or other producer is invoked.

All selection arguments are mandatory. There is no batch mode or limit override.
The first new pilot is zero16 row6 / owner6 (192 stored rows). Larger sources or
different templates require a separately reviewed implementation and pilot.
Run only under the primary agent's selected producer resource limits, separately
from compiler execution. Source provenance and generated checks remain unverified
until the primary checks the full dependency chain and audits its Lean axioms.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

# Reuse only the selected adapter's literal parsers/render function. Importing it
# does not run its CLI. Keep Python cache files out of the publication checkout.
sys.dont_write_bytecode = True
import emit_lean_pair_top_selected_registry_socles as adapter


PROJECT = "SymmetricSubgroupAsymptotics."
FORMAL = Path("formal/SymmetricSubgroupAsymptotics")
MAX_ROWS = 192
MAX_OWNER_FILES = 96
MAX_OWNER_BYTES = 8 * 1024 * 1024
MAX_BOUNDARY_FILES = 32
SOURCE_LIMIT = adapter.SOURCE_LIMIT
require = adapter.require
Refused = adapter.Refused

ENCODED_IMPORT = "import SymmetricSubgroupAsymptotics.EncodedPermutationRowChecks\n"
IMPORT_ANCHOR = "import SymmetricSubgroupAsymptotics.FinitePermutationEncoding\n"
OLD_INJECTIVE = """theorem rows_injective : Function.Injective certificate.rows :=
  by native_decide
"""
OLD_INVARIANT = "  generator_invariant := by native_decide +revert\n"
NEW_INVARIANT = """  generator_invariant := by
    exact certificate.row_generator_invariant_of_permutationCodes
      rows_injective previousRow previous_checked classCodeRows
      decodeCode decodeCode_leftInverse (by
        intro j i
        fin_cases j <;> fin_cases i <;> decide +kernel)
"""
OLD_CENTRALIZER = """  intro i
  letI : DecidablePred (fun x : Source =>
      x ∈ Subgroup.centralizer ({representative i} : Set Source)) :=
    fun x => decidable_of_iff (x * representative i = representative i * x)
      Subgroup.mem_centralizer_singleton_iff.symm
  fin_cases i <;>
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] <;>
    native_decide
"""
NEW_CENTRALIZER = """  intro i
  change Nat.card (Subgroup.centralizer
    ({(⟨representativeRows i⟩ : Source)} : Set Source)) = centralizerCard i
  rw [certificate.row_centralizer_card_permutationCodeMul
    rows_injective previousRow previous_checked]
  fin_cases i <;> decide +kernel
"""


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> bytes:
    result = subprocess.run(["git", "-C", str(repo), *args], check=False,
                            capture_output=True, timeout=15)
    require(result.returncode == 0,
            f"git {' '.join(args)} failed: {result.stderr.decode(errors='replace')[:1000]}")
    return result.stdout


def source_bytes(data: bytes, name: str) -> bytes:
    require(len(data) <= SOURCE_LIMIT, f"{name}: source exceeds the selected size limit")
    text = data.decode("utf-8")
    require("\r" not in text and text.endswith("\n"), f"{name}: expected LF-terminated UTF-8")
    require(all(len(line) <= adapter.LINE_LIMIT for line in data.splitlines()),
            f"{name}: source line exceeds the selected limit")
    return data


def git_source(repo: Path, commit: str, rel: Path) -> bytes:
    obj = f"{commit}:{rel.as_posix()}"
    size = int(git(repo, "cat-file", "-s", obj))
    require(0 < size <= SOURCE_LIMIT, f"{obj}: source size exceeds the selected bound")
    data = git(repo, "show", obj)
    require(len(data) == size, f"{obj}: blob size changed")
    return source_bytes(data, obj)


def local_source(repo: Path, rel: Path) -> bytes:
    path = repo / rel
    require(path.is_file() and not path.is_symlink(), f"{rel}: missing source or symlink")
    require(path.resolve().is_relative_to(repo), f"{rel}: source escapes the checkout")
    require(path.stat().st_size <= SOURCE_LIMIT, f"{rel}: source exceeds the selected bound")
    return source_bytes(path.read_bytes(), str(rel))


def module_path(module: str) -> Path:
    require(re.fullmatch(r"SymmetricSubgroupAsymptotics\.[A-Z][A-Za-z0-9_]*", module)
            is not None, f"unsupported project module: {module}")
    return FORMAL / (module.removeprefix(PROJECT) + ".lean")


def imports(data: bytes, name: str) -> list[str]:
    """Closed import parser for the generated files' leading import block."""
    result = []
    past_header = False
    for line in data.decode().splitlines():
        if not line.strip():
            continue
        if line.startswith("import ") and not past_header:
            match = re.fullmatch(r"import ((?:SymmetricSubgroupAsymptotics|Mathlib)\.[A-Za-z0-9_.]+)", line)
            require(match is not None, f"{name}: unsupported import line")
            result.append(match.group(1))
        else:
            past_header = True
            require(not re.match(r"\s*import\b", line), f"{name}: import outside leading block")
    require(result and len(result) == len(set(result)), f"{name}: missing or duplicate imports")
    return result


def declaration(text: str, signature: str) -> str:
    """Select one declaration without interpreting any registry payload."""
    lines = text.splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if re.match(signature, line)]
    require(len(starts) == 1, f"expected exactly one declaration matching {signature}")
    start = starts[0]
    stop = start + 1
    while stop < len(lines) and (not lines[stop].strip() or lines[stop][0].isspace()):
        stop += 1
    return "".join(lines[start:stop]).rstrip() + "\n"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    require(text.count(old) == 1, f"{label}: expected exactly one supported template")
    require(new not in text, f"{label}: already modified or ambiguous template")
    return text.replace(old, new, 1)


def patch_top(data: bytes, owner: int) -> tuple[bytes, int]:
    text = data.decode()
    require(text.count("native_decide") == 3, "top: expected exactly three native proof sites")
    require("decodeCode" not in text and ENCODED_IMPORT not in text,
            "top: unsupported preexisting decoder or encoded import")
    rows = re.findall(r"^abbrev Source := FiniteGroupRow (\d+)$", text, re.MULTILINE)
    require(len(rows) == 1, "top: expected one finite source declaration")
    count = int(rows[0])
    require(1 <= count <= MAX_ROWS, f"top has {count} rows; selected ceiling is {MAX_ROWS}")
    require(text.count(f"namespace {PROJECT}PrimitiveAffineSixteenFrameRow{owner}TopCertificate\n") == 1,
            "top: namespace does not match selected owner")
    require(text.count(f"private def codes (i : Fin {count}) : Fin (16^16) :=\n") == 1,
            "top: code table signature does not match source cardinality")
    require(text.count(f"    (permutationGeneratorEncoding generators) {count} where\n") == 1,
            "top: certificate cardinality differs from code table")
    centralizer = declaration(text, r"^private theorem centralizer_card\b")
    require(centralizer.endswith(OLD_CENTRALIZER), "top: unsupported centralizer theorem body")
    injective = f"""/-- Recover the stored row index by a bounded lookup in this literal table. -/
private def decodeCode (code : Fin (16 ^ 16)) : Fin {count} :=
  ((List.finRange {count}).find? (fun i ↦ decide (certificate.rows i = code))).getD 0

private theorem decodeCode_leftInverse : Function.LeftInverse decodeCode certificate.rows := by
  intro i
  fin_cases i <;> decide +kernel

theorem rows_injective : Function.Injective certificate.rows :=
  decodeCode_leftInverse.injective
"""
    replacements = [
        (IMPORT_ANCHOR, IMPORT_ANCHOR + ENCODED_IMPORT, "encoded import"),
        (OLD_INJECTIVE, injective, "row injectivity"),
        (OLD_INVARIANT, NEW_INVARIANT, "class invariant"),
        (OLD_CENTRALIZER, NEW_CENTRALIZER, "centralizer count"),
    ]
    patched = text
    for old, new, label in replacements:
        patched = replace_once(patched, old, new, label)
    recovered = patched
    for old, new, label in reversed(replacements):
        require(recovered.count(new) == 1, f"{label}: reverse template is ambiguous")
        recovered = recovered.replace(new, old, 1)
    require(recovered == text, "top: changes escaped the three proof blocks and added import")
    require(not re.search(r"\b(native_decide|sorry|admit)\b", patched), "top: unresolved proof site")
    return patched.encode(), count


def package(module: str, stem: str, family: str, row: int) -> str:
    interface = f"DegreeTwo{stem}Interfaces.row{row}"
    selected = f"PrimitiveAffineDegreeTwo{stem}Row{row}"
    catalogue_size = {"zero16": 29, "primitive16": 20}[family]
    return f"""import SymmetricSubgroupAsymptotics.{selected}OrbitWitness
import SymmetricSubgroupAsymptotics.{selected}QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected {family} row {row}

Prepared by `prepare_lean_selected_pair_registry_sources.py`. The existing
orbit witness and the reused normal registry retain the actual literal top.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace {module}

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData {interface} :=
  .ofCertificates {selected}QuotientSocles.family
    {selected}OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.{family} ({row - 1} : Fin {catalogue_size})) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {{p : PreE7PairActionClass 16}}
    (R : DegreeTwoPairTopRealization {interface} p) :
    DegreeTwoPairTopResolvedRow {interface}
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end {module}
end SymmetricSubgroupAsymptotics

end
"""


def prepare(args: argparse.Namespace) -> dict:
    repo = Path(__file__).resolve().parents[2]
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_commit) is not None,
            "source-commit must be a full pinned commit hash")
    commit = git(repo, "rev-parse", f"{args.source_commit}^{{commit}}").decode().strip()
    require(commit == args.source_commit, "source-commit did not resolve to itself")
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    stem = adapter.FAMILIES[args.family]
    expected = args.row if args.family == "zero16" and 2 <= args.row <= 29 else None
    if args.family == "primitive16":
        expected = adapter.PRIMITIVE_OWNERS.get(args.row)
    require(expected is not None and args.degree4_owner == expected,
            "selection is not an audited exact match with a split normal registry")
    owner = args.degree4_owner
    receipt_dir = args.receipt_dir.resolve()
    # Also exclude the publication's other linked checkouts, not only this one.
    worktrees = git(repo, "worktree", "list", "--porcelain").decode().splitlines()
    roots = [Path(line.removeprefix("worktree ")).resolve()
             for line in worktrees if line.startswith("worktree ")]
    require(all(not receipt_dir.is_relative_to(root) for root in roots),
            "receipt directory must be outside every publication checkout")
    require(not receipt_dir.exists(), "receipt directory already exists; refusing to overwrite")

    prefix = PROJECT + f"PrimitiveAffineSixteenFrameRow{owner}"
    top = prefix + "TopCertificate"
    normal = prefix + "NormalCertificate"
    core = prefix + "NormalCore"
    originals: dict[str, bytes] = {}
    order: list[str] = []
    boundary: set[str] = set()
    visiting: set[str] = set()

    def visit(module: str) -> None:
        require(module not in visiting, f"cyclic selected imports: {module}")
        if module in originals:
            return
        require(re.fullmatch(re.escape(prefix) + r"(?:TopCertificate|Normal[A-Za-z0-9]+)", module)
                is not None, f"unsupported selected owner module: {module}")
        require(len(originals) < MAX_OWNER_FILES, "selected import chain exceeds file ceiling")
        data = git_source(repo, commit, module_path(module))
        originals[module] = data
        require(sum(map(len, originals.values())) <= MAX_OWNER_BYTES,
                "selected import chain exceeds byte ceiling")
        visiting.add(module)
        for dep in imports(data, module):
            if dep.startswith(prefix):
                visit(dep)
            elif dep.startswith(PROJECT):
                require("PrimitiveAffineSixteenFrameRow" not in dep,
                        "selected normal registry imports a different row")
                boundary.add(dep)
        visiting.remove(module)
        order.append(module)

    visit(normal)
    require(top in originals and core in originals, "expected a split top/core/normal registry")
    planned = dict(originals)
    planned[top], row_count = patch_top(originals[top], owner)
    for module, data in originals.items():
        if module != top:
            require(not re.search(rb"\b(native_decide|sorry|admit)\b", data),
                    f"{module}: unchanged normal source has an unsupported proof site")

    # Verify the deterministic replacement against the two already checked
    # exact templates. Their files are read only, and no proof status is inferred.
    anchors = []
    for reference in (4, 5):
        rel = FORMAL / f"PrimitiveAffineSixteenFrameRow{reference}TopCertificate.lean"
        original = git_source(repo, commit, rel)
        patched, count = patch_top(original, reference)
        local = local_source(repo, rel)
        require(local == patched, f"{rel}: differs from the audited row4/5 replacement template")
        anchors.append({"path": str(rel), "pinned_original_sha256": sha(original),
                        "local_sha256": sha(local), "row_count": count})

    interface_rel = FORMAL / f"PrimitiveAffineDegreeTwo{stem}Interfaces.lean"
    interface_data = local_source(repo, interface_rel)
    selected, fragments = adapter.interface_generators(repo / interface_rel, args.row)
    header = originals[top].decode().split("private def codes ", 1)
    require(len(header) == 2, "top: expected one literal codes declaration")
    literal_generators = adapter.top_generators(header[0])
    require(literal_generators == selected, "ordered literal generator arrays differ from interface")

    child_block = declaration(originals[core].decode(), r"^def child\b")
    child = adapter.child_table(child_block)
    normal_text = originals[normal].decode()
    data_block = declaration(normal_text, r"^noncomputable def data\b")
    require("FiniteNormalJoinWordRegistryData" in data_block, "unsupported normal registry data")
    bottoms = re.findall(r"^  bottom := (\d+)\s*$", data_block, re.MULTILINE)
    require(len(bottoms) == 1, "normal data must have one literal bottom")
    require(re.search(r"^  child := child\s*$", data_block, re.MULTILINE) is not None,
            "normal data does not retain its exported child table")
    alias = declaration(normal_text, r"^abbrev child\b")
    require(" ".join(alias.split()) ==
            f"abbrev child := PrimitiveAffineSixteenFrameRow{owner}NormalCore.child",
            "normal child does not retain the selected core table")
    bottom = int(bottoms[0])
    witnesses = adapter.two_steps(child, bottom)
    selected_name = f"PrimitiveAffineDegreeTwo{stem}Row{args.row}"
    socles_name = selected_name + "QuotientSocles"
    package_name = selected_name + "FinitePackage"
    require(args.output.resolve() == (repo / module_path(PROJECT + package_name)).resolve(),
            "output must be the selected finite-package source")
    socles = adapter.render(socles_name, stem, args.row, owner, bottom, child, witnesses)
    socles = socles.replace("Generated by `emit_lean_pair_top_selected_registry_socles.py`",
                            "Prepared using `emit_lean_pair_top_selected_registry_socles.py`")
    for name, text in [(socles_name, socles),
                       (package_name, package(package_name, stem, args.family, args.row))]:
        module = PROJECT + name
        require(not (repo / module_path(module)).exists(), f"{name}: output already exists")
        planned[module] = source_bytes(text.encode(), module)
        order.append(module)
    require(sum(map(len, planned.values())) <= MAX_OWNER_BYTES,
            "prepared selected sources exceed byte ceiling")
    for module, data in planned.items():
        for dep in imports(data, module):
            if dep.startswith(PROJECT) and dep not in planned:
                boundary.add(dep)
    require(len(boundary) <= MAX_BOUNDARY_FILES, "too many preexisting import boundaries")

    # An existing boundary dependency must be committed byte-for-byte at the
    # captured HEAD. Record both blob identity and content hash. These are source
    # provenance checks, not proof receipts or a transitive axiom audit.
    boundary_sources = []
    boundary_bytes: dict[Path, bytes] = {}
    for module in sorted(boundary):
        rel = module_path(module)
        local = local_source(repo, rel)
        require(local == git_source(repo, head, rel), f"{rel}: imported source differs from HEAD")
        boundary_bytes[rel] = local
        boundary_sources.append({"module": module, "path": str(rel), "commit": head,
                                 "git_blob": git(repo, "rev-parse", f"{head}:{rel}").decode().strip(),
                                 "sha256": sha(local), "bytes": len(local)})
    require(interface_rel in boundary_bytes and boundary_bytes[interface_rel] == interface_data,
            "interface source changed while preparing the plan")
    helper_rel = Path(adapter.__file__).resolve().relative_to(repo)
    helper_data = local_source(repo, helper_rel)
    require(helper_data == git_source(repo, head, helper_rel), "selected parser/render helper differs from HEAD")

    writes: list[str] = []
    files = []
    for module in order:
        rel = module_path(module)
        path = repo / rel
        exists = path.exists()
        if exists:
            require(module in originals and local_source(repo, rel) == planned[module],
                    f"{rel}: existing source differs from the exact prepared source; left untouched")
        else:
            writes.append(module)
        files.append({"module": module, "path": str(rel), "bytes": len(planned[module]),
                      "output_sha256": sha(planned[module]),
                      "original_sha256": sha(originals[module]) if module in originals else None,
                      "action": "preserve_exact_existing" if exists else "create_missing",
                      "normal_source_unchanged": module in originals and module != top,
                      "lean_checked": False})

    provenance = {
        "schema": "selected-pair-registry-source-preparation-v1", "phase": "planned",
        "family": args.family, "row_one_based": args.row, "degree4_owner": owner,
        "source_commit": commit, "boundary_source_commit": head, "repository": str(repo),
        "tool_sha256": sha(Path(__file__).read_bytes()),
        "adapter_helper": {"path": str(helper_rel), "sha256": sha(helper_data)},
        "reference_top_templates": anchors, "top_row_count": row_count,
        "state_count": len(child), "class_count": len(child[0]), "bottom": bottom,
        "generator_arrays_zero_based": [list(p) for p in literal_generators],
        "interface_fragment_sha256": {name: adapter.digest(text) for name, text in fragments.items()},
        "child_table_sha256": adapter.digest(child_block), "two_step_witnesses": witnesses,
        "owner_original_bytes": sum(map(len, originals.values())),
        "proof_template_counts": {"added_import": 1, "replaced_top_proof_blocks": 3,
                                  "original_native_sites": 3, "remaining_native_sites": 0},
        "boundary_sources": boundary_sources, "files": files, "check_order": order,
        "written_modules": [], "lean_checked": False,
        "note": "Source provenance only. Boundary hashes cover direct preexisting imports, not their transitive proof closure. Run the ordered bounded Lean checks and a standard-axiom audit; generation is not proof.",
    }
    # No mutation above this point. Recheck shared source fingerprints immediately
    # before writing; preserve an external original and prepared copy of every file.
    require(git(repo, "rev-parse", "HEAD").decode().strip() == head, "HEAD changed during preparation")
    for rel, data in boundary_bytes.items():
        require(local_source(repo, rel) == data, f"{rel}: dependency changed during preparation")
    require(local_source(repo, helper_rel) == helper_data, "adapter helper changed during preparation")
    receipt_dir.mkdir(parents=True, exist_ok=False)
    manifest = receipt_dir / "prepared_source_provenance.json"

    def save_manifest() -> None:
        manifest.write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")

    save_manifest()
    try:
        for directory, sources in [("pinned_originals", originals), ("prepared_sources", planned)]:
            for module, data in sources.items():
                target = receipt_dir / directory / module_path(module)
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open("xb") as stream:
                    stream.write(data)
        for module in writes:
            target = repo / module_path(module)
            with target.open("xb") as stream:
                stream.write(planned[module])
            require(target.read_bytes() == planned[module], f"{target}: post-write verification failed")
            provenance["written_modules"].append(module)
        provenance["phase"] = "sources_written_not_lean_checked"
        save_manifest()
    except BaseException:
        provenance["phase"] = "interrupted_preserve_partial_sources"
        save_manifest()
        raise
    return {"receipt": str(manifest), "created_modules": len(writes),
            "ordered_checks": len(order), "top_rows": row_count, "lean_checked": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", required=True, choices=adapter.FAMILIES)
    parser.add_argument("--row", required=True, type=int, help="one selected one-based degree-two row")
    parser.add_argument("--degree4-owner", required=True, type=int)
    parser.add_argument("--source-commit", required=True, help="full pinned commit for original registry sources")
    parser.add_argument("--output", required=True, type=Path,
                        help="exact selected finite-package source, for the bounded stage runner")
    parser.add_argument("--receipt-dir", required=True, type=Path,
                        help="new directory outside all publication checkouts")
    args = parser.parse_args()
    try:
        print(json.dumps(prepare(args)))
    except (Refused, OSError, UnicodeError, RecursionError, subprocess.SubprocessError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
