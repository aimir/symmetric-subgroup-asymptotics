#!/usr/bin/env python3
"""Run or print the sequential grouped frames8 recovery plan.

The plan has seven exact literal tops and fourteen rows.  Heavy Cayley,
conjugacy, normal-lattice, radical, and top-registry work is produced once per
top.  Local quotient and binary-module work remains per row.  Normality,
normal-join, and radical checks are deliberately one finite cell per process,
so no stage inherits the old monolithic preparer's aggregate operation count.

Dry-run is the default.  ``--execute`` runs subprocesses strictly one at a
time and never invokes Lean or ``check_lean.py``; it only prepares inputs and
renders source modules for later serialized checking by the primary agent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
PYTHON = ROOT / "computations/python"
DEFAULT_CONFIG = ROOT / "computations/frames/frames8_grouped_remaining.json"
FORMAL = ROOT / "formal/SymmetricSubgroupAsymptotics"
PLAN_SCHEMA = "frames8-grouped-remaining-plan-v1"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_config(path: Path) -> dict:
    value = json.loads(path.read_text())
    require(isinstance(value, dict) and value.get("schema") == PLAN_SCHEMA,
            "unexpected grouped-plan schema")
    require(value.get("row_convention") == "zero-based",
            "grouped plan must use zero-based rows")
    require(hashlib.sha256((ROOT / "computations/frames/bindings8.g").read_bytes()).hexdigest()
            == value.get("bindings_sha256"), "bindings8.g digest changed")
    require(hashlib.sha256((ROOT / "computations/frames/frames8.json").read_bytes()).hexdigest()
            == value.get("frames_sha256"), "frames8.json digest changed")
    expected = {
        "top8": (8, 7, 576, 10, [10, 11, 12, 13]),
        "top9": (9, 8, 576, 14, [14, 15, 16, 17]),
        "top10": (10, 9, 1152, 18, [18, 19]),
        "top13": (13, 12, 192, 22, [22]),
        "top15": (15, 14, 192, 24, [24]),
        "top16": (16, 15, 192, 25, [25]),
        "top17": (17, 16, 384, 26, [26]),
    }
    groups = value.get("groups")
    require(isinstance(groups, list) and len(groups) == len(expected),
            "wrong grouped-plan top count")
    seen_rows = []
    for group in groups:
        key = group.get("key")
        require(key in expected, f"unexpected group {key}")
        actual = (group.get("top_id"), group.get("top_index"),
                  group.get("top_order"), group.get("representative_row"),
                  group.get("rows"))
        require(actual == expected[key], f"changed exact grouping for {key}")
        require(group["representative_row"] == group["rows"][0],
                f"representative is not first for {key}")
        seen_rows.extend(group["rows"])
    require(seen_rows == list(range(10, 20)) + [22, 24, 25, 26],
            "remaining row coverage changed")
    limits = value.get("limits", {})
    require(limits == {"operation_limit": 40_000_000,
                       "seconds_limit": 300.0}, "unsafe staged limits")
    return value


def module_path(formal: Path, module: str) -> Path:
    return formal / f"{module}.lean"


class Runner:
    def __init__(self, execute: bool, force: bool):
        self.execute = execute
        self.force = force
        self.count = 0

    def command(self, arguments: list[object], supports_force: bool = True) -> None:
        command = [str(x) for x in arguments]
        if self.force and supports_force:
            command.append("--force")
        self.count += 1
        print(" ".join(command))
        if self.execute:
            subprocess.run(command, cwd=ROOT, check=True)


def script(name: str) -> Path:
    return PYTHON / name


def limits(config: dict) -> list[object]:
    value = config["limits"]
    return ["--operation-limit", value["operation_limit"],
            "--seconds-limit", value["seconds_limit"]]


def emit_top_modules(runner: Runner, shared: Path, formal: Path,
                     top_prefix: str) -> None:
    prepared = shared / "top-assembled.json"
    top_module = top_prefix + "TopCertificate"
    normal_module = top_prefix + "NormalCertificate"
    runner.command([sys.executable, script("emit_lean_frames8_selected_top.py"),
                    "--input", prepared, "--output", module_path(formal, top_module),
                    "--module", top_module])
    runner.command([sys.executable, script("emit_lean_frames8_selected_normals.py"),
                    "--input", prepared, "--output", module_path(formal, normal_module),
                    "--module", normal_module, "--top-module", top_module])
    runner.command([sys.executable, script("emit_lean_frames8_selected_top_registry.py"),
                    "--input", prepared,
                    "--output", module_path(formal, top_prefix + "TopRegistry"),
                    "--module", top_prefix + "TopRegistry",
                    "--normal-module", normal_module])


def emit_row_modules(runner: Runner, row_dir: Path, formal: Path,
                     top_prefix: str, row: int, chunks: dict) -> None:
    prepared = row_dir / "prepared.json"
    prefix = f"PrimitiveAffineEightFrameRow{row}"
    top_module = top_prefix + "TopCertificate"
    representation = prefix + "ModuleRepresentation"
    induced = prefix + "InducedBinding"
    orbits = prefix + "ModuleOrbits"
    registry = prefix + "ModuleRegistry"
    runner.command([sys.executable,
                    script("emit_lean_frames8_selected_module_representation.py"),
                    "--input", prepared, "--output", module_path(formal, representation),
                    "--module", representation, "--top-module", top_module])
    runner.command([sys.executable,
                    script("emit_lean_frames8_selected_induced_binding_general.py"),
                    "--input", prepared, "--output", module_path(formal, induced),
                    "--module", induced, "--representation-module", representation,
                    "--top-module", top_module])
    runner.command([sys.executable,
                    script("emit_lean_frames8_selected_module_orbits_split.py"),
                    "--input", prepared, "--output-dir", formal,
                    "--module", orbits, "--representation-module", representation,
                    "--top-module", top_module,
                    "--chunk-size", chunks["orbit_chunk_size"]])
    runner.command([sys.executable,
                    script("emit_lean_frames8_selected_module_registry_split.py"),
                    "--input", prepared, "--output-dir", formal,
                    "--module", registry, "--representation-module", representation,
                    "--orbits-module", orbits, "--top-module", top_module,
                    "--chunk-size", chunks["registry_chunk_size"]])


def execute_group(runner: Runner, config: dict, group: dict,
                  output_root: Path, formal: Path, phase: str) -> None:
    group_dir = output_root / group["key"]
    shared = group_dir / "shared"
    chunks_dir = shared / "normal-chunks"
    representative = group["representative_row"]
    top_prefix = f"PrimitiveAffineEightFrameTop{group['top_id']}"
    staged = script("prepare_frames8_grouped_certificate_staged.py")
    if phase in ("inputs", "all"):
        if runner.execute:
            shared.mkdir(parents=True, exist_ok=True)
        runner.command([sys.executable,
                        script("export_frames8_selected_binding_python.py"),
                        "--row", representative, "--output", shared / "binding.json"],
                       supports_force=False)
        runner.command([sys.executable, staged, "top",
                        "--binding", shared / "binding.json",
                        "--output", shared / "top-structure.json", *limits(config)])
        if runner.execute:
            structure = json.loads((shared / "top-structure.json").read_text())
            state_count, class_count = structure["state_count"], structure["class_count"]
            require(structure["top_index"] == group["top_index"] and
                    structure["top_order"] == group["top_order"],
                    f"generated top disagrees with {group['key']}")
            for i in range(state_count):
                runner.command([sys.executable, staged, "normality",
                                "--top", shared / "top-structure.json", "--state", i,
                                "--output", chunks_dir / f"normality-{i}.json",
                                *limits(config)])
                runner.command([sys.executable, staged, "radical",
                                "--top", shared / "top-structure.json", "--state", i,
                                "--output", chunks_dir / f"radical-{i}.json",
                                *limits(config)])
                for j in range(class_count):
                    runner.command([sys.executable, staged, "transition",
                                    "--top", shared / "top-structure.json", "--state", i,
                                    "--class-index", j,
                                    "--output", chunks_dir / f"transition-{i}-{j}.json",
                                    *limits(config)])
        else:
            print(f"# for i in 0..<state_count({group['key']}): normality i; radical i")
            print(f"# for i,j in state_count×class_count({group['key']}): transition i j")
        runner.command([sys.executable, staged, "assemble-top",
                        "--top", shared / "top-structure.json", "--chunks", chunks_dir,
                        "--output", shared / "top-assembled.json"])
        for row in group["rows"]:
            row_dir = group_dir / f"row{row}"
            binding = row_dir / "binding.json"
            if row == representative:
                if runner.execute:
                    row_dir.mkdir(parents=True, exist_ok=True)
                    binding.write_bytes((shared / "binding.json").read_bytes())
                else:
                    print(f"cp {shared / 'binding.json'} {binding}")
            else:
                runner.command([sys.executable,
                                script("export_frames8_grouped_row_binding.py"),
                                "--row", row, "--top", shared / "top-assembled.json",
                                "--output", binding])
            runner.command([sys.executable,
                            script("export_frames8_orbit_certificate_selected.py"),
                            "--row", row, "--output", row_dir / "module.json"],
                           supports_force=False)
            runner.command([sys.executable, staged, "row",
                            "--top", shared / "top-assembled.json",
                            "--binding", binding, "--module", row_dir / "module.json",
                            "--output", row_dir / "prepared.json", *limits(config)])
    if phase in ("modules", "all"):
        emit_top_modules(runner, shared, formal, top_prefix)
        for row in group["rows"]:
            emit_row_modules(runner, group_dir / f"row{row}", formal,
                             top_prefix, row, config["lean_chunks"])
        rep_induced = f"PrimitiveAffineEightFrameRow{representative}InducedBinding"
        runner.command([sys.executable,
                        script("emit_lean_frames8_selected_stabilizer_generators.py"),
                        "--input", shared / "top-assembled.json",
                        "--module", top_prefix + "StabilizerGenerators",
                        "--induced-module", rep_induced,
                        "--top-module", top_prefix + "TopCertificate",
                        "--output", module_path(
                            formal, top_prefix + "StabilizerGenerators")],
                       supports_force=False)
        prepared_rows = [group_dir / f"row{row}" / "prepared.json"
                         for row in group["rows"]]
        generated_arguments: list[object] = [
            sys.executable,
            script("emit_lean_frames8_grouped_generated_table.py"),
            "--top-id", group["top_id"], "--output-dir", formal,
        ]
        for prepared in prepared_rows:
            generated_arguments.extend(["--row-input", prepared])
        runner.command(generated_arguments)

        local_normals = shared / "stabilizer-local-normals.json"
        normal_arguments: list[object] = [
            sys.executable,
            script("prepare_frames8_selected_stabilizer_normal_table.py"),
            "--output", local_normals, *limits(config),
        ]
        for prepared in prepared_rows:
            normal_arguments.extend(["--input", prepared])
        runner.command(normal_arguments)

        generated_data = top_prefix + "GeneratedData"
        local_normal_module = top_prefix + "LocalNormalTable"
        emit_normal_arguments: list[object] = [
            sys.executable,
            script("emit_lean_frames8_grouped_stabilizer_normals.py"),
            "--input", local_normals,
            "--output", module_path(formal, local_normal_module),
            "--module", local_normal_module,
            "--table-module", generated_data,
            "--top-data", generated_data + ".topData",
            "--stabilizer-module", top_prefix + "StabilizerGenerators",
        ]
        for row in group["rows"]:
            emit_normal_arguments.extend([
                "--row-data", generated_data + f".row{row}Data",
                "--row-local-map",
                f"PrimitiveAffineEightFrameRow{row}InducedBinding.sourceLocalMap",
            ])
        runner.command(emit_normal_arguments)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--output-root", type=Path, required=True,
                        help="scratch/certificate root outside the publication repository")
    parser.add_argument("--formal-output", type=Path, default=FORMAL)
    parser.add_argument("--group", action="append",
                        help="one of top8, top9, top10, top13, top15, top16, top17")
    parser.add_argument("--phase", choices=("inputs", "modules", "all"),
                        default="all")
    parser.add_argument("--execute", action="store_true",
                        help="execute serially; omission is a dry run")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    config = read_config(args.config.resolve())
    output_root = args.output_root.resolve()
    formal = args.formal_output.resolve()
    require(ROOT.resolve() not in output_root.parents and output_root != ROOT.resolve(),
            "generated inputs must stay outside the publication repository")
    selected = set(args.group or [g["key"] for g in config["groups"]])
    valid = {g["key"] for g in config["groups"]}
    require(selected <= valid, f"unknown group(s): {sorted(selected - valid)}")
    runner = Runner(args.execute, args.force)
    for group in config["groups"]:
        if group["key"] in selected:
            print(f"# {group['key']}: exact top {group['top_id']} order "
                  f"{group['top_order']}; rows {group['rows']}")
            execute_group(runner, config, group, output_root, formal, args.phase)
    print(f"# {runner.count} explicit sequential commands"
          + (" executed" if args.execute else " planned (dry run)"))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            subprocess.CalledProcessError, ValueError) as error:
        raise SystemExit(f"refused: {error}")
