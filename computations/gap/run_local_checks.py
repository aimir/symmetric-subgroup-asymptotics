#!/usr/bin/env python3
"""Run GAP verification of four literal quotient charts, without a catalogue scan.

Only Python's standard library is used for JSON decoding and subprocess control.
The independent algebraic checks are in verify_local_charts.g. Data are converted
into literal GAP records, not executed as GAP source. Run --help for options.
"""
import argparse
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def require(flag, message):
    if not flag:
        raise ValueError(message)


def permutations(data, key, degree):
    rows = data.get(key)
    require(isinstance(rows, list) and bool(rows), f"{key}: nonempty list required")
    expected = list(range(1, degree + 1))
    for row in rows:
        require(isinstance(row, list) and all(type(x) is int for x in row)
                and sorted(row) == expected, f"{key}: invalid degree-{degree} permutation")


def validate_inputs(d16, d8):
    require(isinstance(d16, dict) and isinstance(d8, dict), "JSON objects required")
    for key in ("source_generators", "image_generators", "kernel_generators"):
        permutations(d16, key, 16)
    require(d8.get("schema_version") == 1 and d8.get("degree") == 8, "degree8 schema mismatch")
    permutations(d8, "cover_generators", 8)
    charts = d8.get("charts")
    require(isinstance(charts, list) and len(charts) == 3, "exactly three degree8 charts required")
    for chart in charts:
        require(isinstance(chart, dict), "chart must be an object")
        for key in ("source_generators", "kernel_generators", "cover_kernel_generators"):
            permutations(chart, key, 8)
        for key in ("quotient_generators", "alpha_images", "beta_images"):
            permutations(chart, key, 16)


def gap_literal(value):
    if type(value) is int:
        return str(value)
    if isinstance(value, str):
        require(all(ord(c) < 128 for c in value), "only ASCII strings supported")
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ",".join(gap_literal(x) for x in value) + "]"
    if isinstance(value, dict):
        require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", k) for k in value),
                "invalid GAP record field")
        return "rec(" + ",".join(k + ":=" + gap_literal(v) for k, v in value.items()) + ")"
    raise ValueError(f"unsupported JSON value type: {type(value).__name__}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap-command", help="e.g. 'gap' or 'sage --gap'; no shell is used")
    parser.add_argument("--degree16", type=Path, default=ROOT / "certificates/data/degree16_quotient.json")
    parser.add_argument("--degree8", type=Path, default=ROOT / "certificates/data/degree8_quotient_charts.json")
    parser.add_argument("--catalogue-locators", action="store_true",
                        help="also check transgrp/SmallGroup identifiers; never a completeness proof")
    parser.add_argument("--timeout", type=int, default=120, help="subprocess timeout in seconds")
    args = parser.parse_args()
    try:
        if args.gap_command:
            command = shlex.split(args.gap_command)
        elif shutil.which("gap"):
            command = [shutil.which("gap")]
        elif shutil.which("sage"):
            command = [shutil.which("sage"), "--gap"]
        else:
            raise ValueError("GAP not found; supply --gap-command 'sage --gap' or a GAP path")
        require(bool(command) and args.timeout > 0, "nonempty GAP command and positive timeout required")
        d16 = json.loads(args.degree16.read_text())
        d8 = json.loads(args.degree8.read_text())
        validate_inputs(d16, d8)
        with tempfile.TemporaryDirectory(prefix="subgroup-charts-") as tmp:
            driver = Path(tmp) / "driver.g"
            driver.write_text(
                "Degree16Data:=" + gap_literal(d16) + ";;\n"
                "Degree8Data:=" + gap_literal(d8) + ";;\n"
                "CheckCatalogueLocators:=" + str(args.catalogue_locators).lower() + ";;\n"
                'Print("GAP_VERSION ",GAPInfo.Version,"\\n");\n'
                + "Read(" + gap_literal(str(ROOT / "computations/gap/verify_local_charts.g")) + ");\n"
                + "Read(" + gap_literal(str(ROOT / "computations/gap/verify_shared_source_moment.g")) + ");\n"
            )
            result = subprocess.run(command + ["-q", "-T", str(driver)], capture_output=True,
                                    text=True, timeout=args.timeout, check=False)
        output = result.stdout + result.stderr
        print(output, end="" if output.endswith("\n") else "\n")
        required = ["PASS DEGREE16:", "PASS LOCAL CHARTS:", "PASS SHARED SOURCE:"] + [f"PASS DEGREE8 CHART {i}:" for i in (1, 2, 3)]
        if args.catalogue_locators:
            required.append("PASS OPTIONAL CATALOGUE LOCATORS")
        require(result.returncode == 0, f"GAP exit status {result.returncode}")
        require(not re.search(r"\bError\b|Syntax warning|FAIL", output), "GAP reported an error or warning")
        require(all(marker in output for marker in required), "missing required final GAP PASS marker")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
