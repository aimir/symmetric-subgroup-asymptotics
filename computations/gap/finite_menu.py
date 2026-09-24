#!/usr/bin/env python3
"""Export or independently replay the complete literal binary small-width menu.

The producer uses TransGrp to find representatives. The checker uses literal
permutations, all index-two kernels and all central-involution extensions;
it does not query TransGrp or NormalSubgroups. No formal verification is claimed.
"""

import argparse
import gzip
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading

ROOT = Path(__file__).resolve().parents[2]
GAP_DIR = ROOT / "computations/gap"
DEFAULT_DATA = ROOT / "certificates/data/binary_menu.jsonl.gz"
BASE_DATA = ROOT / "certificates/data/base_alphabet.json"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def gap_literal(value):
    if type(value) is bool:
        return str(value).lower()
    if type(value) is int:
        return str(value)
    if isinstance(value, str):
        require(value.isascii(), "GAP input strings must be ASCII")
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ",".join(map(gap_literal, value)) + "]"
    if isinstance(value, dict):
        require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", k) for k in value),
                "invalid certificate field name")
        return "rec(" + ",".join(k + ":=" + gap_literal(v) for k, v in value.items()) + ")"
    raise ValueError(f"unsupported certificate value {type(value).__name__}")


def gap_command(argument):
    if argument:
        command = shlex.split(argument)
    elif shutil.which("gap"):
        command = [shutil.which("gap")]
    elif shutil.which("sage"):
        command = [shutil.which("sage"), "--gap"]
    else:
        raise ValueError("GAP not found; use --gap-command '/path/to/sage --gap'")
    require(bool(command), "empty GAP command")
    return command


def prologue():
    return (
        'SizeScreen([1000000,1000000]);;\n'
        + 'Read(' + gap_literal(str(GAP_DIR / 'finite_entry_witnesses.g')) + ');;\n'
        + 'Read(' + gap_literal(str(GAP_DIR / 'finite_menu_coverage.g')) + ');;\n'
    )


def run_gap(command, driver, timeout, data_sink=None):
    """Stream data separately from progress; reject GAP's successful error exits."""
    errors = []
    passed = []
    timed_out = threading.Event()
    with subprocess.Popen(command + ["-q", "-T", str(driver)], stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, bufsize=1) as proc:
        def expire():
            timed_out.set()
            proc.kill()
        timer = threading.Timer(timeout, expire)
        timer.daemon = True
        timer.start()
        try:
            for line in proc.stdout:
                if line.startswith("DATA "):
                    require(data_sink is not None, "unexpected producer data in replay")
                    value = json.loads(line[5:])
                    data_sink(value)
                else:
                    print(line, end="", flush=True)
                    if re.search(r"\bError\b|Syntax warning|FAIL", line):
                        errors.append(line.strip())
                    if line.startswith("PASS "):
                        passed.append(line.strip())
            code = proc.wait()
        finally:
            timer.cancel()
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    require(not timed_out.is_set(), "GAP timeout")
    require(code == 0 and not errors, f"GAP failed ({code}): " + "; ".join(errors[-4:]))
    return passed


def read_records(path):
    with open(path, "rb") as raw:
        compressed = raw.read(2) == b"\x1f\x8b"
    opener = gzip.open if compressed else open
    with opener(path, "rt", encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            require(line.strip(), f"empty certificate line {number}")
            value = json.loads(line)
            require(isinstance(value, dict), f"record {number} must be an object")
            yield value


def export(args, command):
    output = args.output.resolve()
    require(args.force or not output.exists(), "output exists; use --force to replace it")
    output.parent.mkdir(parents=True, exist_ok=True)
    d16 = json.loads((ROOT / "certificates/data/degree16_quotient.json").read_text())
    d8 = json.loads((ROOT / "certificates/data/degree8_quotient_charts.json").read_text())
    widths = sorted(set(args.widths))
    require(widths and all(w in (2, 4, 8, 16) for w in widths), "unsupported widths")
    temporary = output.with_name(output.name + ".partial")
    require(not temporary.exists(), f"unfinished output exists: {temporary}")
    records = 0
    last = None
    try:
        with tempfile.TemporaryDirectory(prefix="binary-menu-export-") as tmp:
            driver = Path(tmp) / "export.g"
            driver.write_text(prologue() + "FCProduce(" + gap_literal(widths) + ","
                              + gap_literal(d16) + "," + gap_literal(d8) + ");\nQUIT;\n")
            with open(temporary, "wb") as raw:
                with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as packed:
                    def sink(value):
                        nonlocal records, last
                        require(value.get("kind") in ("header", "action", "footer"), "record kind")
                        if records == 0:
                            require(value["kind"] == "header", "header first")
                        require(last != "footer", "data after footer")
                        packed.write((json.dumps(value, separators=(",", ":"), sort_keys=True)
                                      + "\n").encode())
                        records += 1
                        last = value["kind"]
                    passed = run_gap(command, driver, args.timeout, sink)
        require(last == "footer" and any(p.startswith("PASS FINITE MENU EXPORT:") for p in passed),
                "missing final export verdict")
        os.replace(temporary, output)
        print(f"WROTE {output}: {records} records; {output.stat().st_size} compressed bytes")
    except BaseException:
        if temporary.exists():
            temporary.unlink()
        raise


def verify(args, command):
    path = args.input.resolve()
    expected_base = json.loads(BASE_DATA.read_text())
    if isinstance(expected_base, dict):
        expected_base = expected_base["actions"]
    iterator = iter(read_records(path))
    header = next(iterator, None)
    require(header is not None and header.get("kind") == "header", "header required")
    require(header.get("schema_version") == 1, "unsupported schema version")
    if not args.allow_partial:
        require(header.get("widths") == [2, 4, 8, 16], "complete widths required (or explicit --allow-partial)")
    with tempfile.TemporaryDirectory(prefix="binary-menu-verify-") as tmp:
        driver = Path(tmp) / "verify.g"
        with open(driver, "w") as stream:
            stream.write(prologue())
            stream.write("FCPinnedBase:=" + gap_literal(expected_base) + ";;\n")
            stream.write("FCVerifyBegin(" + gap_literal(header) + ");;\n")
            footer_seen = False
            for record in iterator:
                require(not footer_seen, "record after footer")
                kind = record.get("kind")
                require(kind in ("action", "footer"), "unexpected record kind")
                if kind == "action":
                    stream.write("FCVerifyAction(" + gap_literal(record) + ");;\n")
                else:
                    footer_seen = True
                    stream.write("FCVerifyEnd(" + gap_literal(record) + ");;\n")
            require(footer_seen, "footer required")
            stream.write("QUIT;\n")
        passed = run_gap(command, driver, args.timeout)
        require(any(p.startswith("PASS FINITE MENU VERIFY:") for p in passed),
                "missing final complete verification verdict")
    if args.allow_partial:
        print("SCOPE:", header["widths"], "(explicit partial-width replay)")



def export_alphabet(args, command):
    output = args.output.resolve()
    require(args.force or not output.exists(), "output exists; use --force to replace it")
    values = []
    with tempfile.TemporaryDirectory(prefix="binary-alphabet-") as tmp:
        driver = Path(tmp) / "alphabet.g"
        driver.write_text(prologue()
                          + 'FCEmit(rec(schema_version:=1,actions:=FEWBuildBaseAlphabet()));\n'
                          + 'Print("PASS BASE ALPHABET EXPORT\\n");\nQUIT;\n')
        passed = run_gap(command, driver, args.timeout, values.append)
    require(len(values) == 1 and "PASS BASE ALPHABET EXPORT" in passed, "alphabet export verdict")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(values[0], indent=2, sort_keys=True) + "\n")
    print(f"WROTE {output}: 17 literal base colours")


def controls(args, command):
    base = json.loads(BASE_DATA.read_text())["actions"]
    d16 = json.loads((ROOT / "certificates/data/degree16_quotient.json").read_text())
    d8 = json.loads((ROOT / "certificates/data/degree8_quotient_charts.json").read_text())
    with tempfile.TemporaryDirectory(prefix="binary-entry-controls-") as tmp:
        driver = Path(tmp) / "controls.g"
        driver.write_text(prologue()
                          + 'FEWSetBaseAlphabet(' + gap_literal(base) + ');;\n'
                          + 'FEWSetCharts(' + gap_literal(d16) + ',' + gap_literal(d8) + ');;\n'
                          + 'Read(' + gap_literal(str(GAP_DIR / 'finite_entry_witness_controls.g')) + ');;\n'
                          + 'FEWRunFocusedControls();;\nQUIT;\n')
        passed = run_gap(command, driver, args.timeout)
    require(any(p.startswith("PASS FINITE ENTRY CONTROLS:") for p in passed), "focused controls verdict")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap-command", help="executable command, without shell evaluation")
    parser.add_argument("--timeout", type=int, default=7200)
    sub = parser.add_subparsers(dest="mode", required=True)
    produce = sub.add_parser("export", help="produce a gzip JSONL certificate using TransGrp")
    produce.add_argument("--output", type=Path, default=DEFAULT_DATA)
    produce.add_argument("--widths", type=int, nargs="+", default=[2, 4, 8, 16])
    produce.add_argument("--force", action="store_true")
    replay = sub.add_parser("verify", help="replay literal witnesses and both coverage closures")
    replay.add_argument("--input", type=Path, default=DEFAULT_DATA)
    replay.add_argument("--allow-partial", action="store_true")
    alphabet = sub.add_parser("export-alphabet", help="produce a candidate literal base alphabet")
    alphabet.add_argument("--output", type=Path, required=True)
    alphabet.add_argument("--force", action="store_true")
    sub.add_parser("controls", help="bounded local API and conjugacy regression fixtures")
    args = parser.parse_args()
    try:
        require(args.timeout > 0, "timeout must be positive")
        command = gap_command(args.gap_command)
        if args.mode == "export":
            export(args, command)
        elif args.mode == "verify":
            verify(args, command)
        elif args.mode == "export-alphabet":
            export_alphabet(args, command)
        else:
            controls(args, command)
        return 0
    except (OSError, EOFError, ValueError, json.JSONDecodeError, StopIteration) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
