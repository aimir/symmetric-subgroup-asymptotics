#!/usr/bin/env python3
"""Produce or replay constructive two-block affine-nine action coverage."""
import argparse
import gzip
import json
import os
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode = True
from finite_menu import gap_command, gap_literal, require, run_gap
ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'certificates/data/affine9_structure.json.gz'
ALPHABET = ROOT / 'certificates/data/nonbinary_affine9_actions.json'
SOURCE = ROOT / 'computations/gap/affine9_structure.g'


def prologue():
    return 'SizeScreen([1000000,1000000]);;\nRead(' + gap_literal(str(SOURCE)) + ');;\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('operation', choices=['export', 'verify'])
    p.add_argument('--data', type=Path, default=DATA)
    p.add_argument('--alphabet', type=Path, default=ALPHABET)
    p.add_argument('--gap-command')
    p.add_argument('--timeout', type=int, default=21600)
    p.add_argument('--force', action='store_true')
    args = p.parse_args()
    alphabet = json.loads(args.alphabet.read_text())
    command = gap_command(args.gap_command)
    with tempfile.TemporaryDirectory(prefix='affine9-structure-') as tmp:
        driver = Path(tmp) / 'driver.g'
        if args.operation == 'export':
            require(args.force or not args.data.exists(), 'output exists; use --force')
            driver.write_text(prologue() + 'ASProduce(' + gap_literal(alphabet) + ');\nQUIT;\n')
            values = []
            passed = run_gap(command, driver, args.timeout, values.append)
            require(len(values) == 1 and any(x.startswith('PASS AFFINE9 STRUCTURE EXPORT:') for x in passed), 'complete structural export')
            temporary = args.data.with_name(args.data.name + '.partial')
            with open(temporary, 'wb') as raw, gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as packed:
                packed.write((json.dumps(values[0], separators=(',', ':'), sort_keys=True) + '\n').encode())
            os.replace(temporary, args.data)
            print(f'WROTE {args.data}: {args.data.stat().st_size} compressed bytes')
        else:
            with gzip.open(args.data, 'rt') as stream:
                value = json.load(stream)
            driver.write_text(prologue() + 'ASVerify(' + gap_literal(value) + ',' + gap_literal(alphabet) + ');\nQUIT;\n')
            passed = run_gap(command, driver, args.timeout)
            require(any(x.startswith('PASS AFFINE9 STRUCTURE VERIFY:') for x in passed), 'complete structural replay')


if __name__ == '__main__':
    main()
