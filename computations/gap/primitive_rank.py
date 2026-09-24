#!/usr/bin/env python3
"""Produce/replay literal rank and primitive certificates relative to pinned catalogues."""
import argparse
import gzip
import json
import os
from pathlib import Path
import tempfile
import sys
sys.dont_write_bytecode = True
from finite_menu import gap_command, gap_literal, read_records, require, run_gap

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/primitive_rank.jsonl.gz"
SOURCE = ROOT / "computations/gap/primitive_rank.g"


def prologue():
    return 'SizeScreen([1000000,1000000]);;\nRead(' + gap_literal(str(SOURCE)) + ');;\n'


def export(args, command):
    output = args.data.resolve()
    require(args.force or not output.exists(), 'output exists; use --force')
    temporary = output.with_name(output.name + '.partial')
    output.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    last = None
    with tempfile.TemporaryDirectory(prefix='primitive-rank-') as tmp:
        driver = Path(tmp) / 'export.g'
        driver.write_text(prologue() + 'RPProduce();\nQUIT;\n')
        with open(temporary, 'wb') as raw, gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as packed:
            def sink(value):
                nonlocal count, last
                require(value.get('kind') in ('header', 'action', 'footer'), 'record kind')
                require(count != 0 or value['kind'] == 'header', 'header first')
                require(last != 'footer', 'data after footer')
                packed.write((json.dumps(value, separators=(',', ':'), sort_keys=True) + '\n').encode())
                count += 1
                last = value['kind']
            passes = run_gap(command, driver, args.timeout, sink)
    require(last == 'footer' and any(p.startswith('PASS PRIMITIVE RANK EXPORT:') for p in passes), 'complete export verdict')
    os.replace(temporary, output)
    print(f'WROTE {count} records, {output.stat().st_size} compressed bytes: {output}')


def verify(args, command):
    records = read_records(args.data)
    with tempfile.TemporaryDirectory(prefix='primitive-rank-') as tmp:
        driver = Path(tmp) / 'verify.g'
        with driver.open('w') as out:
            out.write(prologue())
            first = next(records, None)
            require(first and first.get('kind') == 'header', 'header required')
            out.write('RPInit(' + gap_literal(first) + ');\n')
            seen_footer = False
            for value in records:
                require(not seen_footer, 'record after footer')
                if value.get('kind') == 'action':
                    out.write('RPVerify(' + gap_literal(value) + ');\n')
                else:
                    require(value.get('kind') == 'footer', 'action or footer required')
                    out.write('RPFinish(' + gap_literal(value) + ');\n')
                    seen_footer = True
            require(seen_footer, 'footer required')
            out.write('QUIT;\n')
        passes = run_gap(command, driver, args.timeout)
        require(any(p.startswith('PASS PRIMITIVE RANK VERIFY:') for p in passes), 'complete replay verdict')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['export', 'verify'])
    parser.add_argument('--data', type=Path, default=DATA)
    parser.add_argument('--force', action='store_true')
    parser.add_argument('--gap-command')
    parser.add_argument('--timeout', type=int, default=21600)
    args = parser.parse_args()
    command = gap_command(args.gap_command)
    (export if args.operation == 'export' else verify)(args, command)


if __name__ == '__main__':
    main()
