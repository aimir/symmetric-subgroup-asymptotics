#!/usr/bin/env python3
"""Produce or verify retained carrier kernels and literal master quotient maps.

Verification does not call a group catalogue or NormalSubgroups. It checks
normal-list completeness by all central-involution quotient extensions.
--produce is the separate discovery mode and may call NormalSubgroups.
"""
import argparse
import gzip
import json
import os
from pathlib import Path
import re
import signal
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading

sys.dont_write_bytecode = True
from run_local_checks import gap_literal, require

ROOT = Path(__file__).resolve().parents[2]


def perm_rows(rows, degree, label, nonempty=False):
    require(isinstance(rows, list) and (bool(rows) or not nonempty), label + ': generator list required')
    for row in rows:
        require(isinstance(row, list) and all(type(x) is int for x in row)
                and sorted(row) == list(range(1, degree + 1)),
                label + ': invalid permutation row or degree')


def validate_inputs(alphabet, maps, records):
    require(isinstance(alphabet, dict) and isinstance(alphabet.get('actions'), list), 'alphabet object required')
    degrees = {}
    for a in alphabet['actions']:
        w = a.get('degree')
        require(type(w) is int and w in (2, 4, 8, 16), 'invalid base degree')
        locator = a.get('catalogue_locator')
        require(isinstance(locator, list) and len(locator) == 2 and locator[0] == w
                and all(type(x) is int and x > 0 for x in locator), 'invalid action locator')
        identifier = f'{w}T{locator[1]}'
        require(identifier not in degrees, 'duplicate action identifier')
        degrees[identifier] = w
        perm_rows(a.get('generators'), w, identifier + ' generators', True)
        perm_rows(a.get('normalizer_generators'), w, identifier + ' normalizer generators', True)
    require(isinstance(maps, dict) and maps.get('schema_version') == 1
            and maps.get('degree') == 8 and isinstance(maps.get('routes'), list), 'invalid map schema')
    for r in maps['routes']:
        require(r.get('source') in degrees and r.get('target') in degrees, 'unknown map action')
        require(degrees[r['source']] == degrees[r['target']] == 8, 'map degree mismatch')
        perm_rows(r.get('source_generator_images'), 8, 'map images', True)
        perm_rows(r.get('kernel_generators'), 8, 'map kernel')
        require(type(r.get('kernel_order')) is int and r['kernel_order'] > 0, 'invalid kernel order')
    for a in records:
        require(isinstance(a, dict) and a.get('action_id') in degrees
                and isinstance(a.get('normals'), list), 'invalid normal action record')
        w, count = degrees[a['action_id']], len(a['normals'])
        require(count > 0, 'empty normal list')
        for n in a['normals']:
            require(isinstance(n, dict), 'normal record must be an object')
            perm_rows(n.get('normal_generators'), w, 'normal generators')
            require(type(n.get('order')) is int and n['order'] > 0, 'invalid normal order')
            require(isinstance(n.get('row'), list) and len(n['row']) == 6
                    and all(type(x) is int and x >= 0 for x in n['row']), 'invalid six-parameter row')
            require(isinstance(n.get('children'), list)
                    and all(type(x) is int and 1 <= x <= count for x in n['children']),
                    'invalid normal-child index')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-command', help="e.g. 'gap' or 'sage --gap'; no shell is used")
    parser.add_argument('--produce', action='store_true', help='produce normal data using NormalSubgroups')
    parser.add_argument('--maps-only', action='store_true', help='check maps and original action weights only')
    parser.add_argument('--normals', type=Path, default=ROOT / 'certificates/data/carrier_normals.jsonl.gz')
    parser.add_argument('--transitions', type=Path, default=ROOT / 'certificates/data/carrier_transitions.json')
    parser.add_argument('--maps', type=Path, default=ROOT / 'certificates/data/carrier_master_maps.json')
    parser.add_argument('--alphabet', type=Path, default=ROOT / 'certificates/data/base_alphabet.json')
    parser.add_argument('--timeout', type=int, default=7200, help='GAP timeout in seconds')
    args = parser.parse_args()
    require(not (args.produce and args.maps_only), 'production and maps-only are separate modes')
    require(args.timeout > 0, 'timeout must be positive')
    if args.gap_command:
        command = shlex.split(args.gap_command)
    elif shutil.which('gap'):
        command = [shutil.which('gap')]
    elif shutil.which('sage'):
        command = [shutil.which('sage'), '--gap']
    else:
        raise ValueError("GAP not found; supply --gap-command 'sage --gap'")
    require(bool(command), 'empty GAP command')
    alphabet = json.loads(args.alphabet.read_text())
    expected_alphabet = json.loads((ROOT / 'certificates/data/base_alphabet.json').read_text())
    transitions = json.loads(args.transitions.read_text())
    maps = json.loads(args.maps.read_text())
    expected_ids = [r['action_id'] for r in transitions['masters']]
    require(expected_ids == ['8T26', '8T27', '8T35', '16T1082', '16T1083',
                             '16T1084', '16T1332', '16T1547'], 'exact master action domain required')
    records = []
    if not args.produce and not args.maps_only:
        with gzip.open(args.normals, 'rt') as stream:
            records = [json.loads(line) for line in stream if line.strip()]
        require([r['action_id'] for r in records] == expected_ids, 'normal action coverage/order mismatch')
    validate_inputs(alphabet, maps, records)
    with tempfile.TemporaryDirectory(prefix='subgroup-carriers-') as tmp:
        driver = Path(tmp) / 'driver.g'
        with driver.open('w') as stream:
            for name, data in [('CarrierAlphabet', alphabet), ('CarrierExpectedAlphabet', expected_alphabet),
                               ('CarrierTransitions', transitions), ('CarrierMaps', maps)]:
                stream.write(name + ':=' + gap_literal(data) + ';;\n')
            stream.write('Read(' + gap_literal(str(ROOT / 'computations/gap/carrier_groups.g')) + ');\n')
            stream.write('Print("GAP_VERSION ",GAPInfo.Version,"\\n");\n')
            stream.write('CCVerifyBase();\n')
            if args.produce:
                stream.write('CCProduce();\n')
            else:
                stream.write('CCVerifyMaps();\nCCTotals:=[0,0];;\n')
                for record in records:
                    stream.write('CCTotals:=CCTotals+CCVerifyNormals(' + gap_literal(record) + ');;\n')
                if not args.maps_only:
                    stream.write('CCRequire(CCTotals[1]=14008,"total literal kernels");\n')
                    stream.write('Print("PASS CARRIER COMPLETE: ",CCTotals,"; ",CCChecks," assertions\\n");\n')
        process = subprocess.Popen(command + ['-q', '-T', str(driver)], stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, start_new_session=True)
        timed_out = threading.Event()

        def stop_process():
            if process.poll() is None:
                timed_out.set()
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

        timer = threading.Timer(args.timeout, stop_process)
        timer.daemon = True
        timer.start()
        messages, produced = [], []
        try:
            for line in process.stdout:
                if line.startswith('DATA '):
                    record = json.loads(line[5:])
                    produced.append(record)
                else:
                    print(line, end='', flush=True)
                    messages.append(line)
            code = process.wait()
        finally:
            timer.cancel()
            if process.poll() is None:
                stop_process()
                process.wait()
        require(not timed_out.is_set(), f'GAP timeout after {args.timeout} seconds')
    output = ''.join(messages)
    require(code == 0 and not re.search(r'\bError\b|Syntax warning|FAIL', output), 'GAP failed')
    require('PASS CARRIER BASE:' in output, 'baseline action binding did not finish')
    if args.produce:
        require('PASS CARRIER PRODUCTION' in output, 'production did not finish')
        require([r['action_id'] for r in produced] == expected_ids, 'produced action coverage mismatch')
        require(sum(len(r['normals']) for r in produced) == 14008, 'produced normal count mismatch')
        args.normals.parent.mkdir(parents=True, exist_ok=True)
        with args.normals.open('wb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0) as stream:
                for record in produced:
                    stream.write((json.dumps(record, separators=(',', ':'), sort_keys=True) + '\n').encode())
        print('WROTE', args.normals)
    else:
        require('PASS CARRIER MAPS:' in output, 'map check did not finish')
        if not args.maps_only:
            require('PASS CARRIER COMPLETE:' in output, 'normal verification did not finish')
            for identifier in expected_ids:
                require('PASS CARRIER NORMALS ' + identifier + ':' in output,
                        'missing normal-profile result for ' + identifier)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, EOFError, KeyError, TypeError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
