#!/usr/bin/env python3
"""Produce or check all literal pair-top character menus using GAP.

Default verification uses supplied permutations and complete irreducible
kernel-intersection closure, without NormalSubgroups or a group catalogue.
--classifiers separately checks correspondence with published catalogues;
this is not a proof of those classifications.
"""
import argparse
import gzip
import json
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import threading

sys.dont_write_bytecode = True
from run_local_checks import gap_literal, require
from finite_menu import gap_command

ROOT = Path(__file__).resolve().parents[2]


def permutations(rows, degree):
    require(isinstance(rows, list), 'permutation list')
    for row in rows:
        require(isinstance(row, list) and all(type(i) is int for i in row)
                and sorted(row) == list(range(1, degree + 1)), 'invalid permutation or degree')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--gap-command')
    p.add_argument('--actions', type=Path, default=ROOT / 'certificates/data/pair_top_actions.json')
    p.add_argument('--data', type=Path, default=ROOT / 'certificates/data/pair_top_groups.jsonl.gz')
    p.add_argument('--produce', action='store_true')
    p.add_argument('--classifiers', action='store_true')
    p.add_argument('--constructors', action='store_true', help='rebuild all 24/29/15 imprimitive domains')
    p.add_argument('--construction-data', type=Path, default=ROOT / 'certificates/data/pair_top_constructions.json')
    p.add_argument('--timeout', type=int, default=7200)
    args = p.parse_args()
    require(args.timeout > 0, 'positive timeout')
    actions = json.loads(args.actions.read_text())['actions']
    baseline = json.loads((ROOT / 'certificates/data/pair_top_actions.json').read_text())['actions']
    require(actions == baseline, 'exact committed literal action domain and generator order')
    expected = {'twelve': 301, 'paired8': 24, 'zero16': 29, 'two_affine16': 15, 'primitive16': 20, 'paired6': 2}
    require({f: sum(a['family'] == f for a in actions) for f in expected} == expected
            and len(actions) == 391 and len({a['id'] for a in actions}) == 391, 'complete action domain')
    for a in actions:
        permutations(a['generators'], a['degree'])
        require(bool(a['generators']), 'nonempty original generators')
    records = []
    construction = None
    if args.constructors and not args.produce:
        construction = json.loads(args.construction_data.read_text())
        require(set(construction) == {'paired8', 'zero16', 'two_affine16'}, 'exact construction domains')
        by_id = {a['id']: a for a in actions}
        for family, rows in construction.items():
            require(isinstance(rows, list), 'construction witness list')
            for row in rows:
                require(row['id'] in by_id and by_id[row['id']]['family'] == family, 'construction literal action id')
                degree = by_id[row['id']]['degree']
                permutations(row['generators'], degree)
                permutations([row['conjugator']], degree)
    if not args.produce:
        with gzip.open(args.data, 'rt') as f:
            records = [json.loads(line) for line in f]
        require([r['id'] for r in records] == [a['id'] for a in actions], 'complete record domain')
        for a, r in zip(actions, records):
            require(r['generators'] == a['generators'], 'same original generator matrices')
            if a.get('branch') == 'paired':
                permutations([r['structure']['top_conjugator']], 6)
            for c in r['characters']:
                permutations(c['kernel_generators'], a['degree'])
                require(type(c['degree']) is int and c['degree'] > 0, 'positive character degree')
            for n in r['normals']:
                permutations(n['generators'], a['degree'])
                require(type(n['order']) is int and n['order'] > 0, 'positive normal order')
                require(isinstance(n['word'], list) and all(type(j) is int for j in n['word']), 'character word')
    with tempfile.TemporaryDirectory(prefix='pair-top-') as tmp:
        driver = Path(tmp) / 'driver.g'
        with driver.open('w') as f:
            f.write('Read(' + gap_literal(str(ROOT / 'computations/gap/pair_top_groups.g')) + ');\n')
            f.write('out:=OutputTextUser();;SetPrintFormattingStatus(out,false);;\n')
            f.write('Print("GAP_VERSION ",GAPInfo.Version,"\\n");\nPTNatural();\nPTTotal:=0;;\n')
            if args.constructors:
                f.write('Read(' + gap_literal(str(ROOT / 'computations/gap/pair_top_constructions.g')) + ');\n')
                f.write('PTCoverage:=PTConstructions(' + gap_literal(actions) + ');;\n')
                if args.produce:
                    f.write('PrintTo(out,"COVERAGE ",PTJSON(PTCoverage),"\\n");\n')
                else:
                    f.write('PTCheckConstructionWitnesses(' + gap_literal(actions) + ',' + gap_literal(construction) + ');\n')
            for i, a in enumerate(actions):
                f.write('a:=' + gap_literal(a) + ';;\n')
                if args.classifiers:
                    if a['family'] == 'twelve':
                        f.write('PTRequire(PTGroup(a.generators)=TransitiveGroup(12,a.index),"literal licensed degree12 action");\n')
                    elif a['family'] == 'primitive16':
                        f.write('PTRequire(IsConjugate(SymmetricGroup(16),PTGroup(a.generators),PrimitiveGroup(16,a.index)),"licensed primitive16 representation");\n')
                    elif a['family'] == 'paired8' and a['index'] >= 18:
                        f.write('PTRequire(IsConjugate(SymmetricGroup(8),PTGroup(a.generators),PrimitiveGroup(8,a.index-17)),"licensed primitive8 representation");\n')
                if args.produce:
                    f.write('r:=PTProduce(a);;PTTotal:=PTTotal+PTCheck(a,r);;PrintTo(out,"DATA ",PTJSON(r),"\\n");\n')
                else:
                    f.write('PTTotal:=PTTotal+PTCheck(a,' + gap_literal(records[i]) + ');;\n')
            f.write('Print("PASS PAIR TOP COMPLETE: 391 actions; ",PTTotal," normals; ",PTChecks," assertions\\n");\n')
        cmd = gap_command(args.gap_command)
        require(bool(cmd), 'nonempty GAP command')
        process = subprocess.Popen(cmd + ['-q', '-T', str(driver)], stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, start_new_session=True)
        timed_out = threading.Event()

        def stop():
            if process.poll() is None:
                timed_out.set()
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

        timer = threading.Timer(args.timeout, stop)
        timer.daemon = True
        timer.start()
        messages, produced, constructed = [], [], []
        try:
            for line in process.stdout:
                if line.startswith('DATA '):
                    produced.append(json.loads(line[5:]))
                elif line.startswith('COVERAGE '):
                    constructed.append(json.loads(line[9:]))
                else:
                    print(line, end='', flush=True)
                    messages.append(line)
            code = process.wait()
        finally:
            timer.cancel()
            if process.poll() is None:
                stop()
                process.wait()
        output = ''.join(messages)
        require(not timed_out.is_set(), 'GAP timeout')
        require(code == 0 and not re.search(r'\bError\b|Syntax warning|FAIL', output), 'GAP failure')
        require('PASS PAIR TOP COMPLETE: 391 actions;' in output, 'incomplete GAP execution')
        if args.constructors:
            require('PASS PAIR TOP CONSTRUCTIONS:' in output, 'incomplete constructive coverage')
            if not args.produce:
                require('PASS PAIR TOP CONSTRUCTION WITNESSES:' in output, 'incomplete retained construction maps')
        for a in actions:
            require('PASS PAIR TOP GROUP ' + a['id'] + ':' in output, 'missing action result')
    if args.produce:
        require([r['id'] for r in produced] == [a['id'] for a in actions], 'complete produced record domain')
        with args.data.open('wb') as f:
            with gzip.GzipFile(fileobj=f, mode='wb', filename='', mtime=0) as z:
                for r in produced:
                    z.write((json.dumps(r, separators=(',', ':'), sort_keys=True) + '\n').encode())
        if args.constructors:
            require(len(constructed) == 1, 'one complete construction transport dataset')
            args.construction_data.write_text(json.dumps(constructed[0], separators=(',', ':'), sort_keys=True) + '\n')
    print('SCOPE: all normal character menus of supplied actions; universal pair lifts and classification are separate.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, EOFError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
