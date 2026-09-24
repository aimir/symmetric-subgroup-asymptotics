#!/usr/bin/env python3
"""Verify or regenerate literal nonbinary finite certificates.

The default verifier uses no group catalogue and no NormalSubgroups call.
--catalogue additionally matches the complete pinned TransGrp degree-16 slice.
--produce is a separate discovery mode; it may enumerate normal subgroups.
"""
import argparse
import gzip
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading

sys.dont_write_bytecode = True
from run_local_checks import gap_literal, require

ROOT = Path(__file__).resolve().parents[2]
DATA_ROOT = ROOT / 'certificates/data'
HEAD_IDS = {1071, 1542, 1543, 1544, 1546, 1767, 1815}
COMPARATOR_IDS = {1298, 1921}


def integer(value, minimum=0):
    return type(value) is int and value >= minimum


def perm(row, degree, label):
    require(isinstance(row, list) and all(type(x) is int for x in row)
            and sorted(row) == list(range(1, degree + 1)), label + ': invalid permutation or degree')


def perms(rows, degree, label, nonempty=False):
    require(isinstance(rows, list) and (bool(rows) or not nonempty), label + ': generator list required')
    for row in rows:
        perm(row, degree, label)


def index(value, count, label):
    require(integer(value, 1) and value <= count, label + ': invalid one-based index')


def indices(values, count, label):
    require(isinstance(values, list), label + ': list required')
    for value in values:
        index(value, count, label)


def cyclo(value):
    if type(value) is int:
        return
    require(isinstance(value, dict) and integer(value.get('conductor'), 1), 'invalid cyclotomic conductor')
    coeffs = value.get('coefficients')
    require(isinstance(coeffs, list) and len(coeffs) == value['conductor'], 'invalid cyclotomic coefficients')
    for pair in coeffs:
        require(isinstance(pair, list) and len(pair) == 2 and type(pair[0]) is int
                and integer(pair[1], 1), 'invalid rational coefficient')


def validate_alphabet(alphabet, expected, scope):
    require(alphabet.get('schema_version') == 1, 'invalid alphabet schema')
    require(alphabet.get('classification') == expected['classification'], 'classification slice metadata changed')
    actions = alphabet.get('actions')
    size, degree = (527, 16) if scope == 'degree16' else (98, 18)
    require(isinstance(actions, list) and len(actions) == size, 'wrong action count for scope')
    require([a.get('action_id') for a in actions] == [a['action_id'] for a in expected['actions']],
            'exact committed action domain/order required')
    counts = {'mixed': [0, 0], 'comparator': [0, 0], 'head': [0, 0]}
    for a in actions:
        if scope == 'degree16':
            locator = a.get('catalogue_locator')
            require(isinstance(locator, list) and len(locator) == 2 and locator[0] == 16
                    and integer(locator[1], 1), 'invalid original catalogue locator')
            require(a.get('action_id') == f'16T{locator[1]}', 'action identity mismatch')
            family = 'head' if locator[1] in HEAD_IDS else ('comparator' if locator[1] in COMPARATOR_IDS else 'mixed')
        else:
            require(integer(a.get('construction_index'), 1)
                    and a.get('action_id') == f'18A{a["construction_index"]}', 'invalid structural action index')
            family = 'mixed'
        require(a.get('degree') == degree, 'action degree mismatch')
        require(a.get('family') == family, 'wrong certificate family')
        for field in ('order', 'normalizer_order', 'normal_count'):
            require(integer(a.get(field), 1), 'invalid ' + field)
        perms(a.get('generators'), degree, 'original action', True)
        perms(a.get('normalizer_generators'), degree, 'original normalizer', True)
        counts[family][0] += 1
        counts[family][1] += a['normal_count']
    expected_counts = ({'mixed': [518, 8807], 'comparator': [2, 175], 'head': [7, 267]}
                       if scope == 'degree16' else {'mixed': [98, 1823], 'comparator': [0, 0], 'head': [0, 0]})
    require(counts == expected_counts,
            'wrong action/normal family partition')


def validate_record(record, action):
    require(record.get('schema_version') == 1 and record.get('action_id') == action['action_id'],
            'normal record identity mismatch')
    normals, classes, characters = (record.get(k) for k in ('normals', 'classes', 'characters'))
    require(isinstance(normals, list) and len(normals) == action['normal_count'], 'normal list count mismatch')
    require(isinstance(classes, list) and classes and isinstance(characters, list), 'class/character lists required')
    count = len(normals)
    atoms = record.get('atoms')
    indices(atoms, count, 'normal closure atoms')
    require(atoms == sorted(set(atoms)), 'normal closure atoms must be distinct and sorted')
    for c in classes:
        perm(c.get('representative'), action['degree'], 'class representative')
        require(integer(c.get('size'), 1), 'invalid class size')
        index(c.get('normal_closure'), count, 'class normal closure')
    for character in characters:
        require(integer(character.get('degree'), 1), 'invalid character degree')
        index(character.get('kernel'), count, 'character kernel')
        require(isinstance(character.get('values'), list) and len(character['values']) == len(classes),
                'character/class length mismatch')
        for value in character['values']:
            cyclo(value)
    for n in normals:
        perms(n.get('generators'), action['degree'], 'normal kernel')
        require(integer(n.get('order'), 1), 'invalid normal order')
        indices(n.get('joins'), count, 'join row')
        require(len(n['joins']) == len(atoms), 'incomplete join row')
        cert = n.get('certificate')
        require(isinstance(cert, dict), 'certificate required')
        kind = cert.get('kind')
        if kind == 'mixed':
            indices(cert.get('linear'), len(characters), 'linear tuple')
            indices(cert.get('general'), len(characters), 'general tuple')
        elif kind == 'comparator':
            require(action['family'] == 'comparator', 'comparator in wrong action')
        elif kind == 'head':
            require(action['family'] == 'head' and cert.get('model_type') in ('A', 'S'), 'invalid head model')
            require(integer(cert.get('model_rank'), 1) and cert['model_rank'] <= 3
                    and integer(cert.get('central_rank')), 'invalid head ranks')
            index(cert.get('central_preimage'), count, 'head central preimage')
            perms(cert.get('generator_images'), 4 * cert['model_rank'], 'head map images', True)
            require(len(cert['generator_images']) == len(action['generators']), 'head image alignment')
        else:
            raise ValueError('unknown certificate kind')
    if action['family'] == 'comparator':
        cmp = record.get('comparator')
        require(isinstance(cmp, dict), 'comparator map missing')
        index(cmp.get('kernel'), count, 'comparator kernel')
        perms(cmp.get('generator_images'), 8, 'comparator map images', True)
        require(len(cmp['generator_images']) == len(action['generators']), 'comparator image alignment')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-command', help="e.g. 'gap' or 'sage --gap'; no shell is used")
    parser.add_argument('--scope', choices=['degree16', 'affine9'], default='degree16')
    parser.add_argument('--alphabet', type=Path)
    parser.add_argument('--data', type=Path)
    parser.add_argument('--produce', action='store_true')
    parser.add_argument('--catalogue', action='store_true')
    parser.add_argument('--actions', help='comma-separated IDs for a clearly labelled partial check/production')
    parser.add_argument('--timeout', type=int, default=21600)
    args = parser.parse_args()
    require(not (args.produce and args.actions) or args.data is not None,
            'partial production requires an explicit --data output')
    prefix = 'nonbinary' if args.scope == 'degree16' else 'nonbinary_affine9'
    default_alphabet = DATA_ROOT / (prefix + '_actions.json')
    args.alphabet = args.alphabet or default_alphabet
    args.data = args.data or DATA_ROOT / (prefix + '_normals.jsonl.gz')
    require(args.timeout > 0, 'timeout must be positive')
    require(not (args.produce and args.catalogue), 'production and catalogue correspondence are separate modes')
    require(not args.catalogue or args.scope == 'degree16', 'affine9 is structural coverage, not catalogue coverage')
    if args.gap_command:
        command = shlex.split(args.gap_command)
    elif shutil.which('gap'):
        command = [shutil.which('gap')]
    elif shutil.which('sage'):
        command = [shutil.which('sage'), '--gap']
    else:
        raise ValueError('GAP not found; provide --gap-command')
    require(bool(command), 'empty GAP command')
    expected = json.loads(default_alphabet.read_text())
    alphabet = json.loads(args.alphabet.read_text())
    validate_alphabet(alphabet, expected, args.scope)
    expected_by_id = {a['action_id']: a for a in expected['actions']}
    selected = set(args.actions.split(',')) if args.actions else set(expected_by_id)
    require(selected and selected <= set(expected_by_id), 'unknown/empty selected action set')
    actions = [a for a in alphabet['actions'] if a['action_id'] in selected]
    records = []
    if not args.produce:
        with gzip.open(args.data, 'rt') as stream:
            records = [json.loads(line) for line in stream if line.strip()]
        record_ids = [r.get('action_id') for r in records]
        complete_ids = [a['action_id'] for a in alphabet['actions']]
        selected_ids = [a['action_id'] for a in actions]
        require(record_ids == complete_ids or (args.actions and record_ids == selected_ids),
                'normal stream must have the complete domain or the exact explicitly selected partial domain')
        validation_actions = alphabet['actions'] if record_ids == complete_ids else actions
        for record, action in zip(records, validation_actions):
            validate_record(record, action)
        records = {r['action_id']: r for r in records}
    with tempfile.TemporaryDirectory(prefix='subgroup-nonbinary-') as tmp:
        driver = Path(tmp) / 'driver.g'
        with driver.open('w') as stream:
            stream.write('Read(' + gap_literal(str(ROOT / 'computations/gap/nonbinary_groups.g')) + ');\n')
            stream.write('SizeScreen([1000000,1000000]);;\nNBOut:=OutputTextUser();;SetPrintFormattingStatus(NBOut,false);;\n')
            stream.write('NonbinaryAlphabet:=' + gap_literal(alphabet) + ';;\n')
            stream.write('Print("GAP_VERSION ",GAPInfo.Version,"\\n");\nNBTotals:=[0,0,0,0];;\n')
            if args.catalogue:
                stream.write('NBVerifyCatalogue();\n')
            for action in actions:
                if args.produce:
                    stream.write('PrintTo(NBOut,"DATA ",NBJSON(NBProduceAction(' + gap_literal(action) + ')),"\\n");\n')
                    stream.write('Print("PRODUCED NONBINARY ' + action['action_id'] + '\\n");\n')
                else:
                    stream.write('NBTotals:=NBTotals+NBVerifyAction(' + gap_literal(action) + ','
                                 + gap_literal(expected_by_id[action['action_id']]) + ','
                                 + gap_literal(records[action['action_id']]) + ');;\n')
            if args.produce:
                stream.write('Print("PASS NONBINARY PRODUCTION\\n");\n')
            elif args.actions:
                stream.write('Print("PASS NONBINARY PARTIAL: ",NBTotals,"; ",NBChecks," assertions\\n");\n')
            else:
                totals = [9249, 9107, 134, 8] if args.scope == 'degree16' else [1823, 1823, 0, 0]
                stream.write('NBRequire(NBTotals=' + gap_literal(totals) + ',"complete certificate partition");\n')
                stream.write('Print("PASS NONBINARY COMPLETE: ",NBTotals,"; ",NBChecks," assertions\\n");\n')
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
                    produced.append(json.loads(line[5:]))
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
    if args.produce:
        require('PASS NONBINARY PRODUCTION' in output, 'production did not finish')
        require([r['action_id'] for r in produced] == [a['action_id'] for a in actions], 'produced domain mismatch')
        for record, action in zip(produced, actions):
            validate_record(record, action)
        args.data.parent.mkdir(parents=True, exist_ok=True)
        with args.data.open('wb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0) as stream:
                for record in produced:
                    stream.write((json.dumps(record, sort_keys=True, separators=(',', ':')) + '\n').encode())
        print('WROTE', args.data)
    else:
        marker = 'PASS NONBINARY PARTIAL:' if args.actions else 'PASS NONBINARY COMPLETE:'
        require(marker in output, 'verification did not finish')
        if args.catalogue:
            require('PASS NONBINARY CATALOGUE:' in output, 'catalogue correspondence did not finish')
        for action in actions:
            require('PASS NONBINARY ACTION ' + action['action_id'] + ':' in output, 'missing action result')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, EOFError, KeyError, TypeError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
