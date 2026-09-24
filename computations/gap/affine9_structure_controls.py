#!/usr/bin/env python3
"""Reject altered constructive affine-nine exhaustion witnesses."""
import argparse
import copy
import gzip
import json
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode = True
from finite_menu import gap_command, gap_literal, require, run_gap
from affine9_structure import DATA, ALPHABET, prologue


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data', type=Path, default=DATA)
    p.add_argument('--alphabet', type=Path, default=ALPHABET)
    p.add_argument('--gap-command')
    p.add_argument('--timeout', type=int, default=600)
    args = p.parse_args()
    with gzip.open(args.data, 'rt') as stream:
        data = json.load(stream)
    alphabet = json.loads(args.alphabet.read_text())
    command = gap_command(args.gap_command)
    cases = []

    def add(name, mutate):
        altered = copy.deepcopy(data)
        mutate(altered)
        cases.append((name, altered))

    def graphs(d):
        return [g for local in d['locals'] for normal in local['normals'] for g in normal['graphs']]

    add('missing adjoining element', lambda d: d['subgroups'][0]['edges'].pop())
    add('false natural irreducibility', lambda d: d['subgroups'][0].update(irreducible=not d['subgroups'][0]['irreducible']))
    add('missing local normal', lambda d: d['locals'][0]['normals'].pop())
    add('missing qualifying outer coset', lambda d: next(n for l in d['locals'] for n in l['normals'] if len(n['graphs']) > 1)['graphs'].pop())
    add('missing quotient involution', lambda d: next(g for g in graphs(d) if g['involutions'])['involutions'].pop())
    add('false nonsplit classification', lambda d: graphs(d)[0]['extensions'][0].update(nonsplit=not graphs(d)[0]['extensions'][0]['nonsplit']))
    add('wrong shared actual class', lambda d: graphs(d)[0]['extensions'][0].update(target='18A98'))
    add('wrong actual automorphism order', lambda d: graphs(d)[0].update(automorphism_order=graphs(d)[0]['automorphism_order'] + 1))
    for name, altered in cases:
        with tempfile.TemporaryDirectory(prefix='affine9-structure-negative-') as tmp:
            driver = Path(tmp) / 'negative.g'
            driver.write_text(prologue() + 'ASVerify(' + gap_literal(altered) + ',' + gap_literal(alphabet) + ');\nQUIT;\n')
            try:
                run_gap(command, driver, args.timeout)
            except ValueError as error:
                require('affine-nine structure:' in str(error), f'{name}: semantic rejection required')
            else:
                raise ValueError(f'altered certificate accepted: {name}')
        print(f'REJECTED {name}', flush=True)
    print(f'PASS AFFINE9 STRUCTURE NEGATIVE CONTROLS: {len(cases)} rejected alterations')


if __name__ == '__main__':
    main()
