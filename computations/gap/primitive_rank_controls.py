#!/usr/bin/env python3
"""Reject altered literal primitive/rank witnesses using the public checker."""
import argparse
import copy
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode = True
from finite_menu import gap_command, gap_literal, read_records, require, run_gap
from primitive_rank import DATA, prologue


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=DATA)
    parser.add_argument('--gap-command')
    parser.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    records = list(read_records(args.data))
    header = records[0]
    actions = [r for r in records if r['kind'] == 'action']
    command = gap_command(args.gap_command)
    cases = []

    def change(name, predicate, mutation):
        row = copy.deepcopy(next(r for r in actions if predicate(r)))
        mutation(row)
        cases.append((name, 'RPVerify(' + gap_literal(row) + ');\n'))

    change('wrong whole head', lambda r: r['catalogue'] == 'transitive' and r['degree'] == 2,
           lambda r: r.update(head2=r['head2'] + 1))
    change('omitted normal', lambda r: r['degree'] == 9 and r['catalogue'] == 'transitive',
           lambda r: r['normals'].pop())
    change('wrong relative head', lambda r: bool(r['normals']),
           lambda r: r['normals'][0].update(rank=r['normals'][0]['rank'] + 1))
    change('wrong literal action order', lambda r: r['degree'] == 2,
           lambda r: r.update(order=r['order'] + 1))
    change('composition chain skips simple layer',
           lambda r: r['catalogue'] == 'primitive' and r['degree'] == 4,
           lambda r: r['composition'].pop(1))
    change('incomplete actual block partition',
           lambda r: r.get('owner', {}).get('kind') == 'v4_blocks',
           lambda r: r['owner']['blocks'].pop())
    change('false semiregular witness', lambda r: 'semiregular' in r,
           lambda r: r.update(semiregular=list(range(1, r['degree'] + 1))))
    change('quotient cover loses its actual kernel', lambda r: r.get('socle_cover_degree', 0) > 1,
           lambda r: r.update(socle_cover_images=[list(range(1, r['socle_cover_degree'] + 1))
                                                for _ in r['socle_cover_images']]))
    cases.append(('missing classification slice', 'RPFinish(rec(kind:="footer",schema_version:=1,actions:=0));\n'))
    for name, body in cases:
        with tempfile.TemporaryDirectory(prefix='primitive-rank-negative-') as tmp:
            driver = Path(tmp) / 'negative.g'
            driver.write_text(prologue() + 'RPInit(' + gap_literal(header) + ');\n' + body + 'QUIT;\n')
            try:
                run_gap(command, driver, args.timeout)
            except ValueError as error:
                require('rank certificate:' in str(error), f'{name}: rejection must be semantic')
            else:
                raise ValueError(f'altered certificate was accepted: {name}')
        print(f'REJECTED {name}', flush=True)
    print(f'PASS PRIMITIVE RANK NEGATIVE CONTROLS: {len(cases)} rejected alterations')


if __name__ == '__main__':
    main()
