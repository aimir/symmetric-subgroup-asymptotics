#!/usr/bin/env python3
"""Check the original-width interfaces between the two pair-top certificates.

Run this together with pair_top_modules.py and gap/pair_top_check.py. This
cross-check binds their records and validates the literal averaging and pair
maps; it does not replace the complete module or character-kernel replays.
"""
import argparse
from collections import Counter, defaultdict
import gzip
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from pair_top_modules import basis, remainder, tables, require

ROOT = Path(__file__).resolve().parents[2]


def stream(path):
    with gzip.open(path, 'rt') as f:
        return [json.loads(line) for line in f]


def apply(rows, vector):
    value = 0
    for i, row in enumerate(rows):
        if vector >> i & 1:
            value ^= row
    return value


def check(actions, modules, groups):
    ids = [a['id'] for a in actions]
    require(len(ids) == 391 and len(set(ids)) == 391, 'complete literal action domain')
    require([m['id'] for m in modules] == ids == [g['id'] for g in groups], 'same complete ordered domain')
    expected = {'twelve': (301, 12, 24), 'paired8': (24, 8, 32),
                'zero16': (29, 16, 32), 'two_affine16': (15, 16, 32),
                'primitive16': (20, 16, 32), 'paired6': (2, 6, 24)}
    require(Counter(a['family'] for a in actions) == Counter({f: x[0] for f, x in expected.items()}), 'six exact domains')
    partition, normal_counts = defaultdict(list), Counter()
    checks = 0
    for a, m, g in zip(actions, modules, groups):
        _, degree, width = expected[a['family']]
        require(a['degree'] == degree and a['original_width'] == width, 'original physical width')
        require(m['degree'] == degree and m['generators'] == a['generators'] == g['generators'], 'same actual ordered generator maps')
        normal_counts[a['family']] += len(g['normals'])
        require(all(len(n['word']) <= a['kappa'] for n in g['normals']), 'same action prefix bound')
        if a['family'] == 'twelve':
            partition[a['branch']].append(a['index'])
            joint = 5 ** (64 * a['kappa']) * 38 ** (192 * m['section_cap']) <= 2 ** (24 * width - 3) * 25 ** (192 * m['section_cap'])
            require(joint == (a['branch'] == 'joint'), 'width24 exact sufficient predicate')
        if a.get('branch') == 'ternary':
            b = g['structure']['ternary_blocks']
            rows = g['structure']['averaging_rows']
            require(sorted(map(len, b)) == [3] * 4 and sorted(sum(b, [])) == list(range(1, 13)), 'four actual triples')
            require(len(rows) == 12 and all(type(x) is int and 0 <= x < 4096 for x in rows), 'literal averaging map')
            require(rows == [sum(1 << (j - 1) for j in next(c for c in b if i in c)) for i in range(1, 13)], 'averaging uses its actual orbit')
            require(len(basis(rows)) == 4 and all(apply(rows, x) == x for x in rows), 'idempotent rank4, kernel dimension8')
            ts = tables(a['generators'], 12)
            for p, t in zip(a['generators'], ts):
                require({tuple(sorted(p[j - 1] for j in c)) for c in b} == {tuple(c) for c in b}, 'original action permutes triples')
                require(all(apply(rows, t[1 << i]) == t[rows[i]] for i in range(12)), 'equivariant averaging on original generators')
            # Its actual kernel is the direct sum of the four even-sum planes.
            kernel = basis((1 << (c[0] - 1)) ^ (1 << (j - 1)) for c in b for j in c[1:])
            require(len(kernel) == 8 and all(apply(rows, x) == 0 for x in kernel), 'literal eight-dimensional kernel')
        if a.get('branch') == 'paired':
            b = g['structure']['pair_blocks']
            images = g['structure']['top_images']
            require(sorted(map(len, b)) == [2] * 6 and sorted(sum(b, [])) == list(range(1, 13)), 'six actual pairs')
            require(len(images) == len(a['generators']), 'all actual generator images')
            for p, q in zip(a['generators'], images):
                require(sorted(q) == list(range(1, 7)), 'literal six-point image')
                require(all(sorted(p[j - 1] for j in c) == b[q[i] - 1] for i, c in enumerate(b)), 'original pair map compatibility')
        checks += 1
    require({k: len(v) for k, v in partition.items()} == {'joint': 283, 'core': 8, 'ternary': 8, 'paired': 2}, 'complete width24 partition')
    require(partition['core'] == [10, 32, 48, 136, 137, 138, 139, 140], 'eight core interfaces')
    require(partition['ternary'] == [37, 77, 117, 168, 210, 214, 242, 261], 'eight averaging interfaces')
    require(partition['paired'] == [195, 236], 'two paired-six interfaces')
    require(normal_counts == Counter(twelve=3914, paired8=147, zero16=349,
                                    two_affine16=95, primitive16=101, paired6=17), 'all original top normals, separately retained')
    # These certify the numerical branches of the universal lifting lemmas,
    # not those mathematical lemmas themselves.
    for width, linear_binary, prefix, tail in [
            (24, 0, 1, 3), (24, 2, 0, 3), (24, 0, 0, 4),
            (32, 0, 2, 4), (32, 0, 0, 6),
            (32, 3, 0, 4), (32, 4, 0, 2)]:
        require(2 ** (96 * linear_binary) * 5 ** (64 * prefix) * 38 ** (192 * tail)
                < 2 ** (24 * width - 3) * 25 ** (192 * tail), 'strict original-width character capacity')
        checks += 1
    require(5 ** 192 < 2 ** 573, 'three ordinary positions at width24')
    require(5 ** 64 < 2 ** 765 and 3 ** 128 < 2 ** 765, 'natural width32 menu')
    require(5 ** 320 < 2 ** 765, 'five ordinary positions at width32')
    require(5 ** 384 > 2 ** 765, 'six ordinary positions are insufficient')
    require(2 ** 384 * 38 ** 768 > 2 ** 765 * 25 ** 768, 'unsharpened rank4 mode is insufficient')
    print('PASS PAIR TOP INTERFACES:', checks + 5, 'action/interface and exact-capacity checks;', dict(normal_counts))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actions', type=Path, default=ROOT / 'certificates/data/pair_top_actions.json')
    p.add_argument('--modules', type=Path, default=ROOT / 'certificates/data/pair_top_modules.jsonl.gz')
    p.add_argument('--groups', type=Path, default=ROOT / 'certificates/data/pair_top_groups.jsonl.gz')
    args = p.parse_args()
    actions = json.loads(args.actions.read_text())['actions']
    require(actions == json.loads((ROOT / 'certificates/data/pair_top_actions.json').read_text())['actions'], 'committed literal domain')
    check(actions, stream(args.modules), stream(args.groups))
    print('SCOPE: finite interfaces only; classifications and all-original-normal lifting are separate mathematical inputs.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, EOFError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
