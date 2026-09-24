#!/usr/bin/env python3
"""Produce or replay complete binary permutation-module certificates.

Every vector is visited. Cyclic-sum closure proves the entire invariant
lattice, and its maximal intervals give all simple types. This does not
prove completeness of the supplied permutation-action classification.
"""
import argparse
import gzip
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]


def require(ok, why):
    if not ok:
        raise ValueError(why)


def basis(vectors):
    rows = {}
    for v in vectors:
        for p in sorted(rows, reverse=True):
            if v >> p & 1:
                v ^= rows[p]
        if v:
            p = v.bit_length() - 1
            for j in rows:
                if rows[j] >> p & 1:
                    rows[j] ^= v
            rows[p] = v
    return tuple(rows[p] for p in sorted(rows))


def remainder(v, b):
    for x in reversed(b):
        if v >> (x.bit_length() - 1) & 1:
            v ^= x
    return v


def coordinates(v, b):
    answer = 0
    for i in range(len(b) - 1, -1, -1):
        if v >> (b[i].bit_length() - 1) & 1:
            v ^= b[i]
            answer ^= 1 << i
    require(v == 0, 'coordinate outside actual module')
    return answer


def contained(c, b):
    return all(remainder(v, b) == 0 for v in c)


def tables(permutations, n):
    result = []
    for p in permutations:
        require(all(type(x) is int for x in p) and sorted(p) == list(range(1, n + 1)),
                'invalid literal permutation')
        tab = [0] * (1 << n)
        for v in range(1, 1 << n):
            low = v & -v
            tab[v] = tab[v ^ low] | 1 << (p[low.bit_length() - 1] - 1)
        result.append(tab)
    require(bool(result), 'nonempty original generator list')
    return result


def quotient(b, c, tabs):
    qb = basis(remainder(v, c) for v in b)
    require(len(qb) == len(b) - len(c), 'actual quotient dimension')
    return tuple(tuple(coordinates(remainder(t[v], c), qb) for v in qb) for t in tabs)


def homdim(a, x):
    d, e = len(a[0]), len(x[0])
    eq = []
    require(len(a) == len(x), 'same ordered generators in Hom equations')
    for g, h in zip(a, x):
        for i in range(d):
            for j in range(e):
                v = 0
                for k in range(d):
                    if g[i] >> k & 1:
                        v ^= 1 << (k * e + j)
                for k in range(e):
                    if h[k] >> j & 1:
                        v ^= 1 << (i * e + k)
                eq.append(v)
    return d * e - len(basis(eq))


def certificate(action):
    n = action['degree']
    require(n in (6, 8, 12, 16), 'module degree')
    tabs = tables(action['generators'], n)
    seen, cyclic = set(), set()
    for v in range(1 << n):
        if v in seen:
            continue
        orbit, queue = {v}, [v]
        for x in queue:
            for t in tabs:
                y = t[x]
                if y not in orbit:
                    orbit.add(y)
                    queue.append(y)
        seen.update(orbit)
        cyclic.add(basis(orbit))
    require(len(seen) == 1 << n, 'every binary vector visited')
    lattice, queue = {()}, [()]
    for b in queue:
        for c in sorted(cyclic, key=lambda q: (len(q), q)):
            d = basis(b + c)
            if d not in lattice:
                lattice.add(d)
                queue.append(d)
    bs = sorted(lattice, key=lambda q: (len(q), q))
    require(tuple(1 << i for i in range(n)) in lattice, 'full module present')
    mats, heads, comms = {}, [], {}
    for b in bs:
        require(all(remainder(t[v], b) == 0 for t in tabs for v in b), 'invariant numerator')
        mats[b] = quotient(b, (), tabs)
        comms[b] = basis(t[v] ^ v for t in tabs for v in b)
        heads.append(len(b) - len(comms[b]))
    types, intervals = [], []
    for ib, b in enumerate(bs):
        lowers = [(j, c) for j, c in enumerate(bs) if len(c) < len(b) and contained(c, b)]
        for ic, c in lowers:
            if any(len(c) < len(d) and contained(c, d) for _, d in lowers):
                continue
            x = quotient(b, c, tabs)
            matches = [j for j, y in enumerate(types) if len(x[0]) == len(y[0]) and homdim(x, y)]
            if not matches:
                types.append(x)
                matches = [len(types) - 1]
            intervals.append([ib, ic, matches[0]])
    cells, profiles, tau = [], [], 0
    for x in types:
        delta = len(x[0])
        end = homdim(x, x)
        require(end > 0 and delta % end == 0, 'simple commuting field')
        hs = [homdim(mats[b], x) for b in bs]
        require(all(h % end == 0 for h in hs), 'same-type multiplicities')
        if delta == 1:
            require(hs == heads, 'trivial Hom equals literal commutator head')
        tau = max(tau, (max(hs) + delta - 1) // delta)
        profiles.append([delta, end, delta // end, max(hs)])
        cells.append(hs)
    family = action['family']
    composition = [0] * len(types)
    chain = [len(bs) - 1]
    while chain[-1] != 0:
        edge = next(e for e in intervals if e[0] == chain[-1])
        composition[edge[2]] += 1
        chain.append(edge[1])
    require(sum(m * p[0] for m, p in zip(composition, profiles)) == n,
            'complete actual composition chain')
    composition_cap = max((m + p[2] - 1) // p[2] for m, p in zip(composition, profiles))
    if family in ('primitive16', 'two_affine16'):
        require(composition_cap <= 4, 'original composition Schur bound')
    if family == 'paired8' and action['index'] == 21:
        require(sorted([p[0], p[1], m] for p, m in zip(profiles, composition)) ==
                [[1, 1, 2], [3, 1, 1], [3, 1, 1]], 'actual two distinct projective three-types')
    if family in ('zero16', 'primitive16', 'two_affine16'):
        require(tau <= 4, 'original-width32 relative section cap')
    if family == 'paired6':
        require(tau == 1, 'six-point same-type section cap')
    triples = 0
    if family == 'paired8':
        require(max(heads) <= 2, 'paired-eight trivial head')
        require(all(p[3] <= p[0] for p in profiles if p[0] > 1), 'nontrivial Schur slot')
        special = [b for b, h in zip(bs, heads) if h == 2]
        require(len(special) <= 1, 'unique head-two numerator')
        for b in special:
            require(len(b) == 5 and remainder((1 << n) - 1, b) == 0, 'head-two shape')
            require(max(len(d) - len(basis(b + comms[d])) for d in bs if contained(b, d)) <= 1,
                    'same upper quotient above the head-two numerator')
        for k, hk in zip(bs, heads):
            for w, hw in zip(bs, heads):
                product = basis(x & y for x in k for y in w)
                for ell in bs:
                    if contained(product, ell):
                        q = len(ell) - len(basis(product + comms[ell]))
                        require(hk + hw + q <= 4, 'common-product denominator inequality')
                        triples += 1
    return dict(id=action['id'], degree=n, generators=action['generators'],
                numerators=bs, simple_intervals=intervals, simple_matrices=types,
                hom_dimensions=cells, trivial_heads=heads, schur_profiles=profiles,
                section_cap=tau, cyclic_count=len(cyclic), product_triples=triples,
                composition_chain=chain, composition_multiplicities=composition,
                composition_cap=composition_cap)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actions', type=Path, default=ROOT / 'certificates/data/pair_top_actions.json')
    p.add_argument('--data', type=Path, default=ROOT / 'certificates/data/pair_top_modules.jsonl.gz')
    p.add_argument('--produce', action='store_true')
    args = p.parse_args()
    actions = json.loads(args.actions.read_text())['actions']
    require(actions == json.loads((ROOT / 'certificates/data/pair_top_actions.json').read_text())['actions'],
            'exact committed literal action domain and generator order')
    require(len(actions) == 391 and len({a['id'] for a in actions}) == 391, 'complete supplied action domain')
    stored = []
    if not args.produce:
        with gzip.open(args.data, 'rt') as f:
            stored = [json.loads(line) for line in f]
        require([x['id'] for x in stored] == [a['id'] for a in actions], 'exact module record domain')
    result = []
    totals = {}
    for i, a in enumerate(actions):
        c = certificate(a)
        # Canonical JSON conversion changes tuples to lists without weakening equality.
        c = json.loads(json.dumps(c))
        if not args.produce:
            require(c == stored[i], 'module certificate mismatch: ' + a['id'])
        if a['family'] == 'twelve':
            accepted = 5 ** (64 * a['kappa']) * 38 ** (192 * c['section_cap']) <= 2 ** 573 * 25 ** (192 * c['section_cap'])
            require(accepted == (a['branch'] == 'joint'), 'exact original-width24 partition')
        t = totals.setdefault(a['family'], [0, 0, 0, 0, 0])
        for j, x in enumerate([1, len(c['numerators']), len(c['simple_intervals']),
                               sum(map(len, c['hom_dimensions'])), c['product_triples']]):
            t[j] += x
        result.append(c)
        if (i + 1) % 25 == 0 or i + 1 == len(actions):
            print('PAIR TOP MODULES', i + 1, '/', len(actions), flush=True)
    require(totals['twelve'][:4] == [301, 5044, 8483, 10960], 'complete degree12 totals')
    require(totals['zero16'][1] == 812, 'complete zero-ternary module total')
    require(totals['paired8'][1] == 170 and totals['paired8'][4] == 4479, 'paired-eight totals')
    if args.produce:
        args.data.parent.mkdir(parents=True, exist_ok=True)
        with args.data.open('wb') as f:
            with gzip.GzipFile(fileobj=f, mode='wb', filename='', mtime=0) as z:
                for c in result:
                    z.write((json.dumps(c, separators=(',', ':'), sort_keys=True) + '\n').encode())
    print('PASS PAIR TOP MODULES:', totals)
    print('SCOPE: complete modules of the supplied literal actions; action classification and universal lifts are separate.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, EOFError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
