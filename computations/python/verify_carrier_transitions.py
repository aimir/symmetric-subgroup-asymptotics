#!/usr/bin/env python3
"""Verify the carrier menu reductions and the two rational cone certificates.

Only Python's standard library is needed. This proves the finite numerical
inequalities conditional on the local group profiles. The separate GAP
checker reconstructs those profiles from the literal action generators.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def require(condition, label):
    if not condition:
        raise ValueError(label)


def rational(pair):
    require(isinstance(pair, list) and len(pair) == 2
            and all(type(x) is int for x in pair) and pair[1] > 0,
            "invalid rational encoding")
    return F(*pair)


def support(row, c, g):
    k, n, m = row[:3]
    return max(c * d + g * e for d in range(k + 1)
               for e in range(m + 1) if d + e <= n)


def interaction(a, b):
    return max(support(a, *b[4:]), support(b, *a[4:]))


def quadratic(matrix, v):
    return sum(matrix[i][j] * v[i] * v[j]
               for i in range(len(v)) for j in range(len(v)))


def psd_rank(matrix):
    """Exact symmetric elimination; zero diagonal forces a zero residual row."""
    a = [row[:] for row in matrix]
    rank = 0
    for i in range(len(a)):
        pivot = a[i][i]
        require(pivot >= 0, "negative Schur-complement pivot")
        if pivot == 0:
            require(all(a[i][j] == 0 for j in range(i + 1, len(a))),
                    "zero diagonal with a nonzero residual row")
            continue
        rank += 1
        for j in range(i + 1, len(a)):
            for k in range(i + 1, len(a)):
                a[j][k] -= a[j][i] * a[i][k] / pivot
    return rank


def verify(data, alphabet):
    checks = 0

    def check(condition, label):
        nonlocal checks
        checks += 1
        require(condition, label)

    check(data['schema_version'] == 1, "schema version")
    check(data['row_fields'] == ['k', 'n', 'm', 'a2', 'c', 'g'], "row fields")
    menus = data['menus']
    check([len(menus[k]) for k in ('H16', 'X', 'J', 'P')] == [12, 9, 10, 10],
          "41-row menu dimensions")
    for menu in menus.values():
        for row in menu:
            check(len(row) == 6 and all(type(v) is int and v >= 0 for v in row),
                  "nonnegative integer row")
    masters = data['masters']
    check([r['action_id'] for r in masters] ==
          ['8T26', '8T27', '8T35', '16T1082', '16T1083', '16T1084', '16T1332', '16T1547'],
          "exact master alphabet")
    check(sum(e['multiplicity'] for r in masters for e in r['profile']) ==
          data['normal_kernel_count'] == 14008, "complete profile multiplicity")
    for r, key in zip(masters[:3], ('X', 'J', 'P')):
        check([e['row'] for e in r['profile']] == menus[key], "degree-eight row profile")
    raw = sorted({tuple(e['row']) for r in masters[3:] for e in r['profile']})
    classes = data['h16_dominance_classes']
    check(len(raw) == 52, "52 distinct degree-sixteen rows")
    check(sorted(tuple(row) for cl in classes for row in cl) == raw,
          "52-row domination partition")
    check(len(classes) == len(menus['H16']) == 12, "12 domination classes")

    def inflate(row):
        k, n, m, c, g = row
        return [k, n, m, m, c, g]

    raw6 = [inflate(row) for row in raw]
    deg8 = list({tuple(r) for key in ('X', 'J', 'P') for r in menus[key]})
    check(len(deg8) == 26, "26 distinct degree-eight rows")
    # Check old and new columns together. Mark domination is necessary
    # separately from pair-row domination; a2=m here is a GAP-checked bound.
    for representative, cl in zip(menus['H16'], classes):
        for row in cl:
            item = inflate(row)
            check(representative[0] >= item[0], "raw k domination")
            check(max(representative[2:4]) >= max(item[2:4]), "raw q domination")
            for column in raw6 + deg8:
                check(interaction(representative, column) >= interaction(item, column),
                      "raw row domination on every old and new column")

    rows = menus['H16'] + menus['X'] + menus['J'] + menus['P']
    scales = [2] * 12 + [1] * 29
    w = [[F(interaction(a, b), scales[i] * scales[j])
          for j, b in enumerate(rows)] for i, a in enumerate(rows)]
    k = [F(r[0], s) for r, s in zip(rows, scales)]
    q = [F(max(r[2:4]), s) for r, s in zip(rows, scales)]
    seven = data['seven_representatives']
    six = data['six_representatives']
    check(seven == [9, 20, 31, 32, 33, 37, 40], "seven representative indices")
    check(six == [9, 20, 31, 32, 33, 37], "six representative indices")
    for i in range(41):
        check(any(k[o] >= k[i] and q[o] >= q[i]
                  and all(w[o][j] >= w[i][j] for j in range(41)) for o in seven),
              "a simultaneous pair/k/q dominating representative exists")
    check(w[20] == w[40] and k[20] == k[40] and q[20] == q[40],
          "whole-X and whole-P may be merged")
    b = [[w[i][j] / 16 for j in six] for i in six]
    alpha, beta = [k[i] / 4 for i in six], [q[i] / 4 for i in six]
    check([[64 * x for x in r] for r in b] == data['pair_matrix_times_64'],
          "physical pair scaling")
    check(alpha == list(map(rational, data['alpha'])), "physical k scaling")
    check(beta == list(map(rational, data['beta'])), "physical q scaling")
    rt, tt = rational(data['reserves']['RT']), rational(data['reserves']['T2'])
    check((rt, tt) == (F(25, 82), F(29, 164)), "claimed cross and square reserves")

    def deficit(v, cone):
        p, x, y, slack = v[:6], v[6], v[7], v[8]
        total = sum(p)
        if cone == 'A':
            ell, j, rank = x, 2 * x + y, 2 * x + y + slack
            mark = sum(p[i] * (ell * (alpha[i] + beta[i]) + alpha[i] * y)
                       for i in range(6))
        else:
            ell, j, rank = F(x + y, 2), x, x + y + slack
            mark = ell * sum(p[i] * (alpha[i] + beta[i]) for i in range(6))
        ledger = ell * (F(rank, 2) - ell) + (j - ell) * (rank - j)
        benchmark = F((rank + total) ** 2, 4) - rt * rank * total / 4 - tt * total ** 2 / 16
        return benchmark - ledger - quadratic(b, p) / 2 - mark

    basis = [[F(i == j) for i in range(9)] for j in range(9)]
    for cone, expected_rank in [('A', 7), ('B', 8)]:
        diag = [5248 * deficit(v, cone) for v in basis]
        m = [[F(0) for _ in range(9)] for _ in range(9)]
        for i in range(9):
            m[i][i] = diag[i]
            for j in range(i):
                v = [basis[i][h] + basis[j][h] for h in range(9)]
                m[i][j] = m[j][i] = (5248 * deficit(v, cone) - diag[i] - diag[j]) / 2
        p = [[rational(x) for x in r] for r in data['cone_psd_parts'][cone]]
        check(len(p) == 9 and all(len(r) == 9 for r in p), "PSD dimensions")
        check(all(p[i][j] == p[j][i] for i in range(9) for j in range(9)), "PSD symmetry")
        for i in range(9):
            for j in range(9):
                check(m[i][j] - p[i][j] >= 0, "entrywise nonnegative cone remainder")
        check(psd_rank(p) == expected_rank, "exact PSD Schur decomposition")
        # Basis/pair polarization determines the entire homogeneous quadratic.
        for v in basis:
            check(quadratic(m, v) == 5248 * deficit(v, cone), "quadratic diagonal identity")

    actions = {f"{a['degree']}T{a['catalogue_locator'][1]}": a for a in alphabet['actions']}
    colours8 = ['8T18', '8T26', '8T27', '8T28', '8T29', '8T31', '8T35']
    colours16 = ['16T1082', '16T1083', '16T1084', '16T1332', '16T1547']
    check(sum(F(1, actions[x]['normalizer_order']) for x in colours8) == F(3, 64),
          "original degree-eight colour weight")
    check(sum(F(1, actions[x]['normalizer_order']) for x in colours16) == F(65, 688128),
          "original degree-sixteen colour weight")
    check(sum(F(1, actions[x]['normalizer_order']) for x in ['8T27', '8T28']) == F(1, 64),
          "J colours retain their original weights")
    check(sum(F(1, actions[x]['normalizer_order']) for x in ['8T18', '8T29', '8T31', '8T35']) == F(3, 128),
          "P colours retain their original weights")
    print(f"PASS CARRIER TRANSITIONS: {checks} exact assertions; 52-to-12-to-6; two PSD cones")
    print("SCOPE: conditional numerical proof; local group profiles require the separate GAP reconstruction")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=ROOT / 'certificates/data/carrier_transitions.json')
    parser.add_argument('--alphabet', type=Path, default=ROOT / 'certificates/data/base_alphabet.json')
    args = parser.parse_args()
    verify(json.loads(args.data.read_text()), json.loads(args.alphabet.read_text()))


if __name__ == '__main__':
    main()
