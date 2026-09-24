#!/usr/bin/env python3
"""Literal c=1 regression fixtures using only Python's standard library.

Checks inverse-complement incidence for every subgroup of S3 and S4, the
shared-C3 A4-on-pairs external-mark fixture, and a nonsplit C9 character.
These finite cases guard hypotheses and multiplicities; they are not an
all-degree exhaustion theorem or a formal proof.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial


checks = 0


def check(condition, label):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(label)


def identity(n):
    return tuple(range(n))


def compose(p, q):
    """p after q."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    ans = [0] * len(p)
    for i, j in enumerate(p):
        ans[j] = i
    return tuple(ans)


def power(p, exponent):
    ans = identity(len(p))
    base = p
    while exponent:
        if exponent & 1:
            ans = compose(ans, base)
        base = compose(base, base)
        exponent >>= 1
    return ans


def order(p):
    e = identity(len(p))
    x = e
    for k in range(1, 10000):
        x = compose(x, p)
        if x == e:
            return k
    raise AssertionError("order loop")


def closure(n, generators):
    e = identity(n)
    gens = []
    for g in generators:
        if g not in gens:
            gens.append(g)
        gi = inverse(g)
        if gi not in gens:
            gens.append(gi)
    seen = {e}
    todo = deque([e])
    while todo:
        h = todo.popleft()
        for g in gens:
            z = compose(h, g)
            if z not in seen:
                seen.add(z)
                todo.append(z)
    return frozenset(seen)


def enumerate_subgroups(n, ambient):
    """Enumerate every subgroup of a finite permutation group."""
    egroup = frozenset({identity(n)})
    generators = {egroup: ()}
    todo = deque([egroup])
    ambient_sorted = sorted(ambient)
    while todo:
        hgroup = todo.popleft()
        hgens = generators[hgroup]
        for g in ambient_sorted:
            if g in hgroup:
                continue
            kgroup = closure(n, hgens + (g,))
            if kgroup not in generators:
                generators[kgroup] = hgens + (g,)
                todo.append(kgroup)
    return generators


def conjugate_subgroup(group, g):
    gi = inverse(g)
    return frozenset(compose(compose(g, h), gi) for h in group)


def normal_in(nsub, group):
    return all(conjugate_subgroup(nsub, g) == nsub for g in group)


def coset(nsub, x):
    return frozenset(compose(n, x) for n in nsub)


def power_of_three(value):
    exponent = 0
    while value > 1 and value % 3 == 0:
        value //= 3
        exponent += 1
    check(value == 1, "character count is a power of three")
    return exponent


def index_three_data(n, group, subgroup_generators):
    normals = []
    split = []
    nonsplit = []
    for nsub in subgroup_generators:
        if not nsub.issubset(group) or 3 * len(nsub) != len(group):
            continue
        if not normal_in(nsub, group):
            continue
        normals.append(nsub)
        x = next(g for g in group if g not in nsub)
        c1 = coset(nsub, x)
        c2 = coset(nsub, power(x, 2))
        q1 = sum(order(y) == 3 for y in c1)
        q2 = sum(order(y) == 3 for y in c2)
        check(q1 == q2, "inverse oriented cosets have equal complement count")
        if q1:
            split.append((nsub, q1))
        else:
            nonsplit.append(nsub)
    hom_count = 1 + 2 * len(normals)
    ns_count = 1 + 2 * len(nonsplit)
    d = power_of_three(hom_count)
    h = power_of_three(ns_count)
    sigma = hom_count - ns_count
    check(sigma == 2 * len(split), "split-character partition")
    check(sigma == 3**d - 3**h, "sigma=3^d-3^h")
    return d, h, sigma, split


def cycle_three_count(x):
    moved = sum(x[i] != i for i in range(len(x)))
    check(moved % 3 == 0, "order-three support divisible by three")
    return moved // 3


def verify_inverse_complement_incidence(m):
    ambient = frozenset(permutations(range(m)))
    subgroups = enumerate_subgroups(m, ambient)
    left = 0
    split_kernels = 0
    for group in subgroups:
        _d, _h, sigma, split = index_three_data(m, group, subgroups)
        left += sigma
        split_kernels += len(split)

    literal = Fraction(0)
    by_a_direct = Fraction(0)
    by_a_orbits = Fraction(0)
    order_three = [x for x in ambient if order(x) == 3]
    a_values = sorted({cycle_three_count(x) for x in order_three})

    for x in order_three:
        xgroup = frozenset({identity(m), x, power(x, 2)})
        for nsub in subgroups:
            if len(nsub.intersection(xgroup)) != 1:
                continue
            if conjugate_subgroup(nsub, x) != nsub:
                continue
            q = sum(order(y) == 3 for y in coset(nsub, x))
            check(q > 0, "marked representative makes q positive")
            literal += Fraction(1, q)

    for a in a_values:
        x = next(y for y in order_three if cycle_three_count(y) == a)
        ca = frozenset(y for y in ambient if compose(y, x) == compose(x, y))
        check(len(ca) == 3**a * factorial(a) * factorial(m - 3 * a),
              "centralizer order")
        xgroup = frozenset({identity(m), x, power(x, 2)})
        admissible = []
        for nsub in subgroups:
            if len(nsub.intersection(xgroup)) != 1:
                continue
            if conjugate_subgroup(nsub, x) != nsub:
                continue
            q = sum(order(y) == 3 for y in coset(nsub, x))
            admissible.append((nsub, q))
            by_a_direct += Fraction(1, len(ca) * q)

            cnx = frozenset(y for y in nsub if compose(y, x) == compose(x, y))
            normalizer = frozenset(
                y for y in ca if conjugate_subgroup(nsub, y) == nsub
            )
            check(q * len(cnx) >= len(nsub), "q >= [N:C_N(x)]")
            check(len(normalizer) >= 3 * len(cnx),
                  "centralizer normalizer contains <x>C_N(x)")
            check(Fraction(1, len(normalizer) * q) <= Fraction(1, 3 * len(nsub)),
                  "universal 1/(3|N|) relaxation")

        qmap = {nsub: q for nsub, q in admissible}
        unseen = set(qmap)
        while unseen:
            nsub = next(iter(unseen))
            orbit = {conjugate_subgroup(nsub, y) for y in ca}
            check(orbit.issubset(qmap), "C_a preserves admissibility")
            check(len({qmap[z] for z in orbit}) == 1, "q constant on C_a orbit")
            stabilizer = sum(conjugate_subgroup(nsub, y) == nsub for y in ca)
            check(len(orbit) * stabilizer == len(ca), "C_a orbit-stabilizer")
            by_a_orbits += Fraction(1, stabilizer * qmap[nsub])
            unseen.difference_update(orbit)

    check(literal == left, "literal inverse-q incidence")
    check(by_a_direct == Fraction(left, factorial(m)), "cycle-centralizer incidence")
    check(by_a_orbits == Fraction(left, factorial(m)), "centralizer-orbit incidence")
    check(left == 2 * split_kernels, "oriented split kernels counted twice")
    return len(subgroups), left


def permutation_parity(p):
    inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
    return inversions % 2


def induced_on_pairs(p, pairs):
    index = {pair: i for i, pair in enumerate(pairs)}
    return tuple(index[tuple(sorted((p[i], p[j])))] for i, j in pairs)


def disjoint_product(p, q):
    shift = len(p)
    return tuple(p) + tuple(shift + q[i] for i in range(len(q)))


def verify_shared_c3_external_mark():
    a4_nat = [p for p in permutations(range(4)) if permutation_parity(p) == 0]
    v4 = frozenset(p for p in a4_nat if order(p) <= 2)
    check(len(a4_nat) == 12 and len(v4) == 4, "A4/V4 orders")
    generator = next(p for p in a4_nat if order(p) == 3)
    quotient_cosets = [v4, coset(v4, generator), coset(v4, power(generator, 2))]
    check(len(set(quotient_cosets)) == 3, "A4/V4 quotient cosets")
    quotient_value = {a: value for value, c in enumerate(quotient_cosets) for a in c}

    pairs = tuple(combinations(range(4), 2))
    a4_six = {a: induced_on_pairs(a, pairs) for a in a4_nat}
    check(len(set(a4_six.values())) == 12, "A4-on-pairs action is faithful")
    check(len({a4_six[a][0] for a in a4_nat}) == 6, "A4-on-pairs action is transitive")

    bgen = (1, 2, 0)
    bpowers = [power(bgen, k) for k in range(3)]
    fibre_products = []
    sigma_sum = 0
    for theta in (1, 2):
        elements = []
        for k, bk in enumerate(bpowers):
            for a in a4_nat:
                if theta * k % 3 == quotient_value[a]:
                    elements.append(disjoint_product(bk, a4_six[a]))
        group = frozenset(elements)
        check(len(group) == 12, "A4-on-pairs fibre product order")
        check(closure(9, tuple(group)) == group, "A4-on-pairs fibre product is a group")
        kernel = frozenset(
            disjoint_product(bpowers[0], a4_six[a]) for a in v4
        )
        check(kernel.issubset(group) and len(kernel) == 4, "projection kernel V4")
        subgroups = enumerate_subgroups(9, group)
        d, h, sigma, _split = index_three_data(9, group, subgroups)
        check((d, h, sigma) == (1, 0, 2), "2-kernel split mark descent")
        sigma_sum += sigma
        fibre_products.append(group)
    check(fibre_products[0] != fibre_products[1], "oriented theta records are distinct")
    check(sigma_sum == (3**1 - 1) * (3**1 - 3**0), "A4-on-pairs double moment")


def main():
    for degree in (3, 4):
        groups, oriented_marks = verify_inverse_complement_incidence(degree)
        print(f"S{degree}: {groups} subgroups; {oriented_marks} oriented split marks; reciprocal-complement identities PASS.")
    verify_shared_c3_external_mark()
    print("Shared C3: two distinct A4-on-pairs fibre products, each with two surviving marks; joint count = 4.")
    generator = tuple(list(range(1, 9)) + [0])
    cyclic9 = closure(9, (generator,))
    subgroups = enumerate_subgroups(9, cyclic9)
    d, h, sigma, split = index_three_data(9, cyclic9, subgroups)
    check((d, h, sigma, len(split)) == (1, 1, 0, 0), "C9 has no split nonzero character")
    print("C9: d=1, h=1, surviving split characters = 0.")
    print(f"PASS: {checks} exact finite assertions.")


if __name__ == "__main__":
    main()
