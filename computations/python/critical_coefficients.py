#!/usr/bin/env python3
"""Exact critical-model coefficients and benchmark values, not subgroup counts.

Print a CSV table through --max-degree (default 24). With --check, first compare
the coefficient recurrence with the four-colour orbit sum, and the Gaussian
recurrence with its exact product formula. Only standard-library arithmetic
is used. No asymptotic assertion follows from these finite checks.
"""

import argparse
import csv
from fractions import Fraction
from math import factorial
import sys


def coefficients(limit):
    values = [Fraction(1)]
    for r in range(1, limit + 1):
        value = values[r - 1] / 2
        if r >= 2:
            value += values[r - 2] / 3
        if r >= 4:
            value += values[r - 4] / 96
        values.append(value / r)
    return values


def orbit_colour_sum(rank):
    """Keep the two degree-four action colours and their normalizers separate."""
    total = Fraction(0)
    for extraspecial in range(rank // 4 + 1):
        remainder = rank - 4 * extraspecial
        for klein in range(remainder // 2 + 1):
            for dihedral in range((remainder - 2 * klein) // 2 + 1):
                pairs = remainder - 2 * klein - 2 * dihedral
                denominator = (
                    2**pairs * factorial(pairs)
                    * 24**klein * factorial(klein)
                    * 8**dihedral * factorial(dihedral)
                    * 384**extraspecial * factorial(extraspecial)
                )
                total += Fraction(1, denominator)
    return total


def gaussian_rows(limit):
    rows = [[1]]
    for n in range(1, limit + 1):
        previous = rows[-1]
        rows.append(
            [1] + [previous[k] + 2**(n - k) * previous[k - 1]
                   for k in range(1, n)] + [1]
        )
    return rows


def gaussian_product(n, k):
    value = Fraction(1)
    for i in range(k):
        value *= Fraction(2 ** (n - i) - 1, 2 ** (k - i) - 1)
    if value.denominator != 1:
        raise ArithmeticError("Gaussian product did not yield an integer")
    return value.numerator


def finite_checks():
    c = coefficients(20)
    for rank in range(21):
        if c[rank] != orbit_colour_sum(rank):
            raise ArithmeticError(f"four-colour coefficient mismatch at rank {rank}")
    for n, row in enumerate(gaussian_rows(20)):
        if row != [gaussian_product(n, k) for k in range(n + 1)]:
            raise ArithmeticError(f"Gaussian product mismatch at rank {n}")
    if [sum(row) for row in gaussian_rows(4)] != [1, 2, 5, 16, 67]:
        raise ArithmeticError("small Gaussian totals disagree")
    print("PASS: four-colour coefficients and Gaussian product agree through rank 20.", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-degree", type=int, default=24)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_degree < 0:
        parser.error("--max-degree must be nonnegative")
    if args.check:
        finite_checks()
    rank_limit = args.max_degree // 2
    c = coefficients(rank_limit)
    gaussian = [sum(row) for row in gaussian_rows(rank_limit)]
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(["n", "rank", "parity", "G_rank", "coefficient", "benchmark_L"])
    for n in range(args.max_degree + 1):
        rank, parity = divmod(n, 2)
        coefficient = c[rank]
        if parity and rank:
            coefficient += c[rank - 1] / 6
        benchmark = factorial(n) * gaussian[rank] * coefficient
        if benchmark.denominator != 1:
            raise ArithmeticError(f"labelled benchmark not integral at degree {n}")
        writer.writerow([n, rank, parity, gaussian[rank], str(coefficient), benchmark.numerator])


if __name__ == "__main__":
    main()
