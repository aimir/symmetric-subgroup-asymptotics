#!/usr/bin/env python3
"""Exhaustively count the isometries of the two critical binary quadratic models.

This finite linear check establishes the constant72 in the critical lift
bound. The actual group types and original normalizers are checked by the
pinned base-alphabet verifier; this program does not classify group actions.
"""
from itertools import product

def quadratic(v, dimension):
    return sum(((v >> i) & 1) * ((v >> (i + 1)) & 1)
               for i in range(0, dimension, 2)) % 2

def image(columns, v):
    out = 0
    for i, x in enumerate(columns):
        if (v >> i) & 1:
            out ^= x
    return out

def independent(columns):
    span = {0}
    for x in columns:
        if x in span:
            return False
        span |= {v ^ x for v in tuple(span)}
    return True

def verify(dimension, expected_gl, expected_orthogonal, expected_zeros):
    q = [quadratic(v, dimension) for v in range(1 << dimension)]
    linear = isometries = 0
    for columns in product(range(1, 1 << dimension), repeat=dimension):
        if not independent(columns):
            continue
        linear += 1
        if all(q[image(columns, v)] == q[v] for v in range(1 << dimension)):
            isometries += 1
    if (linear, isometries, q.count(0)) != (expected_gl, expected_orthogonal, expected_zeros):
        raise ValueError('critical quadratic model mismatch')
    return linear, isometries

if __name__ == '__main__':
    verify(2, 6, 2, 3)
    verify(4, 20160, 72, 10)
    print('PASS CRITICAL QUADRATIC: exhaustive GL(2,2), GL(4,2); orthogonal orders2 and72')
