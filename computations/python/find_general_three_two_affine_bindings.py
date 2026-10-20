#!/usr/bin/env python3
"""Selected7/21/168 matrix-row bindings; no databases or bulk mode.

Reads the one GL3 receipt. The two literal target permutation tuples below
are the public SmallAffineSoluble8Row{1,2}Order.g0/g1 definitions. Output is
only untrusted conjugators and ordinary words; Lean must check both directions.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import time


class Bound:
    def __init__(self):
        self.operations = 0
        self.started = time.monotonic()

    def tick(self):
        self.operations += 1
        if self.operations > 2_000_000 or time.monotonic()-self.started > 5:
            raise RuntimeError("selected binding budget exceeded")

    def pmul(self, a, b):
        self.tick()
        return tuple(a[b[i]] for i in range(8))

    def pinv(self, a):
        return tuple(a.index(i) for i in range(8))

    def mmul(self, a, b):
        self.tick()
        return sum((sum(((a >> (3*i+k)) & 1) * ((b >> (3*k+j)) & 1)
                        for k in range(3)) % 2) << (3*i+j)
                   for i in range(3) for j in range(3))

    def matrix_perm(self, a):
        return tuple(sum((sum(((a >> (3*i+j)) & 1) * ((v >> j) & 1)
                             for j in range(3)) % 2) << i for i in range(3))
                     for v in range(8))

    def words(self, generators, identity, multiply, inverse):
        out = {identity: []}
        queue = deque([identity])
        signed = [(g, i, False) for i, g in enumerate(generators)]
        signed += [(inverse(g), i, True) for i, g in enumerate(generators)]
        while queue:
            a = queue.popleft()
            for g, i, inv in signed:
                b = multiply(a, g)
                if b not in out:
                    if len(out) >= 168:
                        raise RuntimeError("selected word group exceeds168 elements")
                    out[b] = out[a] + [[i, inv]]
                    queue.append(b)
        return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    if receipt["ambient_order"] != 168 or len(receipt["row_generators"]) != 15:
        raise RuntimeError("not the selected GL3 receipt")
    b = Bound()
    ident = tuple(range(8))
    t0 = (0, 6, 1, 7, 2, 4, 3, 5)
    t1 = (0, 3, 1, 2, 4, 7, 5, 6)
    results = []
    for row, targets, size in [(4, [t0], 7), (14, [t0, t1], 21)]:
        matrices = [receipt["codes"][j] for j in receipt["row_generators"][row]]
        source = [b.matrix_perm(a) for a in matrices]
        sw = b.words(source, ident, b.pmul, b.pinv)
        tw = b.words(targets, ident, b.pmul, b.pinv)
        if len(sw) != size or len(tw) != size:
            raise RuntimeError("selected literal groups have unexpected size")
        found = None
        for conjugator_index, conjugator_code in enumerate(receipt["codes"]):
            c = b.matrix_perm(conjugator_code)
            ci = b.pinv(c)
            images = [b.pmul(b.pmul(c, g), ci) for g in source]
            if all(g in tw for g in images):
                found = (c, ci, images, conjugator_index, conjugator_code)
                break
        if found is None:
            raise RuntimeError("no actual point conjugator found")
        c, ci, images, conjugator_index, conjugator_code = found
        results.append({"row": row, "target": f"SmallAffineSoluble8Row{1 if row == 4 else 2}Order",
                        "conjugator": c, "inverse": ci,
                        "conjugator_matrix_index": conjugator_index,
                        "conjugator_matrix_code": conjugator_code,
                        "forward_words": [tw[g] for g in images],
                        "backward_words": [sw[b.pmul(b.pmul(ci, g), c)] for g in targets]})
    codes = receipt["codes"]
    # Only168*at most168 tiny tests to obtain inverses; no table is emitted.
    inverse = {}
    for a in codes:
        inverse[a] = next(c for c in codes if b.mmul(a, c) == 273)
    row7 = [codes[j] for j in receipt["row_generators"][7]]
    full_words = b.words(row7, 273, b.mmul, lambda a: inverse[a])
    if len(full_words) != 168:
        raise RuntimeError("row7 did not generate actual GL3")
    print(json.dumps({"bindings": results,
                      "ambient_generators_in_row7": [full_words[a] for a in [275, 98]],
                      "operations": b.operations, "wall_seconds": time.monotonic()-b.started}, indent=2))


if __name__ == "__main__":
    main()
