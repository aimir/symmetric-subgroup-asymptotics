#!/usr/bin/env python3
"""Read the one GL3 pilot receipt and report bounded invariant flags.

No group or subgroup discovery is performed. At most15*7*3*9 binary
coordinate tests are needed for each of the vector and dual-vector tests.
The result is untrusted witness preparation, not a proof.
"""
import argparse
import json
from pathlib import Path


def column(a, v):
    return sum((sum(((a >> (3*i+j)) & 1) * ((v >> j) & 1)
                    for j in range(3)) % 2) << i for i in range(3))


def row(v, a):
    return sum((sum(((v >> i) & 1) * ((a >> (3*i+j)) & 1)
                    for i in range(3)) % 2) << j for j in range(3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    if receipt["ambient_order"] != 168 or len(receipt["codes"]) != 168:
        raise RuntimeError("not the selected GL3(2) receipt")
    generators = receipt["row_generators"]
    if len(generators) != 15 or any(len(gs) != 3 for gs in generators):
        raise RuntimeError("selected15-by3 generator cap violated")
    flags = []
    for i, indices in enumerate(generators):
        matrices = [receipt["codes"][j] for j in indices]
        vector = next((v for v in range(1, 8) if all(column(a, v) == v for a in matrices)), None)
        covector = next((v for v in range(1, 8) if all(row(v, a) == v for a in matrices)), None)
        flags.append({"row": i, "order": receipt["row_orders"][i],
                      "fixed_vector": vector, "fixed_covector": covector})
    survivors = [f["row"] for f in flags
                 if f["fixed_vector"] is None and f["fixed_covector"] is None]
    if survivors != [4, 7, 14]:
        raise RuntimeError(f"unexpected candidate rows: {survivors}")
    print(json.dumps({"flags": flags, "candidate_irreducible_rows": survivors}, indent=2))


if __name__ == "__main__":
    main()
