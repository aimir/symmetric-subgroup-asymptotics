#!/usr/bin/env python3
"""Export one bounded primitive composition-density receipt chunk.

The source is the committed primitive_rank stream.  The exporter retains all
336 PrimGrp locators in degrees 2--44, their exact group orders, and the
3-adic order valuations.  Natural A_n/S_n rows are recognized by their exact
orders; every other row must pass the stronger order-valuation three-tenths
test outside the theorem's excluded degrees.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/primitive_rank.jsonl.gz"
FORMAL = ROOT / "formal/SymmetricSubgroupAsymptotics"
SPANS = ((2, 11), (12, 20), (21, 27), (28, 36), (37, 44))
NAMES = ("2To11", "12To20", "21To27", "28To36", "37To44")


def valuation_three(n: int) -> int:
    value = 0
    while n % 3 == 0:
        n //= 3
        value += 1
    return value


def all_rows() -> list[dict]:
    rows = []
    with gzip.open(DATA, "rt", encoding="utf-8") as source:
        for line in source:
            row = json.loads(line)
            if not (row.get("kind") == "action"
                    and row.get("catalogue") == "primitive"
                    and 2 <= row["degree"] <= 44):
                continue
            degree = row["degree"]
            order = row["order"]
            if degree >= 5 and order == math.factorial(degree) // 2:
                kind = "naturalAlternating"
            elif degree >= 5 and order == math.factorial(degree):
                kind = "naturalSymmetric"
            else:
                kind = "orderBound"
            value = valuation_three(order)
            if kind == "orderBound" and degree >= 4 and degree != 9:
                if 10 * value > 3 * degree:
                    raise RuntimeError(
                        f"order valuation fails at {degree}P{row['index']}")
            rows.append({"degree": degree, "index": row["index"],
                         "order": order, "value": value, "kind": kind})
    if len(rows) != 336:
        raise RuntimeError(f"expected 336 bounded primitive rows, got {len(rows)}")
    locators = [(r["degree"], r["index"]) for r in rows]
    if len(set(locators)) != len(locators):
        raise RuntimeError("duplicate primitive catalogue locator")
    if locators != sorted(locators):
        raise RuntimeError("primitive catalogue locators are not sorted")
    return rows


def render(chunk: int, rows: list[dict]) -> str:
    lo, hi = SPANS[chunk]
    selected = [r for r in rows if lo <= r["degree"] <= hi]
    name = NAMES[chunk]
    digest = hashlib.sha256(DATA.read_bytes()).hexdigest()
    entries = []
    for r in selected:
        if r["kind"] == "orderBound":
            natural = "by simp"
            bound = "by intro _ _ _; omega"
        else:
            natural = "by intro _; omega"
            bound = "by simp"
        entries.append(
            "  { degree := %(degree)d, catalogueIndex := %(index)d,\n"
            "    groupOrder := %(order)d, ternaryValuation := %(value)d,\n"
            "    kind := .%(kind)s, valuation_eq := by decide +kernel,\n"
            "    degree_lower := by omega, degree_upper := by omega,\n"
            "    index_pos := by omega, natural_degree := %(natural)s,\n"
            "    order_bound := %(bound)s }," % (r | {"natural": natural, "bound": bound})
        )
    return f"""import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRow

/-! Generated bounded primitive receipt, degrees {lo}--{hi}.

Source: `certificates/data/primitive_rank.jsonl.gz`, compressed SHA256
`{digest}`.  This chunk contains {len(selected)} published PrimGrp locators.
Lean checks every exact 3-adic valuation and every applicable integer bound.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

def primitiveCompositionBoundRows{name} : Array PrimitiveCompositionBoundRow := #[
{chr(10).join(entries)}]

theorem primitiveCompositionBoundRows{name}_size :
    primitiveCompositionBoundRows{name}.size = {len(selected)} := by
  decide +kernel

theorem primitiveCompositionBoundRows{name}_locators_nodup :
    (primitiveCompositionBoundRows{name}.toList.map
      PrimitiveCompositionBoundRow.locator).Nodup := by
  decide +kernel

theorem primitiveCompositionBoundRows{name}_degree_range :
    ∀ r ∈ primitiveCompositionBoundRows{name}.toList,
      {lo} ≤ r.degree ∧ r.degree ≤ {hi} := by
  decide +kernel

end SymmetricSubgroupAsymptotics
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chunk", type=int, choices=range(len(SPANS)), required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render(args.chunk, all_rows())
    path = FORMAL / f"PrimitiveCompositionBoundedRows{NAMES[args.chunk]}.lean"
    if args.check:
        if not path.is_file() or path.read_text(encoding="utf-8") != content:
            raise SystemExit(f"stale generated receipt: {path}")
        print(f"PASS {path.relative_to(ROOT)}")
    else:
        path.write_text(content, encoding="utf-8")
        print(f"WROTE {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
