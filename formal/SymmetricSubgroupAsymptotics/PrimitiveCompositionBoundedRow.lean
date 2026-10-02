import Mathlib.Data.Nat.Factorization.Basic

/-!
# Bounded primitive three-tenths receipt rows

The bounded primitive catalogue is certified by a stronger reduction than a
literal replay of every composition chain.  An ordinary row is discharged by
the ternary valuation of its exact group order.  The only systematic failures
of that stronger test are the natural alternating and symmetric rows, which
are discharged symbolically in `PrimitiveNaturalCompositionZero`.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The proof route attached to a bounded primitive catalogue row. -/
inductive PrimitiveCompositionBoundKind where
  | orderBound
  | naturalAlternating
  | naturalSymmetric
  deriving DecidableEq, Repr

/-- One published PrimGrp row together with kernel-checked arithmetic. -/
structure PrimitiveCompositionBoundRow where
  degree : ℕ
  catalogueIndex : ℕ
  groupOrder : ℕ
  ternaryValuation : ℕ
  kind : PrimitiveCompositionBoundKind
  valuation_eq : groupOrder.factorization 3 = ternaryValuation
  degree_lower : 2 ≤ degree
  degree_upper : degree ≤ 44
  index_pos : 0 < catalogueIndex
  natural_degree : kind ≠ .orderBound → 5 ≤ degree
  order_bound : kind = .orderBound → 4 ≤ degree → degree ≠ 9 →
    10 * ternaryValuation ≤ 3 * degree

/-- Catalogue locator retained independently of the arithmetic payload. -/
def PrimitiveCompositionBoundRow.locator (r : PrimitiveCompositionBoundRow) : ℕ × ℕ :=
  (r.degree, r.catalogueIndex)

end SymmetricSubgroupAsymptotics
