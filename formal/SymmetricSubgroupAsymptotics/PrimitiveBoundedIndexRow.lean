import Mathlib.Tactic

/-! # One bounded primitive quotient-index row -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- One checked bounded almost-simple primitive catalogue row.  The exact
orders allow Lean to recover the socle quotient instead of importing it as a
published equality. -/
structure PrimitiveBoundedIndexRow where
  degree : ℕ
  catalogueIndex : ℕ
  groupOrder : ℕ
  socleOrder : ℕ
  outerOrder : ℕ
  order_factorization : groupOrder = outerOrder * socleOrder
  index_bound : 2 * outerOrder ≤ degree

namespace PrimitiveBoundedIndexRow

/-- The pinned PrimGrp degree/index locator. -/
def locator (row : PrimitiveBoundedIndexRow) : ℕ × ℕ :=
  (row.degree, row.catalogueIndex)

end PrimitiveBoundedIndexRow

end SymmetricSubgroupAsymptotics
