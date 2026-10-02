import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexRows5To11
import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexRows12To18
import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexRows19To24
import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexRows25To29

/-!
# Complete bounded primitive quotient-index receipt

The four generated degree chunks contain 30, 30, 27, and 29 rows.  Their
checked sizes assemble to the complete 116-row simple-socle slice without a
single large kernel reduction.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- All simple-nonabelian-socle primitive rows in degrees 5 through 29. -/
def primitiveBoundedIndexRows : Array PrimitiveBoundedIndexRow :=
  primitiveBoundedIndexRows5To11 ++
  primitiveBoundedIndexRows12To18 ++
  primitiveBoundedIndexRows19To24 ++
  primitiveBoundedIndexRows25To29

theorem primitiveBoundedIndexRows_size :
    primitiveBoundedIndexRows.size = 116 := by
  simp [primitiveBoundedIndexRows,
    primitiveBoundedIndexRows5To11_size,
    primitiveBoundedIndexRows12To18_size,
    primitiveBoundedIndexRows19To24_size,
    primitiveBoundedIndexRows25To29_size]

/-- Typed access to the complete exact-order receipt. -/
def primitiveBoundedIndexRow (i : Fin 116) : PrimitiveBoundedIndexRow :=
  primitiveBoundedIndexRows[i.val]'(by
    rw [primitiveBoundedIndexRows_size]
    exact i.isLt)

theorem primitiveBoundedIndexRow_bound (i : Fin 116) :
    2 * (primitiveBoundedIndexRow i).outerOrder ≤
      (primitiveBoundedIndexRow i).degree :=
  (primitiveBoundedIndexRow i).index_bound

end SymmetricSubgroupAsymptotics
