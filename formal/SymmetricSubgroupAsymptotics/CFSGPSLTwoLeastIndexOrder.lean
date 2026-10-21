import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The least-proper-index/order half for the literal PSL2 quotient,
uniformly for q>=4. The fields of orders four and five are included by
the same exact order comparison, with no abstract A5 identification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open CFSGPSLTwoRootCoordinates PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F]

theorem leastProperIndex_le_borel_index (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) :
    ell≤Nat.card F+1 := by
  have hh := hell.2 (projectiveBorel (F:=F)) projectiveBorel_isCoatom.1
  rwa [projectiveBorel_index] at hh

theorem leastProperIndex_square_lt_card (hq : 4≤Nat.card F) (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) : ell^2<Nat.card (PSL (F:=F)) := by
  have he := Nat.pow_le_pow_left (leastProperIndex_le_borel_index ell hell) 2
  have hh := projectiveBorel_index_square_lt_card hq
  rw [projectiveBorel_index] at hh
  exact he.trans_lt hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
