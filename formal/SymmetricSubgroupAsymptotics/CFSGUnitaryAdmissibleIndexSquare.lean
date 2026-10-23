import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoIndexSquare
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHigherIndexSquare

/-! The original unitary index-square inequality in every rank and
field allowed by the pinned classifier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_admissible_leastIndex_square_lt (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedA r q) := by
  by_cases htwo : r = 2
  · subst r
    have hq2 := CFSGTwistedAQuadraticTrace.order_two_le q
    have hqne := hsmall rfl
    exact twistedA_rank_two_leastIndex_square_lt q (by omega) ell hell
  by_cases hthree : r = 3
  · subst r
    exact twistedA_rank_three_leastIndex_square_lt q ell hell
  obtain ⟨s, hs⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
  subst r
  exact twistedA_higher_leastIndex_square_lt q s ell hell

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
