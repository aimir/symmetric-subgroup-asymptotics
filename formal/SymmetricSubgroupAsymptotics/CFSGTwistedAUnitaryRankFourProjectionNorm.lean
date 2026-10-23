import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourProjection
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSum

/-! The half-projection of an outside singular vector is anisotropic.
This is the literal signed norm decomposition, not a Witt-index premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitaryRankFourProjection_eq_self_of_mem (q : CFSG.PrimePower)
    (x : Fin 5 → q.Extension 2) (hx : x ∈ unitaryRankFourHalf q) : unitaryRankFourProjection q x = x := by
  rw [unitaryRankFourProjection_apply, unitaryRankFourHalf_middle_zero q x hx, zero_smul, sub_zero]

theorem unitaryRankFour_outside_middle_ne_zero (q : CFSG.PrimePower)
    (x : Fin 5 → q.Extension 2) (hx : x ∉ unitaryRankFourHalf q) : x 2 ≠ 0 := by
  intro hz
  have hh := unitaryRankFourProjection_decomposition q x
  rw [hz, zero_smul, add_zero] at hh
  apply hx
  rw [hh]
  exact unitaryRankFourProjection_mem q x

theorem unitaryRankFourProjection_norm (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 (unitaryRankFourProjection q x) (unitaryRankFourProjection q x) =
      unitaryNaturalPair q 4 x x - definingFieldAutomorphism q 2 (x 2) * x 2 := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  have hph : hermitianPair sig H (unitaryRankFourProjection q x) (unitaryRankFourMiddle q) = 0 :=
    unitaryRankFourMiddle_perp_half q _ (unitaryRankFourProjection_mem q x)
  have hhp : hermitianPair sig H (unitaryRankFourMiddle q) (unitaryRankFourProjection q x) = 0 :=
    (unitaryNaturalPair_zero_swap q 4 _ _).mp hph
  have hh := hermitian_orthogonal_sum_self sig H (unitaryRankFourProjection q x)
    (unitaryRankFourMiddle q) (x 2) hph hhp
  have hhnorm : hermitianPair sig H (unitaryRankFourMiddle q) (unitaryRankFourMiddle q) = 1 :=
    unitaryRankFourMiddle_norm q
  rw [hhnorm, mul_one] at hh
  have he := congrArg (fun v : Fin 5 → q.Extension 2 => hermitianPair sig H v v)
    (unitaryRankFourProjection_decomposition q x)
  change hermitianPair sig H x x = hermitianPair sig H
    (unitaryRankFourProjection q x + x 2 • unitaryRankFourMiddle q)
    (unitaryRankFourProjection q x + x 2 • unitaryRankFourMiddle q) at he
  apply eq_sub_iff_add_eq.mpr
  exact (he.trans hh).symm

theorem unitaryRankFourProjection_norm_ne_zero (q : CFSG.PrimePower)
    (x : Fin 5 → q.Extension 2) (hx : x ∉ unitaryRankFourHalf q)
    (hnorm : unitaryNaturalPair q 4 x x = 0) :
    unitaryNaturalPair q 4 (unitaryRankFourProjection q x) (unitaryRankFourProjection q x) ≠ 0 := by
  have hc := unitaryRankFour_outside_middle_ne_zero q x hx
  have hs : definingFieldAutomorphism q 2 (x 2) ≠ 0 :=
    fun h => hc ((definingFieldAutomorphism q 2).injective (h.trans (map_zero _).symm))
  intro hz
  have hh := unitaryRankFourProjection_norm q x
  rw [hz, hnorm, zero_sub] at hh
  exact (mul_ne_zero hs hc) (neg_eq_zero.mp hh.symm)

theorem unitaryRankFourProjection_ne_zero (q : CFSG.PrimePower)
    (x : Fin 5 → q.Extension 2) (hx : x ∉ unitaryRankFourHalf q)
    (hnorm : unitaryNaturalPair q 4 x x = 0) : unitaryRankFourProjection q x ≠ 0 := by
  intro hz
  apply unitaryRankFourProjection_norm_ne_zero q x hx hnorm
  rw [hz]
  exact pair_zero_left _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
