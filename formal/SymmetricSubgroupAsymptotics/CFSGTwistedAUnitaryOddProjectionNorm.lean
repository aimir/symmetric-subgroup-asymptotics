import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddProjection
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSum

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitaryOddProjection_eq_self_of_mem (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∈ unitaryOddHalf q m) : unitaryOddProjection q m x = x := by
  rw [unitaryOddProjection_apply, unitaryOddHalf_middle_zero q m x hx, zero_smul, sub_zero]

theorem unitaryOdd_outside_middle_ne_zero (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∉ unitaryOddHalf q m) : x (unitaryOddMiddleIndex m) ≠ 0 := by
  intro hz
  have hh := unitaryOddProjection_decomposition q m x
  rw [hz, zero_smul, add_zero] at hh
  apply hx
  rw [hh]
  exact unitaryOddProjection_mem q m x

theorem unitaryOddProjection_norm (q : CFSG.PrimePower) (m : ℕ) (x : Fin (2*m+5) → q.Extension 2) :
    unitaryNaturalPair q (2*m+4) (unitaryOddProjection q m x) (unitaryOddProjection q m x) =
      unitaryNaturalPair q (2*m+4) x x - definingFieldAutomorphism q 2 (x (unitaryOddMiddleIndex m)) * x (unitaryOddMiddleIndex m) *
        unitaryNaturalPair q (2*m+4) (unitaryOddMiddle q m) (unitaryOddMiddle q m) := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  have hph : hermitianPair sig H (unitaryOddProjection q m x) (unitaryOddMiddle q m) = 0 :=
    unitaryOddMiddle_perp_half q m _ (unitaryOddProjection_mem q m x)
  have hhp : hermitianPair sig H (unitaryOddMiddle q m) (unitaryOddProjection q m x) = 0 :=
    (unitaryNaturalPair_zero_swap q (2*m+4) _ _).mp hph
  have hh := hermitian_orthogonal_sum_self sig H (unitaryOddProjection q m x)
    (unitaryOddMiddle q m) (x (unitaryOddMiddleIndex m)) hph hhp
  have he := congrArg (fun v : Fin (2*m+5) → q.Extension 2 => hermitianPair sig H v v)
    (unitaryOddProjection_decomposition q m x)
  change hermitianPair sig H x x = hermitianPair sig H
    (unitaryOddProjection q m x + x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m)
    (unitaryOddProjection q m x + x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m) at he
  apply eq_sub_iff_add_eq.mpr
  exact (he.trans hh).symm

theorem unitaryOddProjection_norm_ne_zero (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∉ unitaryOddHalf q m)
    (hnorm : unitaryNaturalPair q (2*m+4) x x = 0) :
    unitaryNaturalPair q (2*m+4) (unitaryOddProjection q m x) (unitaryOddProjection q m x) ≠ 0 := by
  have hc := unitaryOdd_outside_middle_ne_zero q m x hx
  have hs : definingFieldAutomorphism q 2 (x (unitaryOddMiddleIndex m)) ≠ 0 :=
    fun h => hc ((definingFieldAutomorphism q 2).injective (h.trans (map_zero _).symm))
  intro hz
  have hh := unitaryOddProjection_norm q m x
  rw [hz, hnorm, zero_sub] at hh
  exact (mul_ne_zero (mul_ne_zero hs hc) (unitaryOddMiddle_norm_ne_zero q m))
    (neg_eq_zero.mp hh.symm)

theorem unitaryOddProjection_ne_zero (q : CFSG.PrimePower) (m : ℕ)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∉ unitaryOddHalf q m)
    (hnorm : unitaryNaturalPair q (2*m+4) x x = 0) : unitaryOddProjection q m x ≠ 0 := by
  intro hz
  apply unitaryOddProjection_norm_ne_zero q m x hx hnorm
  rw [hz]
  exact pair_zero_left _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
