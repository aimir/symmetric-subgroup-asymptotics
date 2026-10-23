import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleImage
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalCrossSum

/-! Literal middle scaling in the original signed five-space. A norm-one
coefficient gives an actual linear isometry, not an ambient action input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

def unitaryRankFourMiddleScale (q : CFSG.PrimePower) (c : q.Extension 2) :
    (Fin 5 → q.Extension 2) →ₗ[q.Extension 2] (Fin 5 → q.Extension 2) :=
  unitaryRankFourProjection q + (LinearMap.proj (2 : Fin 5)).smulRight (c • unitaryRankFourMiddle q)

theorem unitaryRankFourMiddleScale_apply (q : CFSG.PrimePower) (c : q.Extension 2)
    (x : Fin 5 → q.Extension 2) : unitaryRankFourMiddleScale q c x =
      unitaryRankFourProjection q x + x 2 • (c • unitaryRankFourMiddle q) := rfl

theorem unitaryRankFourMiddleScale_coordinate (q : CFSG.PrimePower) (c : q.Extension 2)
    (x : Fin 5 → q.Extension 2) (i : Fin 5) :
    unitaryRankFourMiddleScale q c x i = if i = 2 then c * x 2 else x i := by
  rw [unitaryRankFourMiddleScale_apply,unitaryRankFourProjection_apply]
  by_cases hi : i = 2
  · subst i
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,unitaryRankFourMiddle,Pi.single_eq_same,
      smul_eq_mul,mul_one,sub_self,zero_add,ite_true]
    exact mul_comm _ _
  · simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,unitaryRankFourMiddle,Pi.single_apply,
      if_neg hi,smul_eq_mul,mul_zero,sub_zero,add_zero]

theorem unitaryRankFourMiddleScale_fix_half (q : CFSG.PrimePower) (c : q.Extension 2)
    (x : Fin 5 → q.Extension 2) (hx : x ∈ unitaryRankFourHalf q) : unitaryRankFourMiddleScale q c x = x := by
  rw [unitaryRankFourMiddleScale_apply,unitaryRankFourProjection_eq_self_of_mem q x hx,
    unitaryRankFourHalf_middle_zero q x hx,zero_smul,add_zero]

def unitaryRankFourMiddleScaleEquiv (q : CFSG.PrimePower) (c : q.Extension 2) (hc : c ≠ 0) :
    (Fin 5 → q.Extension 2) ≃ₗ[q.Extension 2] (Fin 5 → q.Extension 2) where
  toLinearMap := unitaryRankFourMiddleScale q c
  invFun := unitaryRankFourMiddleScale q c⁻¹
  left_inv := by
    intro x
    funext i
    change unitaryRankFourMiddleScale q c⁻¹ (unitaryRankFourMiddleScale q c x) i = x i
    by_cases hi : i = 2
    · simp only [unitaryRankFourMiddleScale_coordinate,hi,ite_true]
      rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
    · simp only [unitaryRankFourMiddleScale_coordinate,if_neg hi]
  right_inv := by
    intro x
    funext i
    change unitaryRankFourMiddleScale q c (unitaryRankFourMiddleScale q c⁻¹ x) i = x i
    by_cases hi : i = 2
    · simp only [unitaryRankFourMiddleScale_coordinate,hi,ite_true]
      rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
    · simp only [unitaryRankFourMiddleScale_coordinate,if_neg hi]

theorem unitaryRankFourMiddleScale_pair (q : CFSG.PrimePower) (c : q.Extension 2)
    (hc : definingFieldAutomorphism q 2 c * c = 1) (x y : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 (unitaryRankFourMiddleScale q c x) (unitaryRankFourMiddleScale q c y) =
      unitaryNaturalPair q 4 x y := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let p := unitaryRankFourProjection q x
  let z := unitaryRankFourProjection q y
  have hph : hermitianPair sig H p (unitaryRankFourMiddle q) = 0 :=
    unitaryRankFourMiddle_perp_half q p (unitaryRankFourProjection_mem q x)
  have hhz : hermitianPair sig H (unitaryRankFourMiddle q) z = 0 :=
    unitaryRankFourMiddle_pair_half q z (unitaryRankFourProjection_mem q y)
  have hhn : hermitianPair sig H (unitaryRankFourMiddle q) (unitaryRankFourMiddle q) = 1 :=
    unitaryRankFourMiddle_norm q
  have hs := hermitian_orthogonal_cross_sum sig H p z (unitaryRankFourMiddle q) (x 2) (y 2) hph hhz
  rw [hhn,mul_one,←unitaryRankFourProjection_decomposition,←unitaryRankFourProjection_decomposition] at hs
  have ht := hermitian_orthogonal_cross_sum sig H p z (unitaryRankFourMiddle q) (x 2*c) (y 2*c) hph hhz
  rw [hhn,mul_one] at ht
  have hcoef : sig (x 2*c) * (y 2*c) = sig (x 2) * y 2 := by
    rw [map_mul]
    calc
      _ = (sig c*c) * (sig (x 2)*y 2) := by ring
      _ = _ := by rw [hc,one_mul]
  change hermitianPair sig H _ _ = _
  rw [unitaryRankFourMiddleScale_apply,unitaryRankFourMiddleScale_apply,smul_smul,smul_smul]
  exact (ht.trans (congrArg (fun a => hermitianPair sig H p z + a) hcoef)).trans hs.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
