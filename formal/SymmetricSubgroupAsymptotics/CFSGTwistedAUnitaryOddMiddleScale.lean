import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleImage
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalCrossSum

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

def unitaryOddMiddleScale (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2) :
    (Fin (2*m+5) → q.Extension 2) →ₗ[q.Extension 2] (Fin (2*m+5) → q.Extension 2) :=
  unitaryOddProjection q m + (LinearMap.proj (unitaryOddMiddleIndex m)).smulRight (c • unitaryOddMiddle q m)

theorem unitaryOddMiddleScale_apply (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2)
    (x : Fin (2*m+5) → q.Extension 2) : unitaryOddMiddleScale q m c x =
      unitaryOddProjection q m x + x (unitaryOddMiddleIndex m) • (c • unitaryOddMiddle q m) := rfl

theorem unitaryOddMiddleScale_coordinate (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2)
    (x : Fin (2*m+5) → q.Extension 2) (i : Fin (2*m+5)) :
    unitaryOddMiddleScale q m c x i = if i = unitaryOddMiddleIndex m then c * x (unitaryOddMiddleIndex m) else x i := by
  rw [unitaryOddMiddleScale_apply,unitaryOddProjection_apply]
  by_cases hi : i = unitaryOddMiddleIndex m
  · subst i
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,unitaryOddMiddle,Pi.single_eq_same,
      smul_eq_mul,mul_one,sub_self,zero_add,ite_true]
    exact mul_comm _ _
  · simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,unitaryOddMiddle,Pi.single_apply,
      if_neg hi,smul_eq_mul,mul_zero,sub_zero,add_zero]

theorem unitaryOddMiddleScale_fix_half (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2)
    (x : Fin (2*m+5) → q.Extension 2) (hx : x ∈ unitaryOddHalf q m) : unitaryOddMiddleScale q m c x = x := by
  rw [unitaryOddMiddleScale_apply,unitaryOddProjection_eq_self_of_mem q m x hx,
    unitaryOddHalf_middle_zero q m x hx,zero_smul,add_zero]

def unitaryOddMiddleScaleEquiv (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2) (hc : c ≠ 0) :
    (Fin (2*m+5) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (2*m+5) → q.Extension 2) where
  toLinearMap := unitaryOddMiddleScale q m c
  invFun := unitaryOddMiddleScale q m c⁻¹
  left_inv := by
    intro x
    funext i
    change unitaryOddMiddleScale q m c⁻¹ (unitaryOddMiddleScale q m c x) i = x i
    by_cases hi : i = unitaryOddMiddleIndex m
    · simp only [unitaryOddMiddleScale_coordinate,hi,ite_true]
      rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
    · simp only [unitaryOddMiddleScale_coordinate,if_neg hi]
  right_inv := by
    intro x
    funext i
    change unitaryOddMiddleScale q m c (unitaryOddMiddleScale q m c⁻¹ x) i = x i
    by_cases hi : i = unitaryOddMiddleIndex m
    · simp only [unitaryOddMiddleScale_coordinate,hi,ite_true]
      rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
    · simp only [unitaryOddMiddleScale_coordinate,if_neg hi]

theorem unitaryOddMiddleScale_pair (q : CFSG.PrimePower) (m : ℕ) (c : q.Extension 2)
    (hc : definingFieldAutomorphism q 2 c * c = 1) (x y : Fin (2*m+5) → q.Extension 2) :
    unitaryNaturalPair q (2*m+4) (unitaryOddMiddleScale q m c x) (unitaryOddMiddleScale q m c y) =
      unitaryNaturalPair q (2*m+4) x y := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  let p := unitaryOddProjection q m x
  let z := unitaryOddProjection q m y
  have hph : hermitianPair sig H p (unitaryOddMiddle q m) = 0 :=
    unitaryOddMiddle_perp_half q m p (unitaryOddProjection_mem q m x)
  have hhz : hermitianPair sig H (unitaryOddMiddle q m) z = 0 :=
    unitaryOddMiddle_pair_half q m z (unitaryOddProjection_mem q m y)
  let d := hermitianPair sig H (unitaryOddMiddle q m) (unitaryOddMiddle q m)
  have hs := hermitian_orthogonal_cross_sum sig H p z (unitaryOddMiddle q m) (x (unitaryOddMiddleIndex m)) (y (unitaryOddMiddleIndex m)) hph hhz
  rw [←unitaryOddProjection_decomposition,←unitaryOddProjection_decomposition] at hs
  have ht := hermitian_orthogonal_cross_sum sig H p z (unitaryOddMiddle q m) (x (unitaryOddMiddleIndex m)*c) (y (unitaryOddMiddleIndex m)*c) hph hhz
  have hcoef : sig (x (unitaryOddMiddleIndex m)*c) * (y (unitaryOddMiddleIndex m)*c) = sig (x (unitaryOddMiddleIndex m)) * y (unitaryOddMiddleIndex m) := by
    rw [map_mul]
    calc
      _ = (sig c*c) * (sig (x (unitaryOddMiddleIndex m))*y (unitaryOddMiddleIndex m)) := by ring
      _ = _ := by rw [hc,one_mul]
  change hermitianPair sig H _ _ = _
  rw [unitaryOddMiddleScale_apply,unitaryOddMiddleScale_apply,smul_smul,smul_smul]
  exact (ht.trans (congrArg (fun a => hermitianPair sig H p z + a*d) hcoef)).trans hs.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
