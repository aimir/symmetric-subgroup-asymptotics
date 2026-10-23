import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfWeights
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity
import Mathlib.Tactic.Ring

/-! Constructed opposed-half similitudes for the literal signed form.
The first half is fixed and the second is scaled by its genuine fixed
multiplier. The odd-dimensional middle is supplied by actual norm
surjectivity, not an isometry-extension premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters

def unitaryHalfScale (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2) :
    (Fin (r+1) → q.Extension 2) →ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2) where
  toFun x i := unitaryHalfWeight r t u i * x i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' a x := by ext i; change _ * (a*x i) = a * (_*x i); ring

theorem unitaryHalfScale_apply (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (x : Fin (r+1) → q.Extension 2) (i : Fin (r+1)) :
    unitaryHalfScale q r t u x i = unitaryHalfWeight r t u i * x i := rfl

def unitaryHalfScaleEquiv (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : t ≠ 0) (hu : u ≠ 0) :
    (Fin (r+1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r+1) → q.Extension 2) where
  toLinearMap := unitaryHalfScale q r t u
  invFun := unitaryHalfScale q r t⁻¹ u⁻¹
  left_inv := by
    intro x
    funext i
    change unitaryHalfWeight r t⁻¹ u⁻¹ i * (unitaryHalfWeight r t u i * x i) = x i
    rw [←mul_assoc,unitaryHalfWeight_inverse_mul r t u ht hu,one_mul]
  right_inv := by
    intro x
    funext i
    change unitaryHalfWeight r t u i * (unitaryHalfWeight r t⁻¹ u⁻¹ i * x i) = x i
    rw [←mul_assoc,mul_comm (unitaryHalfWeight r t u i),unitaryHalfWeight_inverse_mul r t u ht hu,one_mul]

private theorem reversal_mulVec (q : CFSG.PrimePower) (r : ℕ)
    (y : Fin (r+1) → q.Extension 2) (i : Fin (r+1)) :
    ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i =
      signWeight (q.Extension 2) r i * y i.rev := by
  simp [Matrix.mulVec,dotProduct,signedReversalUnit_apply,ite_mul,eq_comm]

theorem unitaryHalfScale_pair (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : definingFieldAutomorphism q 2 t = t) (hu : definingFieldAutomorphism q 2 u * u = t)
    (x y : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r (unitaryHalfScale q r t u x) (unitaryHalfScale q r t u y) = t * unitaryNaturalPair q r x y := by
  change (∑ i, definingFieldAutomorphism q 2 (unitaryHalfScale q r t u x i) *
    (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ unitaryHalfScale q r t u y) i)) =
    t * ∑ i, definingFieldAutomorphism q 2 (x i) *
      (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i)
  simp only [reversal_mulVec,unitaryHalfScale_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  calc
    _ = (definingFieldAutomorphism q 2 (unitaryHalfWeight r t u i) * unitaryHalfWeight r t u i.rev) *
        (definingFieldAutomorphism q 2 (x i) * (signWeight (q.Extension 2) r i * y i.rev)) := by ring
    _ = _ := by rw [unitaryHalfWeight_pair (definingFieldAutomorphism q 2) r t u ht hu]

theorem unitaryHalfScale_fix_standard (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (x : Fin (r+1) → q.Extension 2) (hx : x ∈ unitaryStandardSingularSpace q r) :
    unitaryHalfScale q r t u x = x := by
  funext i
  rw [unitaryHalfScale_apply]
  by_cases hi : 2*i.val < r
  · simp only [unitaryHalfWeight,if_pos hi,one_mul]
  · rw [hx i (by omega),mul_zero]

theorem unitaryHalfScale_scale_opposite (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (x : Fin (r+1) → q.Extension 2) (hx : x ∈ unitaryOppositeSingularSpace q r) :
    unitaryHalfScale q r t u x = t • x := by
  funext i
  change unitaryHalfWeight r t u i * x i = t * x i
  by_cases hi : r < 2*i.val
  · have hnot : ¬2*i.val < r := by omega
    simp only [unitaryHalfWeight,if_neg hnot,if_pos hi]
  · have hv : i.rev.val = r-i.val := by rw [Fin.val_rev]; omega
    have hib := i.isLt
    have hz : x i = 0 := (unitaryOppositeSingularSpace_mem_iff q r x).mp hx i (by omega)
    rw [hz,mul_zero,mul_zero]

theorem exists_unitaryHalfScale_parameters (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ≠ 0) (hfixed : definingFieldAutomorphism q 2 t = t) :
    ∃ u : q.Extension 2, u ≠ 0 ∧ definingFieldAutomorphism q 2 u * u = t := by
  obtain ⟨u,hu⟩ := CFSGTwistedA2UnipotentArrays.exists_norm_eq_fixed q t hfixed
  refine ⟨u,?_,by simpa only [mul_comm] using hu⟩
  intro h
  exact ht (hu.symm.trans (by rw [h,zero_mul]))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
