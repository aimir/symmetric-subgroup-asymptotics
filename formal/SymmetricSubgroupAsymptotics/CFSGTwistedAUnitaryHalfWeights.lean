import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfDecomposition

/-! Exact coordinate weights for opposed-half normalization. Their
sigma-paired product is the actual similitude multiplier, including the
anisotropic middle coordinate when present. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
variable {K : Type*} [Field K]

def unitaryHalfWeight (r : ℕ) (t u : K) (i : Fin (r+1)) : K :=
  if 2*i.val < r then 1 else if r < 2*i.val then t else u

theorem unitaryHalfWeight_ne_zero (r : ℕ) (t u : K) (ht : t ≠ 0) (hu : u ≠ 0) (i : Fin (r+1)) :
    unitaryHalfWeight r t u i ≠ 0 := by
  unfold unitaryHalfWeight
  split_ifs <;> first | exact one_ne_zero | exact ht | exact hu

theorem unitaryHalfWeight_inverse_mul (r : ℕ) (t u : K) (ht : t ≠ 0) (hu : u ≠ 0) (i : Fin (r+1)) :
    unitaryHalfWeight r t⁻¹ u⁻¹ i * unitaryHalfWeight r t u i = 1 := by
  unfold unitaryHalfWeight
  split_ifs <;> simp only [one_mul,inv_mul_cancel₀ ht,inv_mul_cancel₀ hu]

theorem unitaryHalfWeight_pair (sigma : K ≃+* K) (r : ℕ) (t u : K)
    (ht : sigma t = t) (hu : sigma u * u = t) (i : Fin (r+1)) :
    sigma (unitaryHalfWeight r t u i) * unitaryHalfWeight r t u i.rev = t := by
  have hir := i.isLt
  have hrev : i.rev.val = r-i.val := by rw [Fin.val_rev]; omega
  by_cases hi : 2*i.val < r
  · have h1 : ¬2*i.rev.val < r := by omega
    have h2 : r < 2*i.rev.val := by omega
    simp only [unitaryHalfWeight,if_pos hi,if_neg h1,if_pos h2,map_one,one_mul]
  · by_cases hj : r < 2*i.val
    · have h1 : 2*i.rev.val < r := by omega
      simp only [unitaryHalfWeight,if_neg hi,if_pos hj,if_pos h1,ht,mul_one]
    · have h1 : ¬2*i.rev.val < r := by omega
      have h2 : ¬r < 2*i.rev.val := by omega
      simpa only [unitaryHalfWeight,if_neg hi,if_neg hj,if_neg h1,if_neg h2] using hu

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
