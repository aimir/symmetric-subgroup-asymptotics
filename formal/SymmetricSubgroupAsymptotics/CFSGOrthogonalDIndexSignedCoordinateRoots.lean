import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays

/-! Actual signed SL coordinate permutations transport D upper skew
roots in every rank. Both paired weights are retained, with their
square-one identity proving equality of the two required coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSignedCoordinateRoots
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSignedPermutation
open CFSGOrthogonalDGenerationMonomialAction CFSGOrthogonalDGenerationRootArrays
variable (K : Type) [Field K]

theorem weight_ne_zero {r : ℕ} (b : Fin r) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    weight K b σ i ≠ 0 := by
  intro hi
  have h := weight_mul_self K b σ i
  rw [hi, zero_mul] at h
  exact zero_ne_one h

theorem weight_ratio {r : ℕ} (b : Fin r) (σ : Equiv.Perm (Fin r)) (i j : Fin r) (t : K) :
    weight K b σ j * t / weight K b σ i = weight K b σ i * t / weight K b σ j := by
  apply (div_eq_div_iff (weight_ne_zero K b σ i) (weight_ne_zero K b σ j)).mpr
  calc
    weight K b σ j * t * weight K b σ j =
        (weight K b σ j * weight K b σ j) * t := by ring
    _ = t := by rw [weight_mul_self, one_mul]
    _ = (weight K b σ i * weight K b σ i) * t := by rw [weight_mul_self, one_mul]
    _ = weight K b σ i * t * weight K b σ i := by ring

theorem signedPermutation_plus_conjugation (r : ℕ) (b : Fin r)
    (σ : Equiv.Perm (Fin r)) (i j : Fin r) (t : K) :
    ((signedPermutationElement K r b σ).val : Mat K r) * plusArray i j t *
      (↑((signedPermutationElement K r b σ).val⁻¹) : Mat K r) =
      plusArray (σ.symm i) (σ.symm j)
        (weight K b σ (σ.symm i) * t / weight K b σ (σ.symm j)) := by
  have h := conjugation_two_entry (signedPermutationElement K r b σ).val
    (Equiv.sumCongr σ σ) (Sum.elim (weight K b σ) (weight K b σ))
    (signedPermutationElement_coe K r b σ)
    (Sum.inl i) (Sum.inr j) (Sum.inl j) (Sum.inr i) t
    (by simpa only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, Sum.elim_inr]
      using weight_ne_zero K b σ (σ.symm j))
    (by simpa only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, Sum.elim_inr]
      using weight_ne_zero K b σ (σ.symm i))
  simpa only [plusArray, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Sum.map_inr, Sum.elim_inl, Sum.elim_inr, weight_ratio] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSignedCoordinateRoots
