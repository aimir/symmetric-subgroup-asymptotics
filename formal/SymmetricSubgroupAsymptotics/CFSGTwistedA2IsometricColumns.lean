import SymmetricSubgroupAsymptotics.CFSGTwistedA2IsotropicClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitriangularSimilitude

/-! Actual first-column equations of signed-form isometries. The zero
lower-pivot case is upper triangular; the nonzero case is eligible for
the previously proved explicit upper-array clearing operation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2TriangularSimilitude
variable {K : Type} [Field K] (σ : K ≃+* K)

theorem isometric_first_column (M : Mat K 2)
    (hform : (σ.toRingHom.mapMatrix M).transpose *
        (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * M =
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2)) :
    SignedIsotropic σ (fun i => M i 0) := by
  rw [signedReversal_two_inv, signedReversal_two_array] at hform
  let J : Mat K 2 := !![0, 0, 1; 0, -1, 0; 1, 0, 0]
  have hr (j : Fin 3) : ((σ.toRingHom.mapMatrix M).transpose * J) 0 j =
      (![σ (M 2 0), -σ (M 1 0), σ (M 0 0)] : Fin 3 → K) j := by
    fin_cases j <;>
      simp [J, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hh := congrArg (fun A : Mat K 2 => A 0 0) hform
  change (((σ.toRingHom.mapMatrix M).transpose * J) * M) 0 0 = 0 at hh
  rw [Matrix.mul_apply, Fin.sum_univ_three, hr 0, hr 1, hr 2] at hh
  change σ (M 2 0) * M 0 0 + (-σ (M 1 0)) * M 1 0 +
    σ (M 0 0) * M 2 0 = 0 at hh
  change σ (M 0 0) * M 2 0 - σ (M 1 0) * M 1 0 + σ (M 2 0) * M 0 0 = 0
  linear_combination hh

theorem isometric_upper_of_lower_pivot_zero (M : (Mat K 2)ˣ)
    (hform : (σ.toRingHom.mapMatrix (M : Mat K 2)).transpose *
        (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * (M : Mat K 2) =
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2))
    (h20 : (M : Mat K 2) 2 0 = 0) : (M : Mat K 2).BlockTriangular id := by
  have hcol := isometric_first_column σ (M : Mat K 2) hform
  have h10 : (M : Mat K 2) 1 0 = 0 := by
    have hz : σ ((M : Mat K 2) 1 0) * (M : Mat K 2) 1 0 = 0 := by
      change σ ((M : Mat K 2) 0 0) * (M : Mat K 2) 2 0 -
        σ ((M : Mat K 2) 1 0) * (M : Mat K 2) 1 0 +
          σ ((M : Mat K 2) 2 0) * (M : Mat K 2) 0 0 = 0 at hcol
      simpa only [h20, map_zero, mul_zero, zero_mul, zero_sub, add_zero,
        neg_eq_zero] using hcol
    rcases mul_eq_zero.mp hz with h | h
    · exact (map_eq_zero σ).mp h
    · exact h
  exact triangular_of_first_column K σ M 1 (by simpa only [one_smul] using hform) h10 h20

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
