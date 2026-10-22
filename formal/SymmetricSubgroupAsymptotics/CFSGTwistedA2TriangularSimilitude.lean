import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentFixedLine
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDiagramScalars
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! In natural dimension three, a literal signed-form similitude which
preserves the first coordinate line is upper triangular. This is a direct
matrix consequence, not an assumed unitary/Borel identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2TriangularSimilitude
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K]

theorem signedReversal_two_inv :
    (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) = (signedReversalUnit K 2 : Mat K 2) := by
  have hh : signedReversalUnit K 2 * signedReversalUnit K 2 = 1 := by
    apply Units.ext
    change (signedReversalUnit K 2 : Mat K 2) * (signedReversalUnit K 2 : Mat K 2) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, signedReversalUnit_apply,
        signWeight, Fin.rev, Matrix.one_apply] <;> norm_num [Fin.ext_iff]
  exact congrArg (fun u : (Mat K 2)ˣ => (u : Mat K 2))
    (inv_eq_of_mul_eq_one_right hh)

theorem pivot_ne_zero (M : (Mat K 2)ˣ) (h10 : (M : Mat K 2) 1 0 = 0)
    (h20 : (M : Mat K 2) 2 0 = 0) : (M : Mat K 2) 0 0 ≠ 0 := by
  intro h00
  have hh := congrArg (fun A : Mat K 2 => A 0 0) (Units.inv_mul M)
  change ((↑(M⁻¹) : Mat K 2) * (M : Mat K 2)) 0 0 = 1 at hh
  simpa [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20] using hh

theorem triangular_of_first_column (σ : K ≃+* K) (M : (Mat K 2)ˣ) (c : K)
    (hform : (σ.toRingHom.mapMatrix (M : Mat K 2)).transpose *
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * (M : Mat K 2) =
        c • (↑((signedReversalUnit K 2)⁻¹) : Mat K 2))
    (h10 : (M : Mat K 2) 1 0 = 0) (h20 : (M : Mat K 2) 2 0 = 0) :
    (M : Mat K 2).BlockTriangular id := by
  have h00 := pivot_ne_zero K M h10 h20
  have hσ00 : σ ((M : Mat K 2) 0 0) ≠ 0 := (map_ne_zero σ).mpr h00
  have he := congrArg (fun A : Mat K 2 => A 0 1) hform
  rw [signedReversal_two_inv] at he
  change (((M : Mat K 2).map σ.toRingHom).transpose *
      (signedReversalUnit K 2 : Mat K 2) * (M : Mat K 2)) 0 1 =
    (c • (signedReversalUnit K 2 : Mat K 2)) 0 1 at he
  have hp : σ ((M : Mat K 2) 0 0) * (M : Mat K 2) 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.map_apply, signedReversalUnit_apply, signWeight, Fin.rev, h10, h20] using he
  have h21 : (M : Mat K 2) 2 1 = 0 := (mul_eq_zero.mp hp).resolve_left hσ00
  intro i j hji
  fin_cases i <;> fin_cases j <;> simp_all

end SymmetricSubgroupAsymptotics.CFSGTwistedA2TriangularSimilitude
