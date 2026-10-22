import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitIsometry
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitriangularSimilitude
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusFixed
import Mathlib.LinearAlgebra.Matrix.Block

/-! Every actual upper-triangular determinant-one signed-form isometry
factors as the literal original torus word times a norm-constrained upper
array. No full unitary-group equality is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2TriangularSimilitude
open CFSGTwistedA2DiagonalTorus
variable (K : Type) [Field K] (σ : K ≃+* K)

theorem upper_isometric_factor (hσ : Function.Involutive σ) (M : (Mat K 2)ˣ)
    (hu : (M : Mat K 2).BlockTriangular id) (hdet : Matrix.det (M : Mat K 2) = 1)
    (hform : (σ.toRingHom.mapMatrix (M : Mat K 2)).transpose *
        (↑((signedReversalUnit K 2)⁻¹) : Mat K 2) * (M : Mat K 2) =
      (↑((signedReversalUnit K 2)⁻¹) : Mat K 2)) :
    ∃ (z : K) (hz : z ≠ 0) (a b : K), NormCondition σ a b ∧
      (M : Mat K 2) = (torusUnit K σ z hz : Mat K 2) * upperArray σ a b := by
  have h10 : (M : Mat K 2) 1 0 = 0 := hu (by decide)
  have h20 : (M : Mat K 2) 2 0 = 0 := hu (by decide)
  let z := (M : Mat K 2) 0 0
  have hz : z ≠ 0 := pivot_ne_zero K M h10 h20
  have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
  have he := congrArg (fun A : Mat K 2 => A 0 2) hform
  rw [signedReversal_two_inv] at he
  have h02 : σ z * (M : Mat K 2) 2 2 = 1 := by
    simpa [z, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.map_apply, signedReversal_two_array, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, h10, h20] using he
  have hd2 : (M : Mat K 2) 2 2 = (σ z)⁻¹ := by
    apply mul_left_cancel₀ hσz
    rw [h02, mul_inv_cancel₀ hσz]
  have hp : z * (M : Mat K 2) 1 1 * (M : Mat K 2) 2 2 = 1 := by
    have hp' := hdet
    rw [Matrix.det_of_upperTriangular hu] at hp'
    change (∏ i : Fin 3, (M : Mat K 2) i i) = 1 at hp'
    rw [Fin.prod_univ_three] at hp'
    simpa only [z, mul_assoc] using hp'
  have hh := congrArg (fun a : K => a * σ z) hp
  rw [hd2] at hh
  have hprod : z * (M : Mat K 2) 1 1 = σ z := by
    simpa only [mul_assoc, inv_mul_cancel₀ hσz, mul_one, one_mul] using hh
  have hd1 : (M : Mat K 2) 1 1 = σ z / z := by
    apply (eq_div_iff hz).mpr
    simpa only [mul_comm] using hprod
  let T := torusUnit K σ z hz
  let N := T⁻¹ * M
  have hNval : (N : Mat K 2) =
      Matrix.diagonal (torusInverseWeights K σ z) * (M : Mat K 2) := rfl
  have hNu : (N : Mat K 2).BlockTriangular id := by
    intro i j hji
    rw [hNval, Matrix.diagonal_mul, hu hji, mul_zero]
  have hNd : ∀ i : Fin 3, (N : Mat K 2) i i = 1 := by
    intro i
    rw [hNval, Matrix.diagonal_mul]
    fin_cases i
    · simp [torusInverseWeights, z, hz]
    · simp [torusInverseWeights, hd1, hz, hσz]
    · simp [torusInverseWeights, hd2, hσz]
  have hMfix := unit_fixed_of_isometric K 2 σ.toRingHom M hform
  have hTfix : diagramFieldUnitHom K 2 σ.toRingHom T = T :=
    torusUnit_fixed K σ hσ z hz
  have hNfix : diagramFieldUnitHom K 2 σ.toRingHom N = N := by
    change diagramFieldUnitHom K 2 σ.toRingHom (T⁻¹ * M) = T⁻¹ * M
    rw [map_mul, map_inv, hTfix, hMfix]
  have hNform := fixed_unit_isometric K 2 σ.toRingHom N hNfix
  obtain ⟨a, b, hab, hn⟩ := upperArray_of_unitriangular_similitude K σ hσ
    (N : Mat K 2) 1 hNu hNd (by simpa only [one_smul] using hNform)
  refine ⟨z, hz, a, b, hab, ?_⟩
  calc
    (M : Mat K 2) = (T : Mat K 2) * (N : Mat K 2) := by
      change (M : Mat K 2) = (T : Mat K 2) * ((↑(T⁻¹) : Mat K 2) * (M : Mat K 2))
      rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = _ := congrArg (fun A : Mat K 2 => (T : Mat K 2) * A) hn

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
