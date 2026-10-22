import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexJointKernel
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveFixedVector
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPlaneImage

/-! An actual projective D highest-root element has a unique actual
natural representative among conjugate highest roots. Four actual
linear forms have a common nonzero kernel vector in dimension >=8;
that vector removes the possible scalar between representatives.
No lifting of arbitrary projective automorphisms is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootLift
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexPairOperator CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexProjectiveUnipotent
open CFSGOrthogonalDIndexProjectiveFixedVector CFSGOrthogonalDIndexJointKernel
open CFSGAlternatingPairOperator
variable (K : Type) [Field K]

theorem conjugate_highestRoot_fixed_of_two_forms_zero (s : ℕ)
    (g : elementaryRootGroup K (s + 4)) (a : K) (x : Index (s + 4) → K)
    (h0 : (splitQuadraticForm K (s + 4)).polarBilin
      ((g.val : Mat K (s + 4)) *ᵥ firstVector K s) x = 0)
    (h1 : (splitQuadraticForm K (s + 4)).polarBilin
      ((g.val : Mat K (s + 4)) *ᵥ secondVector K s) x = 0) :
    ((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) *ᵥ x = x := by
  have hz : Matrix.mulVecLin
      (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) x = 0 := by
    rw [conjugate_highestRoot_displacement_pairOperator]
    simp only [LinearMap.smul_apply, pairOperator_apply, h0, h1, zero_smul, sub_self, smul_zero]
  change ((((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) *ᵥ x) = 0 at hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hz
  exact sub_eq_zero.mp hz

theorem conjugate_highestRoot_eq_of_projective_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) (a b : K)
    (he : projection K s (g * highestRoot K s a * g⁻¹) =
      projection K s (h * highestRoot K s b * h⁻¹)) :
    g * highestRoot K s a * g⁻¹ = h * highestRoot K s b * h⁻¹ := by
  let B := (splitQuadraticForm K (s + 4)).polarBilin
  let f : Fin 4 → Module.Dual K (Index (s + 4) → K) := fun i =>
    if i = 0 then B ((g.val : Mat K (s + 4)) *ᵥ firstVector K s)
    else if i = 1 then B ((g.val : Mat K (s + 4)) *ᵥ secondVector K s)
    else if i = 2 then B ((h.val : Mat K (s + 4)) *ᵥ firstVector K s)
    else B ((h.val : Mat K (s + 4)) *ᵥ secondVector K s)
  obtain ⟨x, hx, hz⟩ := exists_nonzero_joint_kernel f (by
    rw [Fintype.card_fin, naturalSpace_finrank]
    omega)
  apply eq_of_projective_eq_of_joint_fixed K s _ _ he x hx
  · apply conjugate_highestRoot_fixed_of_two_forms_zero K s g a x
    · simpa only [f, if_pos rfl] using hz (0 : Fin 4)
    · simpa [f] using hz (1 : Fin 4)
  · apply conjugate_highestRoot_fixed_of_two_forms_zero K s h b x
    · simpa [f] using hz (2 : Fin 4)
    · simpa [f] using hz (3 : Fin 4)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootLift
