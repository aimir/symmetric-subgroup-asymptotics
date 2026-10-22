import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicCoset
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponents
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction

/-! Every actual even-component isometry is a one-sided diagonal coset
of the original elementary subgroup. Normalizing the INVERSE image of
the positive space, and then inverting, is essential: a double-coset
factorization alone would not give this assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentCover
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIsometryIndexComponents
open CFSGOrthogonalDIsometryIndexComponentOrbit CFSGOrthogonalDIsometryIndexLastSquares
open CFSGOrthogonalDIsometryIndexParabolicCoset
variable (K : Type) [Field K]

theorem component_one_sided_factor (s : ℕ) (g : componentMatrices K (s + 4)) :
    ∃ t : Kˣ, ∃ e : elementaryRootGroup K (s + 4),
      g.val = lastDiagonalHom K (s + 3) t * e.val := by
  obtain ⟨a, ha⟩ := exists_elementary_positive_alignment K s g⁻¹
  have hforward : (positiveSpace K (s + 4)).map
      (Matrix.mulVecLin ((a.val * g.val⁻¹ : (Mat K (s + 4))ˣ) : Mat K (s + 4))) =
        positiveSpace K (s + 4) := by
    rw [CFSGMatrixSubspaceUnitAction.map_mul]
    exact ha
  have hinv := CFSGMatrixSubspaceUnitAction.invariant_inverse
    (positiveSpace K (s + 4)) (a.val * g.val⁻¹) hforward
  let ga : quadraticPreserving K (s + 4) :=
    ⟨g.val * a.val⁻¹, (quadraticPreserving K (s + 4)).mul_mem
      (componentMatrices_le_quadraticPreserving K (s + 4) g.property)
      ((quadraticPreserving K (s + 4)).inv_mem (elementary_le_quadraticPreserving K s a.property))⟩
  have hga : (positiveSpace K (s + 4)).map
      (Matrix.mulVecLin (ga.val : Mat K (s + 4))) = positiveSpace K (s + 4) := by
    simpa only [mul_inv_rev, inv_inv] using hinv
  obtain ⟨t, e, he⟩ := parabolic_one_sided_factor K s ga hga
  refine ⟨t, e * a, ?_⟩
  have hh := congrArg (fun u : (Mat K (s + 4))ˣ => u * a.val) he
  change (g.val * a.val⁻¹) * a.val = (lastDiagonalHom K (s + 3) t * e.val) * a.val at hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one, Subgroup.coe_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentCover
