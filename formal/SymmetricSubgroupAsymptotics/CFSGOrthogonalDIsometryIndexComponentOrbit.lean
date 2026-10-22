import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents

/-! The actual elementary group normalizes the positive-space image of
an actual EVEN-component matrix back to the positive space. The crossed
alternative is excluded by its proved distance one; determinant is not
used to define the component, including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentOrbit
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveGraph
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit CFSGOrthogonalDIsometryIndexCrossingSpaces
variable (K : Type) [Field K]

theorem exists_elementary_positive_alignment (s : ℕ) (g : componentMatrices K (s + 4)) :
    ∃ e : elementaryRootGroup K (s + 4),
      ((positiveSpace K (s + 4)).map (ambientLinearEquiv K (s + 4) g.val).toLinearMap).map
        (naturalLinearHom K (s + 4) e).toLinearMap = positiveSpace K (s + 4) := by
  let P : Subspaces (splitQuadraticForm K (s + 4)) :=
    ⟨(positiveSpace K (s + 4)).map (ambientLinearEquiv K (s + 4) g.val).toLinearMap, by
      rintro x ⟨y, hy, rfl⟩
      exact (((mem_componentMatrices_iff K (s + 4) g.val).mp g.property).1 y).trans
        (positiveSpace_singular K (s + 4) ⟨y, hy⟩)⟩
  have hd : Module.finrank K P.val = s + 4 :=
    ((ambientLinearEquiv K (s + 4) g.val).finrank_map_eq (positiveSpace K (s + 4))).trans
      (positiveSpace_finrank K (s + 4))
  obtain ⟨e, he | ⟨j, he⟩⟩ := exists_normalize_full_rank K (s + 4) (by omega) P hd
  · exact ⟨e, he⟩
  · have hm : e.val * g.val ∈ componentMatrices K (s + 4) :=
      (componentMatrices K (s + 4)).mul_mem (elementary_le_componentMatrices K s e.property)
        g.property
    have hp := ((mem_componentMatrices_iff K (s + 4) (e.val * g.val)).mp hm).2
    have hmap : (positiveSpace K (s + 4)).map
        (ambientLinearEquiv K (s + 4) (e.val * g.val)).toLinearMap =
          P.val.map (naturalLinearHom K (s + 4) e).toLinearMap := by
      change (positiveSpace K (s + 4)).map
        (Matrix.mulVecLin ((e.val : Mat K (s + 4)) * (g.val : Mat K (s + 4)))) = _
      rw [Matrix.mulVecLin_mul, Submodule.map_comp]
      rfl
    rw [hmap, he, crossing_distance_one] at hp
    exact False.elim ((by decide : ¬Even (1 : ℕ)) hp)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentOrbit
