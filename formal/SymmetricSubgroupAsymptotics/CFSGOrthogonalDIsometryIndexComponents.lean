import SymmetricSubgroupAsymptotics.CFSGQuadraticIsometryComponentIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentMatrices

/-! The actual even-component MATRIX subgroup has index at most two
in the SAME literal split-quadratic isometry group, in every field and
rank. This is the first factor in the later elementary-index problem;
no elementary/component equality or determinant criterion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponents
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexComponentMatrices
open CFSGOrthogonalDIndexSingularComponents
variable (K : Type) [Field K]

def quadraticIsometryEquiv (r : ℕ) : quadraticPreserving K r ≃*
    isometryGroup (splitQuadraticForm K r) where
  toFun g := ⟨ambientLinearEquiv K r g.val, by
    intro x
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact g.property x⟩
  invFun f := ⟨(ambientLinearEquiv K r).symm f.val, by
    intro x
    have hf := f.property x
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply] at hf
    change splitQ K (ambientLinearEquiv K r ((ambientLinearEquiv K r).symm f.val) x) = splitQ K x
    rw [(ambientLinearEquiv K r).apply_symm_apply]
    exact hf⟩
  left_inv g := Subtype.ext ((ambientLinearEquiv K r).symm_apply_apply g.val)
  right_inv f := Subtype.ext ((ambientLinearEquiv K r).apply_symm_apply f.val)
  map_mul' g h := Subtype.ext ((ambientLinearEquiv K r).map_mul g.val h.val)

theorem componentMatrices_le_quadraticPreserving (r : ℕ) :
    componentMatrices K r ≤ quadraticPreserving K r := by
  intro g hg x
  have hQ := ((mem_componentMatrices_iff K r g).mp hg).1 x
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply] at hQ
  exact hQ

theorem component_subgroupOf_eq_comap (r : ℕ) :
    (componentMatrices K r).subgroupOf (quadraticPreserving K r) =
      (componentStabilizer (splitQuadraticForm K r) (splitQuadraticForm_nondegenerate K r)
        r (naturalSpace_finrank K r) (positiveSpace K r) (positiveSpace_self_orthogonal K r)
        (positiveSpace_singular K r)).comap (quadraticIsometryEquiv K r).toMonoidHom := by
  ext g
  change g.val ∈ componentMatrices K r ↔
    Even (distance r (positiveSpace K r)
      ((positiveSpace K r).map (ambientLinearEquiv K r g.val).toLinearMap))
  rw [mem_componentMatrices_iff]
  constructor
  · exact fun h => h.2
  · intro he
    refine ⟨?_, he⟩
    intro x
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact g.property x

theorem componentMatrices_index_le_two (r : ℕ) :
    ((componentMatrices K r).subgroupOf (quadraticPreserving K r)).index ≤ 2 := by
  rw [component_subgroupOf_eq_comap]
  let C := componentStabilizer (splitQuadraticForm K r) (splitQuadraticForm_nondegenerate K r)
    r (naturalSpace_finrank K r) (positiveSpace K r) (positiveSpace_self_orthogonal K r)
    (positiveSpace_singular K r)
  have hidx := C.index_comap_of_surjective (f := (quadraticIsometryEquiv K r).toMonoidHom)
    (quadraticIsometryEquiv K r).surjective
  rw [hidx]
  exact CFSGQuadraticIsometryComponentIndex.componentStabilizer_index_le_two
    (splitQuadraticForm K r) (splitQuadraticForm_nondegenerate K r)
      r (naturalSpace_finrank K r) (positiveSpace K r) (positiveSpace_self_orthogonal K r)
      (positiveSpace_singular K r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponents
