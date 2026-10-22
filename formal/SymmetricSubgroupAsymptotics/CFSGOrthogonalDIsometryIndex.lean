import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexComponentCover
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex
import SymmetricSubgroupAsymptotics.CFSGIndexFromSubgroupCosetCover

/-! The original elementary split-D group has index at most TWO in the
actual quadratic even component, and at most FOUR in the full quadratic
isometry group. These include characteristic two; determinant alone is
not a component test. The proof uses actual one-sided root-word cosets
and the actual finite-field square subgroup, with no named Ω identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndex
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIsometryIndexComponents CFSGOrthogonalDIsometryIndexLastDiagonal
open CFSGOrthogonalDIsometryIndexLastSquares CFSGOrthogonalDIsometryIndexComponentCover
open CFSGOrthogonalDIsometryIndexGeneralLinearLift
variable (K : Type) [Field K] [Finite K]

theorem elementary_component_index_le_two (s : ℕ) :
    ((elementaryRootGroup K (s + 4)).subgroupOf (componentMatrices K (s + 4))).index ≤ 2 := by
  let f := lastDiagonalHom K (s + 3)
  let N := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hf : ∀ a : Kˣ, f a ∈ componentMatrices K (s + 4) := by
    intro a
    rw [lastDiagonalHom_eq_lift]
    exact generalLinearLift_mem_component K (s + 4) _
  have hN : ∀ a ∈ N, f a ∈ elementaryRootGroup K (s + 4) := by
    rintro a ⟨b, rfl⟩
    exact last_square_mem K (s + 2) b
  have hc : ∀ g ∈ componentMatrices K (s + 4), ∃ a : Kˣ,
      (f a)⁻¹ * g ∈ elementaryRootGroup K (s + 4) := by
    intro g hg
    obtain ⟨a, e, he⟩ := component_one_sided_factor K s ⟨g, hg⟩
    refine ⟨a, ?_⟩
    change (lastDiagonalHom K (s + 3) a)⁻¹ * g ∈ elementaryRootGroup K (s + 4)
    change g = lastDiagonalHom K (s + 3) a * e.val at he
    rw [he, inv_mul_cancel_left]
    exact e.property
  exact (CFSGIndexFromSubgroupCosetCover.index_le_of_parameter_subgroup
    (elementaryRootGroup K (s + 4)) (componentMatrices K (s + 4)) f hf N hN hc).trans
      (CFSGFiniteFieldSquareIndex.squares_index_le_two K)

theorem elementary_quadratic_isometry_index_le_four (s : ℕ) :
    ((elementaryRootGroup K (s + 4)).subgroupOf (quadraticPreserving K (s + 4))).index ≤ 4 := by
  change (elementaryRootGroup K (s + 4)).relIndex (quadraticPreserving K (s + 4)) ≤ 4
  rw [← Subgroup.relIndex_mul_relIndex (elementaryRootGroup K (s + 4))
    (componentMatrices K (s + 4)) (quadraticPreserving K (s + 4))
      (elementary_le_componentMatrices K s) (componentMatrices_le_quadraticPreserving K (s + 4))]
  exact Nat.mul_le_mul (elementary_component_index_le_two K s) (componentMatrices_index_le_two K (s + 4))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndex
