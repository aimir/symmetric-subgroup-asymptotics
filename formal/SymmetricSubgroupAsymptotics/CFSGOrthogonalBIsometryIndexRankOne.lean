import SymmetricSubgroupAsymptotics.CFSGIndexFromCosetCover
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneCover

/-! The actual original elementary B1 subgroup has index at most two
in the literal determinant-one isometry group. The only finite-field
count is the index of squares in Kˣ; no PSL2/SO3 recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOne
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBIsometryIndexRankOneDiagonal
variable (K : Type) [Field K]

def specialDiagonal : Kˣ →* specialFormUnits K 1 :=
  (diagonalHom K).codRestrict (specialFormUnits K 1) (fun a =>
    (mem_specialFormUnits_iff K 1 _).mpr
      ⟨diagonalHom_preserves K a, diagonalHom_det K a⟩)

theorem elementary_index_le_two [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) :
    ((elementaryRootGroup K 1).subgroupOf (specialFormUnits K 1)).index ≤ 2 := by
  let H := (elementaryRootGroup K 1).subgroupOf (specialFormUnits K 1)
  let N := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hN : N ≤ H.comap (specialDiagonal K) := by
    rintro a ⟨b, rfl⟩
    exact square_diagonal_mem K b
  have hc : ∀ g : specialFormUnits K 1, ∃ a : Kˣ,
      (specialDiagonal K a)⁻¹ * g ∈ H := by
    intro g
    obtain ⟨a, ha⟩ := CFSGOrthogonalBIsometryIndexRankOneCover.one_sided_cover K p h2 g
    exact ⟨a, ha⟩
  exact (CFSGIndexFromCosetCover.index_le_of_parameter_subgroup H
    (specialDiagonal K) N hN hc).trans
      (CFSGFiniteFieldSquareIndex.squares_index_le_two K)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOne
