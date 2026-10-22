import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryCover
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonalSquares
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex
import SymmetricSubgroupAsymptotics.CFSGIndexFromCosetCover

/-! The SAME original B elementary group has index at most two in the
literal determinant-one isometry group, in every positive rank over an
odd finite field. The proof is an actual coset cover and explicit square
words, with no named classical-group recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryIndex
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBLastDiagonal
variable (K : Type) [Field K]

def specialLastDiagonal (s : ℕ) : Kˣ →* specialFormUnits K (s + 1) :=
  (lastDiagonalHom K s).codRestrict (specialFormUnits K (s + 1))
    (fun t => lastDiagonalHom_mem_special K s t)

theorem elementary_index_le_two [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    ((elementaryRootGroup K (s + 1)).subgroupOf (specialFormUnits K (s + 1))).index ≤ 2 := by
  let H := (elementaryRootGroup K (s + 1)).subgroupOf (specialFormUnits K (s + 1))
  let N := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hN : N ≤ H.comap (specialLastDiagonal K s) := by
    rintro t ⟨a, rfl⟩
    exact CFSGOrthogonalBLastDiagonalSquares.square_lastDiagonal_mem K s a
  have hcover : ∀ g : specialFormUnits K (s + 1), ∃ t : Kˣ,
      (specialLastDiagonal K s t)⁻¹ * g ∈ H := by
    intro g
    obtain ⟨t, ht⟩ := CFSGOrthogonalBSpecialIsometryCover.special_one_sided_cover K p h2 s g
    exact ⟨t, ht⟩
  exact (CFSGIndexFromCosetCover.index_le_of_parameter_subgroup H
    (specialLastDiagonal K s) N hN hcover).trans
      (CFSGFiniteFieldSquareIndex.squares_index_le_two K)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryIndex
