import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndex
import Mathlib.Algebra.CharP.Reduced

/-! In a finite characteristic-two field every unit is an actual square.
The proved one-sided coset cover then identifies the SAME elementary
subgroup with the genuine quadratic even component. The full quadratic
isometry index improves to two without a determinant criterion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCharTwo
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIsometryIndexComponents CFSGOrthogonalDIsometryIndexLastSquares
open CFSGOrthogonalDIsometryIndexComponentCover
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem unit_is_square (a : Kˣ) : ∃ b : Kˣ, b ^ 2 = a := by
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (a : K)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hc
    exact a.ne_zero hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two] using hc.symm

theorem elementary_eq_component (s : ℕ) :
    elementaryRootGroup K (s + 4) = componentMatrices K (s + 4) := by
  apply le_antisymm (elementary_le_componentMatrices K s)
  intro g hg
  obtain ⟨a, e, he⟩ := component_one_sided_factor K s ⟨g, hg⟩
  obtain ⟨b, hb⟩ := unit_is_square K a
  change g = lastDiagonalHom K (s + 3) a * e.val at he
  rw [he, ← hb]
  exact (elementaryRootGroup K (s + 4)).mul_mem (last_square_mem K (s + 2) b) e.property

theorem elementary_quadratic_isometry_index_le_two (s : ℕ) :
    ((elementaryRootGroup K (s + 4)).subgroupOf (quadraticPreserving K (s + 4))).index ≤ 2 := by
  rw [elementary_eq_component K s]
  exact componentMatrices_index_le_two K (s + 4)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCharTwo
