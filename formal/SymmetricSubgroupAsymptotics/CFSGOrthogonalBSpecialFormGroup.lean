import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexDeterminant
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Literal determinant-one isometries of the original B Gram matrix.
The elementary subgroup is included by its checked actual root words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm
variable (K : Type) [Field K]

def specialFormUnits (n : ℕ) : Subgroup ((Mat K n)ˣ) :=
  formUnits K n ⊓ (Matrix.GeneralLinearGroup.det : (Mat K n)ˣ →* Kˣ).ker

theorem mem_specialFormUnits_iff (n : ℕ) (g : (Mat K n)ˣ) :
    g ∈ specialFormUnits K n ↔
      (g : Mat K n).transpose * gram K n * (g : Mat K n) = gram K n ∧
        (g : Mat K n).det = 1 := by
  constructor
  · intro hg
    exact ⟨hg.1, congrArg (fun a : Kˣ => (a : K)) hg.2⟩
  · rintro ⟨hf, hd⟩
    refine ⟨hf, ?_⟩
    apply Units.ext
    exact hd

theorem elementary_le_specialFormUnits (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (n : ℕ) :
    elementaryRootGroup K n ≤ specialFormUnits K n := by
  intro g hg
  apply (mem_specialFormUnits_iff K n g).mpr
  exact ⟨elementary_le_formUnits h2 n hg,
    CFSGOrthogonalBIndexDeterminant.elementary_det_eq_one K p n ⟨g, hg⟩⟩

theorem pairing_invariant (n : ℕ) (g : formUnits K n) (v w : Index n → K) :
    (gram K n).toBilin' ((g.val : Mat K n) *ᵥ v) ((g.val : Mat K n) *ᵥ w) =
      (gram K n).toBilin' v w := by
  have hf : (g.val : Mat K n).transpose * gram K n * (g.val : Mat K n) = gram K n :=
    g.property
  have hb : (gram K n).toBilin'.comp (g.val : Mat K n).toLin'
      (g.val : Mat K n).toLin' = (gram K n).toBilin' := by
    rw [Matrix.toBilin'_comp, hf]
  exact congrArg (fun B : LinearMap.BilinForm K (Index n → K) => B v w) hb

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup
