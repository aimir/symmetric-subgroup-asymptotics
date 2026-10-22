import SymmetricSubgroupAsymptotics.CFSGOrthogonalBConjugateRootPlanes
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The SAME natural plane labelled by an actual conjugate long-root
subgroup is totally singular for the original preserved B Gram form.
This proves a label property; it is not a polar orbit/classifier input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

def IsTotallySingular (s : ℕ) (P : Submodule K (Index (s + 3) → K)) : Prop :=
  ∀ v ∈ P, ∀ w ∈ P, (gram K (s + 3)).toBilin' v w = 0

theorem standardRootPlane_totallySingular (s : ℕ) :
    IsTotallySingular (K := K) s (standardRootPlane s) := by
  have hzero (i j : Fin (s + 3)) :
      (gram K (s + 3)).toBilin' (positiveVector s i) (positiveVector s j) = 0 := by
    simp only [positiveVector, Matrix.toBilin'_single, gram, pos]
  intro v hv w hw
  obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hv
  obtain ⟨c, d, rfl⟩ := (Submodule.mem_span_pair).mp hw
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hzero, smul_zero, add_zero]

theorem natural_pairing_invariant (h2 : (2 : K) ≠ 0) (n : ℕ)
    (g : elementaryRootGroup K n) (v w : Index n → K) :
    (gram K n).toBilin' ((g.val : Mat K n) *ᵥ v) ((g.val : Mat K n) *ᵥ w) =
      (gram K n).toBilin' v w := by
  have hf := CFSGOrthogonalBIndexForm.elementary_le_formUnits h2 n g.property
  change (g.val : Mat K n).transpose * gram K n * (g.val : Mat K n) = gram K n at hf
  have hb : (gram K n).toBilin'.comp (g.val : Mat K n).toLin' (g.val : Mat K n).toLin' =
      (gram K n).toBilin' := by
    rw [Matrix.toBilin'_comp, hf]
  have he := congrArg (fun B : LinearMap.BilinForm K (Index n → K) => B v w) hb
  exact he

theorem conjugateRootPlane_totallySingular (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) :
    IsTotallySingular s (conjugateRootPlane (K := K) s g) := by
  rintro v ⟨v0, hv0, rfl⟩ w ⟨w0, hw0, rfl⟩
  change (gram K (s + 3)).toBilin' ((g.val : Mat K (s + 3)) *ᵥ v0)
    ((g.val : Mat K (s + 3)) *ᵥ w0) = 0
  rw [natural_pairing_invariant h2]
  exact standardRootPlane_totallySingular s v0 hv0 w0 hw0

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
