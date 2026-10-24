import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleCoordinates
import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicSpanning

/-! Singular vectors span the SAME odd-B natural space. The original
middle coordinate is retained inside the smaller quadratic tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddSingularSpanning

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOddQuadraticForm
open CFSGOrthogonalBOddPoleCoordinates
variable (K : Type) [Field K]

theorem singular_span_eq_top (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Submodule.span K {v : Index (n + 1) → K | quadratic K (n + 1) v = 0} = ⊤ := by
  let S := Submodule.span K {v : Index (n + 1) → K | quadratic K (n + 1) v = 0}
  let E := coordinateEquiv K h2 n
  have hle : Submodule.span K
      {x : K × ((Index n → K) × K) |
        CFSGQuadraticHyperbolicShear.norm (quadratic K n) x = 0} ≤
        S.comap E.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.subset_span
    change quadratic K (n + 1) (E.symm x) = 0
    have h := quadratic_coordinates K h2 n (E.symm x)
    change quadratic K (n + 1) (E.symm x) =
      CFSGQuadraticHyperbolicShear.norm (quadratic K n) (E (E.symm x)) at h
    rw [E.apply_symm_apply] at h
    exact h.trans hx
  rw [CFSGQuadraticHyperbolicSpanning.singular_span_eq_top] at hle
  apply top_unique
  intro v _
  have hv := hle (show E v ∈ (⊤ : Submodule K (K × ((Index n → K) × K))) from trivial)
  change E.symm (E v) ∈ S at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddSingularSpanning
