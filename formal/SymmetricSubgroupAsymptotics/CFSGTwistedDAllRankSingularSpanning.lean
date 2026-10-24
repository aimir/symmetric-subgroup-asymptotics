import SymmetricSubgroupAsymptotics.CFSGTwistedDBasePoleCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularSpanning

/-! Singular spanning in every actual fixed natural rank, including
the genuine rank-two tail. Its anisotropic quadratic-extension norm
plane is retained in the literal base pole coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularSpanning

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDBasePoleCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedA2FixedField

theorem base_singular_span_eq_top (q : CFSG.PrimePower) :
    Submodule.span (fixedField q) {v : fixedSpace 0 q | fixedQuadraticForm 0 q v = 0} = ⊤ := by
  let S := Submodule.span (fixedField q)
    {v : fixedSpace 0 q | fixedQuadraticForm 0 q v = 0}
  let E := basePoleEquiv q
  have hle : Submodule.span (fixedField q)
      {x : fixedField q × (q.Extension 2 × fixedField q) |
        CFSGQuadraticHyperbolicShear.norm (normForm q) x = 0} ≤
        S.comap E.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.subset_span
    change fixedQuadraticForm 0 q (E.symm x) = 0
    rcases x with ⟨a, z, b⟩
    rw [quadratic_inv]
    exact hx
  rw [CFSGQuadraticHyperbolicSpanning.singular_span_eq_top] at hle
  apply top_unique
  intro v _
  have hv := hle (show E v ∈ (⊤ : Submodule (fixedField q)
    (fixedField q × (q.Extension 2 × fixedField q))) from trivial)
  change E.symm (E v) ∈ S at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

theorem singular_span_eq_top (n : ℕ) (q : CFSG.PrimePower) :
    Submodule.span (fixedField q) {v : fixedSpace n q | fixedQuadraticForm n q v = 0} = ⊤ := by
  cases n with
  | zero => exact base_singular_span_eq_top q
  | succ n => exact CFSGTwistedDSingularSpanning.singular_span_eq_top n q

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularSpanning
