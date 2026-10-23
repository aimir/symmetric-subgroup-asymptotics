import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicSpanning
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar

/-! Singular vectors span the SAME actual defining-fixed quadratic
space. The pole decomposition includes its smaller fixed tail, and hence
also the anisotropic norm plane. No split-space replacement is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularSpanning
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedA2FixedField

theorem singular_span_eq_top (n : ℕ) (q : CFSG.PrimePower) :
    Submodule.span (fixedField q)
      {v : fixedSpace (n + 1) q | fixedQuadraticForm (n + 1) q v = 0} = ⊤ := by
  let S := Submodule.span (fixedField q)
    {v : fixedSpace (n + 1) q | fixedQuadraticForm (n + 1) q v = 0}
  have hle : Submodule.span (fixedField q)
      {x : fixedField q × (fixedSpace n q × fixedField q) |
        CFSGQuadraticHyperbolicShear.norm (fixedQuadraticForm n q) x = 0} ≤
        S.comap (poleEquiv n q).symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.subset_span
    change fixedQuadraticForm (n + 1) q ((poleEquiv n q).symm x) = 0
    rcases x with ⟨a, z, b⟩
    rw [quadratic_inv]
    exact hx
  rw [CFSGQuadraticHyperbolicSpanning.singular_span_eq_top] at hle
  apply top_unique
  intro v _
  have hv := hle (show (poleEquiv n q v) ∈ ⊤ from trivial)
  change (poleEquiv n q).symm (poleEquiv n q v) ∈ S at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

theorem linearMap_ext_of_singular (n : ℕ) (q : CFSG.PrimePower)
    {T : Type*} [AddCommGroup T] [Module (fixedField q) T]
    (f g : fixedSpace (n + 1) q →ₗ[fixedField q] T)
    (h : ∀ v, fixedQuadraticForm (n + 1) q v = 0 → f v = g v) : f = g := by
  have he : f.comp (poleEquiv n q).symm.toLinearMap =
      g.comp (poleEquiv n q).symm.toLinearMap := by
    apply CFSGQuadraticHyperbolicSpanning.linearMap_ext_of_singular (fixedQuadraticForm n q)
    intro x hx
    apply h
    rcases x with ⟨a, z, b⟩
    exact (quadratic_inv n q a b z).trans hx
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun he (poleEquiv n q v)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hv

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularSpanning
