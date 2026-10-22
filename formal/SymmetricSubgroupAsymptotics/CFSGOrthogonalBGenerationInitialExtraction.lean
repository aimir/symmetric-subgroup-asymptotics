import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialTorusAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialCommutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter

/-! Actual first-stage odd B pair extraction. The generic primitive
scalar filter is applied to literal quadratic short roots and linear
chain roots, using the already-proved two actual torus actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialExtraction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationInitialCommutation CFSGOrthogonalBGenerationInitialTorusAction
open CFSGOrthogonalBGenerationCoxeter
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem initialMixedWeyl_val (s : ℕ) :
    (initialMixedWeyl K s).val = alphaUnit K s 1 * betaUnit K s 1 * (coxeterWeyl K (s + 2)).val := by
  change (alphaElement K s 1).val * (betaElement K s 1).val * (coxeterWeyl K (s + 2)).val = _
  rw [betaElement_val]
  rfl

theorem beta_line_and_cleaned_word (h2 : (2 : K) ≠ 0) (hcard : 3 ≤ Nat.card K)
    (s : ℕ) (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (Mat K (s + 3))ˣ)
    (hT : (initialTorus K h2 s g).val ∈ H) (hY : (initialMixedWeyl K s).val ∈ H) :
    (∀ a, betaUnit K s a ∈ H) ∧ alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val ∈ H := by
  have hy : alphaUnit K s 1 * betaUnit K s 1 * (coxeterWeyl K (s + 2)).val ∈ H := by
    rw [← initialMixedWeyl_val]
    exact hY
  have hB := CFSGOrthogonalDGenerationScalarFilter.second_line_of_pair hcard g hg
    (alphaUnit K s) (betaUnit K s) (alphaUnit_add K s) (alphaUnit_zero K s)
    (betaUnit_add K s) (betaUnit_zero K s) (alpha_beta_commute K s)
    (initialTorus K h2 s g).val (coxeterWeyl K (s + 2)).val (g : K)
    (initialTorus_alpha K h2 s g) (initialTorus_beta K h2 s g)
    (shiftedTorus_alpha K h2 s g) (shiftedTorus_beta K h2 s g)
    (shiftedTorus_commute K h2 s g) H hT hy
  refine ⟨hB, ?_⟩
  exact CFSGOrthogonalDGenerationScalarFilter.cleaned_word_mem
    (alphaUnit K s) (betaUnit K s) (alpha_beta_commute K s 1 1)
    (coxeterWeyl K (s + 2)).val H (hB 1) hy

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialExtraction
