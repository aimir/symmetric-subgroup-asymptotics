import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear

/-! A hyperbolic pole pair makes the singular vectors span even when
the remaining quadratic space is anisotropic. The explicit decomposition
uses three singular vectors and retains the quadratic norm in characteristic
two. Consequently linear maps agreeing on singular vectors agree everywhere. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicSpanning
open CFSGQuadraticHyperbolicShear
variable {K W T : Type*} [Field K] [AddCommGroup W] [Module K W]

theorem singular_decomposition (Q : QuadraticForm K W) (x : K × (W × K)) :
    x = (x.1 - 1) • (1, (0, 0)) + (1, (x.2.1, -Q x.2.1)) +
      (x.2.2 + Q x.2.1) • (0, (0, 1)) := by
  apply Prod.ext
  · change x.1 = (x.1 - 1) * 1 + 1 + (x.2.2 + Q x.2.1) * 0
    ring
  · apply Prod.ext
    · change x.2.1 = (x.1 - 1) • (0 : W) + x.2.1 + (x.2.2 + Q x.2.1) • 0
      simp only [smul_zero, zero_add, add_zero]
    · change x.2.2 = (x.1 - 1) * 0 + -Q x.2.1 + (x.2.2 + Q x.2.1) * 1
      ring

theorem singular_span_eq_top (Q : QuadraticForm K W) :
    Submodule.span K {x : K × (W × K) | norm Q x = 0} = ⊤ := by
  apply top_unique
  intro x _
  have he : (1, ((0 : W), (0 : K))) ∈
      Submodule.span K {x : K × (W × K) | norm Q x = 0} :=
    Submodule.subset_span (by simp [norm])
  have hf : (0, ((0 : W), (1 : K))) ∈
      Submodule.span K {x : K × (W × K) | norm Q x = 0} :=
    Submodule.subset_span (by simp [norm])
  have hz : (1, (x.2.1, -Q x.2.1)) ∈
      Submodule.span K {x : K × (W × K) | norm Q x = 0} :=
    Submodule.subset_span (by simp [norm])
  rw [singular_decomposition Q x]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ he) hz)
    (Submodule.smul_mem _ _ hf)

theorem linearMap_ext_of_singular [AddCommGroup T] [Module K T]
    (Q : QuadraticForm K W) (f g : (K × (W × K)) →ₗ[K] T)
    (h : ∀ x, norm Q x = 0 → f x = g x) : f = g := by
  apply LinearMap.ext
  intro x
  have he := h (1, (0, 0)) (by simp [norm])
  have hf := h (0, (0, 1)) (by simp [norm])
  have hz := h (1, (x.2.1, -Q x.2.1)) (by simp [norm])
  conv_lhs => rw [singular_decomposition Q x]
  conv_rhs => rw [singular_decomposition Q x]
  simp only [map_add, map_smul, he, hf, hz]

end SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicSpanning
