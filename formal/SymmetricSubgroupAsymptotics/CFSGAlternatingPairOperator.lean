import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module

/-! The literal rank-two skew operator attached to a bilinear form and
an ordered pair of vectors. A basis change in the SAME two-plane
scales it by its determinant; no geometric recognition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def pairOperator (B : LinearMap.BilinForm K V) (u v : V) : V →ₗ[K] V :=
  (B v).smulRight u - (B u).smulRight v

@[simp] theorem pairOperator_apply (B : LinearMap.BilinForm K V) (u v x : V) :
    pairOperator B u v x = B v x • u - B u x • v := rfl

theorem pairOperator_basisChange (B : LinearMap.BilinForm K V) (u v : V) (a b c d : K) :
    pairOperator B (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) • pairOperator B u v := by
  apply LinearMap.ext
  intro x
  simp only [pairOperator_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  module

theorem pairOperator_mem_span (B : LinearMap.BilinForm K V) (u v u' v' : V)
    (hu : u' ∈ Submodule.span K {u, v}) (hv : v' ∈ Submodule.span K {u, v}) :
    ∃ d : K, pairOperator B u' v' = d • pairOperator B u v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
  exact ⟨a * d - b * c, pairOperator_basisChange B u v a b c d⟩

theorem pairOperator_intertwines (B : LinearMap.BilinForm K V) (L : V →ₗ[K] V)
    (hL : ∀ x y, B (L x) (L y) = B x y) (u v x : V) :
    L (pairOperator B u v x) = pairOperator B (L u) (L v) (L x) := by
  simp only [pairOperator_apply, map_sub, map_smul, hL]

theorem pairOperator_conjugation (B : LinearMap.BilinForm K V) (L R : V →ₗ[K] V)
    (hL : ∀ x y, B (L x) (L y) = B x y) (hLR : ∀ x, L (R x) = x) (u v : V) :
    (L.comp (pairOperator B u v)).comp R = pairOperator B (L u) (L v) := by
  apply LinearMap.ext
  intro x
  change L (pairOperator B u v (R x)) = pairOperator B (L u) (L v) x
  rw [pairOperator_intertwines B L hL, hLR]

end SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
