import SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Over a nondegenerate symmetric form, skew maps with disjoint actual
ranges have additive ranks. This supplies the intersection test needed
when a product of long roots still has displacement rank at most two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem disjoint_skew_ranges_rank_add (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) (A C : V →ₗ[K] V)
    (hA : ∀ x y, B (A x) y = -B x (A y))
    (hC : ∀ x y, B (C x) y = -B x (C y))
    (hd : Disjoint (LinearMap.range A) (LinearMap.range C)) :
    Module.finrank K (LinearMap.range (A + C)) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range C) := by
  have hk : LinearMap.ker (A + C) = LinearMap.ker A ⊓ LinearMap.ker C := by
    ext x
    constructor
    · intro hx
      change A x + C x = 0 at hx
      have he : A x = -C x := eq_neg_of_add_eq_zero_left hx
      have ha : A x ∈ (LinearMap.range A) ⊓ (LinearMap.range C) := by
        refine ⟨⟨x, rfl⟩, ⟨-x, ?_⟩⟩
        rw [map_neg]
        exact he.symm
      have haz : A x = 0 := hd.le_bot ha
      have hcz : C x = 0 := by simpa only [haz, zero_add] using hx
      exact ⟨haz, hcz⟩
    · rintro ⟨ha, hc⟩
      change A x + C x = 0
      change A x = 0 at ha
      change C x = 0 at hc
      rw [ha, hc, add_zero]
  have hsup : LinearMap.ker A ⊔ LinearMap.ker C = ⊤ := by
    rw [skew_ker_eq_orthogonal_range B hB A hA, skew_ker_eq_orthogonal_range B hB C hC,
      ← orthogonal_inf B hB hs, hd.eq_bot, B.orthogonal_bot]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker A) (LinearMap.ker C)
  rw [hsup, ← hk, finrank_top] at hdim
  have h1 := LinearMap.finrank_range_add_finrank_ker A
  have h2 := LinearMap.finrank_range_add_finrank_ker C
  have h3 := LinearMap.finrank_range_add_finrank_ker (A + C)
  omega

end SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
