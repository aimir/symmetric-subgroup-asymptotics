import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import Lean.Elab.Tactic.Omega

/-! Actual normalizer flag induction from quadratic-singular test
vectors. The subgroup must already act trivially on the flag quotients;
this premise is not inferred merely from an ambient Sylow's existence. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGQuadraticFlagNormalizer
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem preserves_flag (ρ : G →* (V ≃ₗ[K] V)) (Q : QuadraticForm K V)
    (F : ℕ → Submodule K V) (r : ℕ) (hzero : F 0 = ⊥)
    (hQ : ∀ g v, Q (ρ g v) = Q v)
    (hsingular : ∀ k, k ≤ r → ∀ v ∈ F k, Q v = 0)
    (P : Subgroup G) (T : Set G) (hTP : T ⊆ P)
    (hfixed : ∀ k, k < r → ∀ p ∈ P, ∀ v ∈ F (k + 1), ρ p v - v ∈ F k)
    (hrecover : ∀ k, k < r → ∀ v, Q v = 0 →
      (∀ t ∈ T, ρ t v - v ∈ F k) → v ∈ F (k + 1))
    (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    ∀ k, k ≤ r → ∀ v ∈ F k, ρ g v ∈ F k := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    have hv0 : v = 0 := by simpa only [hzero, Submodule.mem_bot] using hv
    rw [hv0, map_zero]
    exact (F 0).zero_mem
  | succ k ih =>
    intro hk v hv
    apply hrecover k (by omega) (ρ g v)
    · rw [hQ]
      exact hsingular (k + 1) hk v hv
    · intro t ht
      let c : G := g⁻¹ * t * g
      have hc : c ∈ P := (Subgroup.mem_normalizer_iff''.mp hg t).mp (hTP ht)
      have hd := hfixed k (by omega) c hc v hv
      have himage := ih (by omega) (ρ c v - v) hd
      have he : g * c = t * g := by dsimp only [c]; group
      have hact : ρ g (ρ c v) = ρ t (ρ g v) := by
        have h := congrArg (fun f : V ≃ₗ[K] V => f v) (congrArg ρ he)
        simpa only [map_mul, LinearEquiv.mul_apply] using h
      simpa only [map_sub, hact] using himage

end SymmetricSubgroupAsymptotics.CFSGQuadraticFlagNormalizer
