import SymmetricSubgroupAsymptotics.CFSGQuadraticFlagNormalizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! A genuine ambient conjugator is forced to preserve singular flag
prefixes by the test-root recovery property. Equality follows by finite
dimension, and the original conjugate subgroup then acts trivially on
the SAME standard flag quotients. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGQuadraticFlagConjugator
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem preserves_flag (ρ : G →* (V ≃ₗ[K] V)) (Q : QuadraticForm K V)
    (F : ℕ → Submodule K V) (basisVector : ℕ → V) (r : ℕ) (hzero : F 0 = ⊥)
    (hspan : ∀ k, k < r → F (k + 1) = F k ⊔ Submodule.span K {basisVector k})
    (hQ : ∀ g v, Q (ρ g v) = Q v)
    (hsingular : ∀ k, k < r → Q (basisVector k) = 0)
    (U : Subgroup G) (T : Set G) (a : G)
    (hconj : ∀ t ∈ T, a⁻¹ * t * a ∈ U)
    (hUfixed : ∀ k, k < r → ∀ u ∈ U, ρ u (basisVector k) - basisVector k ∈ F k)
    (hrecover : ∀ k, k < r → ∀ v, Q v = 0 →
      (∀ t ∈ T, ρ t v - v ∈ F k) → v ∈ F (k + 1)) :
    ∀ k, k ≤ r → ∀ v ∈ F k, ρ a v ∈ F k := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    have hv0 : v = 0 := by simpa only [hzero, Submodule.mem_bot] using hv
    rw [hv0, map_zero]
    exact (F 0).zero_mem
  | succ k ih =>
    intro hk v hv
    have hklt : k < r := by omega
    have hmon : F k ≤ F (k + 1) := by rw [hspan k hklt]; exact le_sup_left
    have hvec : ρ a (basisVector k) ∈ F (k + 1) := by
      apply hrecover k hklt (ρ a (basisVector k))
      · rw [hQ]
        exact hsingular k hklt
      · intro t ht
        let c : G := a⁻¹ * t * a
        have hd := hUfixed k hklt c (hconj t ht)
        have himage := ih (by omega) (ρ c (basisVector k) - basisVector k) hd
        have he : a * c = t * a := by dsimp only [c]; group
        have hact : ρ a (ρ c (basisVector k)) = ρ t (ρ a (basisVector k)) := by
          have h := congrArg (fun f : V ≃ₗ[K] V => f (basisVector k)) (congrArg ρ he)
          simpa only [map_mul, LinearEquiv.mul_apply] using h
        simpa only [map_sub, hact] using himage
    rw [hspan k hklt] at hv
    rcases Submodule.mem_sup.mp hv with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    rw [map_add, map_smul]
    exact (F (k + 1)).add_mem (hmon (ih (by omega) x hx)) ((F (k + 1)).smul_mem c hvec)

theorem map_eq_of_preserves [FiniteDimensional K V] (a : V ≃ₗ[K] V)
    (F : Submodule K V) (hF : ∀ v ∈ F, a v ∈ F) : F.map a.toLinearMap = F := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    exact hF v hv
  · exact a.finrank_map_eq F

theorem fixed_on_flag_of_conjugate (ρ : G →* (V ≃ₗ[K] V))
    (F : ℕ → Submodule K V) (r : ℕ) (U : Subgroup G) (a : G)
    (hmap : ∀ k, k ≤ r → (F k).map (ρ a).toLinearMap = F k)
    (hUfixed : ∀ k, k < r → ∀ u ∈ U, ∀ v ∈ F (k + 1), ρ u v - v ∈ F k)
    (p : G) (hp : a⁻¹ * p * a ∈ U) :
    ∀ k, k < r → ∀ v ∈ F (k + 1), ρ p v - v ∈ F k := by
  intro k hk v hv
  rw [← hmap (k + 1) (by omega)] at hv
  rcases hv with ⟨w, hw, rfl⟩
  let c : G := a⁻¹ * p * a
  have hd := hUfixed k hk c hp w hw
  have himage : ρ a (ρ c w - w) ∈ F k := by
    rw [← hmap k (by omega)]
    exact ⟨ρ c w - w, hd, rfl⟩
  have he : a * c = p * a := by dsimp only [c]; group
  have hact : ρ a (ρ c w) = ρ p (ρ a w) := by
    have h := congrArg (fun f : V ≃ₗ[K] V => f w) (congrArg ρ he)
    simpa only [map_mul, LinearEquiv.mul_apply] using h
  simpa only [map_sub, hact] using himage

end SymmetricSubgroupAsymptotics.CFSGQuadraticFlagConjugator
