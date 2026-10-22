import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction

/-! An actual paired relative-root word clears the last conjugate pair
of a fixed vector when its preceding negative coordinate is nonzero.
No fixed-group generation theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDForkClear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDForkPairAction

theorem exists_clear_last_pair (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (hσ : Function.Involutive σ) (v : Index (s + 2) → K)
    (hb : v (Sum.inr (pen s)) ≠ 0)
    (hbσ : σ (v (Sum.inr (pen s))) = v (Sum.inr (pen s)))
    (hvσ : v (Sum.inr (last s)) = σ (v (Sum.inl (last s)))) :
    ∃ t : K,
      ((forkPair K s t (σ t) : Mat K (s + 2)) *ᵥ v) (Sum.inl (last s)) = 0 ∧
      ((forkPair K s t (σ t) : Mat K (s + 2)) *ᵥ v) (Sum.inr (last s)) = 0 := by
  let t := σ (v (Sum.inl (last s))) / v (Sum.inr (pen s))
  have htσ : σ t = v (Sum.inl (last s)) / v (Sum.inr (pen s)) := by
    dsimp only [t]
    rw [map_div₀, hσ, hbσ]
  refine ⟨t, ?_, ?_⟩
  · rw [CFSGOrthogonalDForkPairAction.positive_last, htσ, div_mul_cancel₀ _ hb, sub_self]
  · rw [CFSGOrthogonalDForkPairAction.negative_last, hvσ]
    dsimp only [t]
    rw [div_mul_cancel₀ _ hb, sub_self]

end SymmetricSubgroupAsymptotics.CFSGTwistedDForkClear
