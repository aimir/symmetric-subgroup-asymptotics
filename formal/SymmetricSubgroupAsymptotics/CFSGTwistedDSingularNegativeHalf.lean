import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist
import Mathlib.Algebra.BigOperators.Fin

/-! On the actual fork-fixed vector carrier, the final paired plane is
anisotropic. Thus vanishing untouched negative coordinates of a singular
vector forces the whole negative half and both final coordinates to vanish. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularNegativeHalf
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGOrthogonalDIndexBundledQuadratic

theorem vanishing_negative_half (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (v : Index (s + 2) → K) (hv : vectorTwist K s σ v = v)
    (hQ : splitQuadraticForm K (s + 2) v = 0)
    (hn : ∀ i : Fin (s + 1), v (Sum.inr i.castSucc) = 0) :
    v (Sum.inl (last s)) = 0 ∧ v ∘ Sum.inr = 0 := by
  have hnorm : v (Sum.inl (last s)) * v (Sum.inr (last s)) = 0 := by
    rw [splitQuadraticForm_apply] at hQ
    change (∑ i : Fin (s + 2), v (Sum.inl i) * v (Sum.inr i)) = 0 at hQ
    rw [Fin.sum_univ_castSucc] at hQ
    have hs : (∑ i : Fin (s + 1), v (Sum.inl i.castSucc) * v (Sum.inr i.castSucc)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hn i, mul_zero]
    simpa only [hs, zero_add, last] using hQ
  have hp : v (Sum.inl (last s)) = 0 := by
    rw [fixed_last_pair K s σ v hv] at hnorm
    rcases mul_eq_zero.mp hnorm with h | h
    · exact h
    · exact σ.injective (by simpa only [map_zero] using h)
  refine ⟨hp, ?_⟩
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact hn j
  · change v (Sum.inr (last s)) = 0
    rw [fixed_last_pair K s σ v hv, hp, map_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularNegativeHalf
