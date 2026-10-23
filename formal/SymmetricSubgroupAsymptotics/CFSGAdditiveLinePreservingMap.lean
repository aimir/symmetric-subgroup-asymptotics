import Mathlib.LinearAlgebra.StdBasis

/-! An additive map preserving every vector line in dimension at least two
is a scalar map. Linearity over the coefficient field is a conclusion,
not an input. This is the elementary rigidity needed to compare two
sesquilinear forms before their field components have been identified. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveLinePreservingMap
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem exists_scalar (T : (I → K) →+ (I → K))
    (hT : ∀ v, ∃ c : K, T v = c • v) (i₀ i₁ : I) (hne : i₀ ≠ i₁) :
    ∃ c : K, ∀ v, T v = c • v := by
  classical
  choose a ha using hT
  let c := a (Pi.single i₀ 1)
  have hb (i : I) : T (Pi.single i 1) = c • Pi.single i 1 := by
    rw [ha]
    by_cases hi : i = i₀
    · subst i; rfl
    have hh := ha (Pi.single i₀ 1 + Pi.single i 1)
    rw [map_add, ha, ha] at hh
    have hc₀ := congrFun hh i₀
    have hc := congrFun hh i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      hi, Ne.symm hi, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at hc₀ hc
    change a (Pi.single i 1) • Pi.single i 1 = a (Pi.single i₀ 1) • Pi.single i 1
    rw [hc₀, hc]
  have hs (i : I) (t : K) : T (Pi.single i t) = c • Pi.single i t := by
    obtain ⟨j, hj⟩ : ∃ j : I, i ≠ j := by
      by_cases h : i = i₀
      · exact ⟨i₁, h ▸ hne⟩
      · exact ⟨i₀, h⟩
    have hh := ha (Pi.single i t + Pi.single j 1)
    rw [map_add, ha, hb] at hh
    have hi := congrFun hh i
    have hj' := congrFun hh j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      hj, Ne.symm hj, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at hi hj'
    have hct : a (Pi.single i t) * t = c * t := hi.trans (by rw [← hj'])
    rw [ha]
    funext k
    by_cases hk : k = i
    · subst k
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] using hct
    · simp [Pi.smul_apply, Pi.single_apply, hk]
  refine ⟨c, ?_⟩
  intro v
  calc
    T v = T (∑ i : I, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i : I, T (Pi.single i (v i)) := map_sum T _ _
    _ = ∑ i : I, c • Pi.single i (v i) := by congr 1; funext i; exact hs i (v i)
    _ = c • v := by rw [← Finset.smul_sum, Finset.univ_sum_single]

end SymmetricSubgroupAsymptotics.CFSGAdditiveLinePreservingMap
