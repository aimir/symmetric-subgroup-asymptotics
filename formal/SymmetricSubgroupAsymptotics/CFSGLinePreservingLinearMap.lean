import Mathlib.LinearAlgebra.StdBasis

/-! A linear endomorphism preserving every literal vector line is
scalar. The scalar is fixed by one basis vector and compared on sums
of two basis vectors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinePreservingLinearMap
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem exists_scalar (T : Module.End K (n → K))
    (hT : ∀ v, ∃ c : K, T v = c • v) (i₀ : n) :
    ∃ c : K, T = c • LinearMap.id := by
  classical
  choose a ha using hT
  refine ⟨a (Pi.single i₀ 1), ?_⟩
  apply (Pi.basisFun K n).ext
  intro i
  simp only [Pi.basisFun_apply, LinearMap.smul_apply, LinearMap.id_apply]
  change T (Pi.single i 1) = a (Pi.single i₀ 1) • Pi.single i 1
  rw [ha]
  by_cases hi : i = i₀
  · subst i; rfl
  have hh := ha (Pi.single i₀ 1 + Pi.single i 1)
  rw [map_add, ha, ha] at hh
  have hc₀ := congrFun hh i₀
  have hc := congrFun hh i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    hi, Ne.symm hi, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add] at hc₀ hc
  rw [hc₀, hc]

end SymmetricSubgroupAsymptotics.CFSGLinePreservingLinearMap
