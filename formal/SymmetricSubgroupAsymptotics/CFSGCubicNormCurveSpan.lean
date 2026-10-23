import SymmetricSubgroupAsymptotics.CFSGCubicNormMonomialSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! Linear spanning consequences of the cubic norm monomial separation.
The scalar field here is the full extension field K. Descent to the
Frobenius-fixed tensor space requires its own dimension argument; this
module does not identify that space with all of K^8 over the fixed field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCubicNormCurveSpan
open CFSGCubicNormMonomialSeparation

private theorem span_eq_top_of_coefficients_zero
    {K T I : Type*} [Field K] [Fintype I]
    (v : T → I → K)
    (h : ∀ c : I → K, (∀ t, ∑ i, c i * v t i = 0) → ∀ i, c i = 0) :
    Submodule.span K (Set.range v) = ⊤ := by
  classical
  by_contra hn
  obtain ⟨f, hf, hzero⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hn) inferInstance
  have hv (t : T) : f (v t) = 0 := by
    have hm : f (v t) ∈ (Submodule.span K (Set.range v)).map f :=
      Submodule.mem_map.mpr ⟨v t, Submodule.subset_span ⟨t, rfl⟩, rfl⟩
    simpa only [hzero, Submodule.mem_bot] using hm
  have hc : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := by
    apply h
    intro t
    have ht := LinearMap.pi_apply_eq_sum_univ f (v t)
    simpa only [hv, smul_eq_mul, mul_comm] using ht.symm
  apply hf
  apply LinearMap.ext
  intro x
  simpa only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]
    using LinearMap.pi_apply_eq_sum_univ f x

theorem normCurve_span_eq_top (K : Type*) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3) :
    Submodule.span K (Set.range (normCurve (K := K) q)) = ⊤ := by
  exact span_eq_top_of_coefficients_zero _ (coefficients_zero K q hq hcard)

theorem exponent_succ_pos (q : ℕ) (hq : 2 ≤ q) (i : Fin 7) :
    0 < exponent q i.succ := by
  have hq2 : 0 < q^2 := pow_pos (by omega) _
  fin_cases i <;> norm_num [exponent] <;> omega

theorem normCurve_zero_succ (K : Type*) [Field K]
    (q : ℕ) (hq : 2 ≤ q) (i : Fin 7) : normCurve q (0 : K) i.succ = 0 := by
  exact zero_pow (Nat.ne_zero_of_lt (exponent_succ_pos q hq i))

def augmentationCurve {K : Type*} [Field K] (q : ℕ) (t : K) : Fin 7 → K :=
  fun i => normCurve q t i.succ - normCurve q 0 i.succ

theorem augmentation_coefficients_zero (K : Type*) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3)
    (c : Fin 7 → K)
    (h : ∀ t, ∑ i, c i * augmentationCurve q t i = 0) : ∀ i, c i = 0 := by
  have hc := coefficients_zero K q hq hcard (Fin.cases 0 c) (by
    intro t
    simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, zero_mul,
      zero_add, augmentationCurve, normCurve_zero_succ K q hq, sub_zero] using h t)
  intro i
  exact hc i.succ

theorem augmentationCurve_span_eq_top (K : Type*) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3) :
    Submodule.span K (Set.range (augmentationCurve (K := K) q)) = ⊤ := by
  exact span_eq_top_of_coefficients_zero _ (augmentation_coefficients_zero K q hq hcard)

end SymmetricSubgroupAsymptotics.CFSGCubicNormCurveSpan
