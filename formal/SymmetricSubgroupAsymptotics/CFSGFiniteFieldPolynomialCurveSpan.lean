import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Lean.Elab.Tactic.Omega

/-! Actual monomial evaluation vectors of length n span K^n when the
field has at least n elements. Polynomial root counting gives the result
without a selected inverse matrix or division by a small integer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Polynomial

namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldPolynomialCurveSpan

def monomialCurve (K : Type*) [Monoid K] (n : ℕ) (t : K) : Fin n → K := fun i => t^i.val

theorem coefficients_zero (K : Type*) [Field K] [Finite K] (n : ℕ)
    (hn : 0 < n) (hcard : n ≤ Nat.card K) (c : Fin n → K)
    (h : ∀ t : K, ∑ i, c i*monomialCurve K n t i = 0) : ∀ i, c i = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite _
  let P : K[X] := ∑ i : Fin n, Polynomial.monomial i.val (c i)
  have hdeg : P.natDegree ≤ n-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le (c i)).trans (by have := i.isLt; omega)
  have hev (t : K) : P.eval t = 0 := by
    simpa only [P,Polynomial.eval_finsetSum,Polynomial.eval_monomial,monomialCurve] using h t
  have hz : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P Function.injective_id hev (by
    have hlt : n-1 < Nat.card K := by omega
    simpa only [Nat.card_eq_fintype_card] using hdeg.trans_lt hlt)
  intro i
  have hc := congrArg (fun R : K[X] => R.coeff i.val) hz
  simpa [P,Polynomial.coeff_monomial,Fin.val_inj] using hc

theorem monomialCurve_span_eq_top (K : Type*) [Field K] [Finite K] (n : ℕ)
    (hn : 0 < n) (hcard : n ≤ Nat.card K) :
    Submodule.span K (Set.range (monomialCurve K n)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f,hf,hzero⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hne) inferInstance
  have hv (t : K) : f (monomialCurve K n t) = 0 := by
    have hm : f (monomialCurve K n t) ∈ (Submodule.span K (Set.range (monomialCurve K n))).map f :=
      Submodule.mem_map.mpr ⟨monomialCurve K n t,Submodule.subset_span ⟨t,rfl⟩,rfl⟩
    simpa only [hzero,Submodule.mem_bot] using hm
  have hc : ∀ i : Fin n, f (fun j => if i=j then 1 else 0) = 0 := by
    apply coefficients_zero K n hn hcard
    intro t
    have ht := LinearMap.pi_apply_eq_sum_univ f (monomialCurve K n t)
    simpa only [hv,smul_eq_mul,mul_comm] using ht.symm
  apply hf
  apply LinearMap.ext
  intro x
  simpa only [hc,smul_zero,Finset.sum_const_zero,LinearMap.zero_apply] using
    LinearMap.pi_apply_eq_sum_univ f x

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldPolynomialCurveSpan
