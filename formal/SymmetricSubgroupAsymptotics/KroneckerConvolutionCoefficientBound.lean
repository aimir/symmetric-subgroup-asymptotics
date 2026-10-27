import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.SplitIfs

/-! All convolution coefficients, not just the target coefficient, have
at most n products of digits below p. This is the no-carry margin needed
for Kronecker substitution. No coefficient bound is assumed separately. -/
set_option autoImplicit false
open scoped BigOperators Polynomial
namespace SymmetricSubgroupAsymptotics.KroneckerConvolutionCoefficientBound

private theorem monomial_mul_coeff (Q : ℕ[X]) (i a k : ℕ) :
    (Polynomial.monomial i a * Q).coeff k=
      if i≤k then a*Q.coeff (k-i) else 0 := by
  rw [←Polynomial.C_mul_X_pow_eq_monomial,mul_assoc,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp

theorem ofFn_coeff_le {n p : ℕ} (c : Fin n → ℕ) (hc : ∀ i, c i<p) (k : ℕ) :
    (Polynomial.ofFn n c).coeff k ≤ p-1 := by
  by_cases hk : k<n
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt c hk]
    have := hc ⟨k,hk⟩
    omega
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge c (by omega)]
    exact Nat.zero_le _

theorem product_coeff_le {n p : ℕ} (r c : Fin n → ℕ)
    (hr : ∀ i, r i<p) (hc : ∀ i, c i<p) (k : ℕ) :
    (Polynomial.ofFn n r * Polynomial.ofFn n c).coeff k ≤ n*(p-1)^2 := by
  classical
  calc
    _ = ∑ i : Fin n,
        (Polynomial.monomial i.val (r i) * Polynomial.ofFn n c).coeff k := by
      rw [Polynomial.ofFn_eq_sum_monomial,Finset.sum_mul,Polynomial.finsetSum_coeff]
    _ ≤ ∑ _i : Fin n, (p-1)^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [monomial_mul_coeff]
      split_ifs
      · have hri : r i≤p-1 := by have := hr i; omega
        have hci := ofFn_coeff_le c hc (k-i.val)
        simpa only [pow_two] using Nat.mul_le_mul hri hci
      · exact Nat.zero_le _
    _ = n*(p-1)^2 := by simp

/-- The middle convolution coefficient is the ordinary dot product. -/
theorem middle_coeff_eq_dot {n : ℕ} (hn : 0<n) (r c : Fin n → ℕ) :
    (Polynomial.ofFn n r * Polynomial.ofFn n (fun i => c i.rev)).coeff (n-1)=
      ∑ i : Fin n, r i*c i := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial,Finset.sum_mul,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  have hk : n-1=i.rev.val+i.val := by
    have hi := i.isLt
    rw [Fin.val_rev]
    omega
  rw [hk,Polynomial.coeff_monomial_mul,
    Polynomial.ofFn_coeff_eq_val_of_lt (fun j : Fin n => c j.rev) i.rev.isLt]
  simp only [Fin.eta,Fin.rev_rev]

end SymmetricSubgroupAsymptotics.KroneckerConvolutionCoefficientBound
