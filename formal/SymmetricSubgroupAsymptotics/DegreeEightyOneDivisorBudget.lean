import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.NormNum

/-! The exact GL(4,3) divisor budget after the primitive composition bound.
The finite check is only 10*7*2*2 exponent tuples, not 24 million integers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.DegreeEightyOneDivisorBudget

private theorem exponent_budget : ∀ (a : Fin 10) (b : Fin 7) (c d : Fin 2),
    a.val+b.val+c.val+d.val≤11 →
      2^a.val*3^b.val*5^c.val*13^d.val≤81^3 := by decide +kernel

private theorem gl_factorization : (24261120 : ℕ).factorization =
    Finsupp.single 2 9+Finsupp.single 3 6+Finsupp.single 5 1+Finsupp.single 13 1 := by
  rw [show (24261120 : ℕ)=2^9*3^6*5*13 by norm_num]
  rw [Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization_pow,Nat.prime_three.factorization_pow,
    Nat.prime_five.factorization,(by decide : Nat.Prime 13).factorization]

/-- All actual complement orders dividing GL(4,3) and using at most eleven
prime factors fit the required cube. -/
theorem order_le_cube (n : ℕ) (hdiv : n∣24261120)
    (hbudget : ArithmeticFunction.cardFactors n≤11) : n≤81^3 := by
  have hn : n≠0 := by intro h; subst n; norm_num at hdiv
  have hle := (Nat.factorization_le_iff_dvd hn (by decide : 24261120≠0)).mpr hdiv
  have hs0 : (24261120 : ℕ).factorization.support ⊆ ({2,3,5,13} : Finset ℕ) := by decide +kernel
  have hs := (Finsupp.support_mono hle).trans hs0
  have hprod : n=2^(n.factorization 2)*3^(n.factorization 3)*
      5^(n.factorization 5)*13^(n.factorization 13) := by
    calc
      n=n.factorization.prod (·^·) := (Nat.prod_factorization_pow_eq_self hn).symm
      _ = ∏ q∈({2,3,5,13} : Finset ℕ), q^(n.factorization q) :=
        Finsupp.prod_of_support_subset _ hs _ (by simp)
      _ = _ := by norm_num [mul_assoc]
  have hsum : ArithmeticFunction.cardFactors n=n.factorization 2+n.factorization 3+
      n.factorization 5+n.factorization 13 := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization,
      Finsupp.sum_of_support_subset _ hs _ (by simp)]
    norm_num [add_assoc]
  have hab : n.factorization 2<10 := by simpa [gl_factorization,Finsupp.single_apply] using Nat.lt_succ_of_le (hle 2)
  have hbb : n.factorization 3<7 := by simpa [gl_factorization,Finsupp.single_apply] using Nat.lt_succ_of_le (hle 3)
  have hcb : n.factorization 5<2 := by simpa [gl_factorization,Finsupp.single_apply] using Nat.lt_succ_of_le (hle 5)
  have hdb : n.factorization 13<2 := by simpa [gl_factorization,Finsupp.single_apply] using Nat.lt_succ_of_le (hle 13)
  calc
    n=2^(n.factorization 2)*3^(n.factorization 3)*5^(n.factorization 5)*13^(n.factorization 13) := hprod
    _ ≤ 81^3 := exponent_budget ⟨_,hab⟩ ⟨_,hbb⟩ ⟨_,hcb⟩ ⟨_,hdb⟩
      (by simpa only [Fin.val_mk] using (hsum ▸ hbudget))

end SymmetricSubgroupAsymptotics.DegreeEightyOneDivisorBudget
