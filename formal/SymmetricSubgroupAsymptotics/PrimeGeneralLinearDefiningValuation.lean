import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! The defining-prime valuation of the ACTUAL finite GL order.
Every factor p^d-p^i has valuation exactly i; the sum is d(d-1)/2.
This is integer factorization, with no linear-group recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PrimeGeneralLinearDefiningValuation

theorem power_sub_power_factorization (p d i : ℕ) (hp : p.Prime) (hi : i < d) :
    (p ^ d - p ^ i).factorization p = i := by
  have hk : d - i ≠ 0 := by omega
  have hpow : 1 < p ^ (d - i) := Nat.one_lt_pow hk hp.one_lt
  have hn : p ^ (d - i) - 1 ≠ 0 := by omega
  have hnot : ¬ p ∣ p ^ (d - i) - 1 := by
    intro hd
    have hh := Nat.dvd_sub (dvd_pow_self p hk) hd
    have hdiff : p ^ (d - i) - (p ^ (d - i) - 1) = 1 := by omega
    rw [hdiff] at hh
    exact hp.ne_one (Nat.dvd_one.mp hh)
  have hmul : p ^ d - p ^ i = p ^ i * (p ^ (d - i) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, show i + (d - i) = d by omega]
  rw [hmul, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hn]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]

theorem GL_order_defining_factorization (p d : ℕ) (hp : p.Prime) :
    (∏ i : Fin d, (p ^ d - p ^ (i : ℕ))).factorization p = d * (d - 1) / 2 := by
  calc
    _ = ∑ i : Fin d, (p ^ d - p ^ (i : ℕ)).factorization p :=
      Nat.factorization_prod_apply (fun i _ =>
        Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hp.one_lt i.isLt))
    _ = ∑ i : Fin d, (i : ℕ) := Finset.sum_congr rfl (fun i _ =>
      power_sub_power_factorization p d i hp i.isLt)
    _ = d * (d - 1) / 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem matrix_GL_defining_factorization (p d : ℕ) (hp : p.Prime) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod p))).factorization p =
      d * (d - 1) / 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod p)) =
      ∏ i : Fin d, (p ^ d - p ^ (i : ℕ)) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_zmod] using
      (Matrix.card_GL_field (𝔽 := ZMod p) d)
  rw [hc]
  exact GL_order_defining_factorization p d hp

end SymmetricSubgroupAsymptotics.PrimeGeneralLinearDefiningValuation
