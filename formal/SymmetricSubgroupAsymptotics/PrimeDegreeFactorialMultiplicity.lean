import Mathlib.Data.Nat.Prime.Factorial

/-! A prime occurs only once in the factorials of its own degree and
the next degree. No finite group order or catalogue input is involved. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PrimeDegreeFactorialMultiplicity

theorem prime_square_not_dvd_succ_factorial (p : ℕ) (hp : Nat.Prime p) :
    ¬p^2 ∣ (p+1).factorial := by
  have hnext : ¬p ∣ p+1 := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm : (p+1)%p = 1 := by
      simp [Nat.add_mod,Nat.mod_eq_of_lt hp.one_lt]
    omega
  have hprev : ¬p ∣ (p-1).factorial := by
    intro hd
    have hh := hp.dvd_factorial.mp hd
    have := hp.pos
    omega
  intro hd
  rw [Nat.factorial_succ,←Nat.mul_factorial_pred hp.ne_zero,pow_two] at hd
  have he : (p+1)*(p*(p-1).factorial) = p*((p+1)*(p-1).factorial) := by ac_rfl
  rw [he] at hd
  have hh : p ∣ (p+1)*(p-1).factorial := (Nat.mul_dvd_mul_iff_left hp.pos).mp hd
  exact (hp.dvd_mul.mp hh).elim hnext hprev

theorem prime_square_not_dvd_factorial (p : ℕ) (hp : Nat.Prime p) :
    ¬p^2 ∣ p.factorial := by
  intro hd
  exact prime_square_not_dvd_succ_factorial p hp
    (hd.trans (Nat.factorial_dvd_factorial (by omega : p ≤ p+1)))

theorem prime_square_not_dvd_degree_factorial (p n : ℕ) (hp : Nat.Prime p)
    (hn : n=p ∨ n=p+1) : ¬p^2 ∣ n.factorial := by
  rcases hn with h | h
  · subst n
    exact prime_square_not_dvd_factorial p hp
  · subst n
    exact prime_square_not_dvd_succ_factorial p hp

end SymmetricSubgroupAsymptotics.PrimeDegreeFactorialMultiplicity
