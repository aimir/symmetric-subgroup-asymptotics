import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! The exact occurrence-factorial cost of merging q selected pairs with
p original pairs is a rising factorial. Even if q! from an arbitrary
presentation is retained, q! choose(M,q) is bounded by M^q. This is the
same coarse pair-selection bound, with no physical quotient assertion.
-/

set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.MarkerPairFactorial

theorem ratio_eq_rising (p q : ℕ) :
    ((p+q).factorial : ℚ)/(p.factorial : ℚ)=((p+1).ascFactorial q : ℚ) := by
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))).mpr
  have h := congrArg (fun n : ℕ => (n:ℚ)) (Nat.factorial_mul_ascFactorial p q)
  simpa only [Nat.cast_mul,mul_comm] using h.symm

/-- The unchanged original occurrence factorial is the denominator. -/
theorem ratio_le_pow (p q M : ℕ) (hM : p+q≤M) :
    ((p+q).factorial : ℚ)/(p.factorial : ℚ)≤(M:ℚ)^q := by
  rw [ratio_eq_rising]
  exact_mod_cast (Nat.ascFactorial_le_pow_add p q).trans
    (Nat.pow_le_pow_left hM q)

/-- Retaining the presentation factorial still costs no more than the
standard power bound for choosing actual pairs. This includes q>M. -/
theorem factorial_choose_le_pow (M q : ℕ) :
    (q.factorial : ℚ)*(M.choose q : ℚ)≤(M:ℚ)^q := by
  have h : q.factorial*M.choose q≤M^q := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow M q
  exact_mod_cast h

theorem ratio_le_rank_pow (p q M N : ℕ) (hM : p+q≤M) (hN : M≤N) :
    ((p+q).factorial : ℚ)/(p.factorial : ℚ)≤(N:ℚ)^q :=
  ratio_le_pow p q N (hM.trans hN)

/-- At zero excess and either physical parity, the allocation can have
at most one selected label, so its presentation factorial is exactly one. -/
theorem factorial_eq_one_of_zero_excess (q g f ε : ℕ)
    (hε : ε≤1) (hgf : g+f=ε) (hq : q≤g) : q.factorial=1 := by
  have hq1 : q≤1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq1 with h | h <;> simp [h]

end SymmetricSubgroupAsymptotics.MarkerPairFactorial
