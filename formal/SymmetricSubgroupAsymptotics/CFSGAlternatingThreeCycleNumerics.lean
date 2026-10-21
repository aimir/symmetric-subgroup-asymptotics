import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The centralizer factor for a product of k disjoint three-cycles is
strictly smaller than that for one three-cycle, except for degree6,k=2.
These are uniform factorial inequalities, not a finite-degree table. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleNumerics

private theorem triple_factor_lt (k : ℕ) (hk : 3≤k) :
    3^k*k.factorial<3*(3*k-3).factorial := by
  induction k,hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    let a := 3*k-3
    have hsmall : 3≤(a+3)*(a+2) := by
      calc
        3 ≤ (a+3)*1 := by omega
        _ ≤ (a+3)*(a+2) := Nat.mul_le_mul_left _ (by omega)
    have hstep : 3*(k+1)≤(a+3)*(a+2)*(a+1) :=
      Nat.mul_le_mul hsmall (by dsimp [a];omega)
    have hright : 3*(k+1)-3=a+3 := by dsimp [a];omega
    rw [hright]
    calc
      3^(k+1)*(k+1).factorial=(3^k*k.factorial)*(3*(k+1)) := by
        rw [pow_succ,Nat.factorial_succ]
        ring
      _ < (3*a.factorial)*(3*(k+1)) :=
        Nat.mul_lt_mul_of_pos_right ih (by omega)
      _ ≤ (3*a.factorial)*((a+3)*(a+2)*(a+1)) := Nat.mul_le_mul_left _ hstep
      _ = 3*(a+3).factorial := by
        rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ]
        ring

theorem many_three_cycles_factor_lt (n k : ℕ) (hk : 3≤k) (hkn : 3*k≤n) :
    3^k*k.factorial*(n-3*k).factorial<3*(n-3).factorial := by
  have he : 3*k-3+(n-3*k)=n-3 := by omega
  have hf : (3*k-3).factorial*(n-3*k).factorial≤(3*k-3+(n-3*k)).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  calc
    3^k*k.factorial*(n-3*k).factorial <
        (3*(3*k-3).factorial)*(n-3*k).factorial :=
      Nat.mul_lt_mul_of_pos_right (triple_factor_lt k hk) (Nat.factorial_pos _)
    _ = 3*((3*k-3).factorial*(n-3*k).factorial) := by ring
    _ ≤ 3*(3*k-3+(n-3*k)).factorial := Nat.mul_le_mul_left _ hf
    _ = 3*(n-3).factorial := by rw [he]

theorem two_three_cycles_factor_lt (n : ℕ) (hn : 7≤n) :
    3^2*Nat.factorial 2*(n-3*2).factorial<3*(n-3).factorial := by
  let a := n-6
  have ha : 1≤a := by dsimp [a];omega
  have he : n-3=a+3 := by dsimp [a];omega
  have hprod : 24≤(a+3)*(a+2)*(a+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega : 4≤a+3) (by omega : 3≤a+2))
      (by omega : 2≤a+1)
  change 18*a.factorial<3*(n-3).factorial
  rw [he]
  calc
    18*a.factorial < (3*((a+3)*(a+2)*(a+1)))*a.factorial :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos _)
    _ = 3*(a+3).factorial := by
      rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ]
      ring

/-- Equality with the one-three-cycle centralizer factor uniquely
recognizes k=1 outside the exceptional degree6. -/
theorem equality_forces_single (n k : ℕ) (hn : 5≤n) (hk : 1≤k) (hkn : 3*k≤n)
    (hne : n≠6)
    (he : 3^k*k.factorial*(n-3*k).factorial=3*(n-3).factorial) : k=1 := by
  by_contra hbad
  have htwo : 2≤k := by omega
  by_cases hk2 : k=2
  · have hn7 : 7≤n := by omega
    have hh := two_three_cycles_factor_lt n hn7
    rw [hk2] at he
    omega
  · have hh := many_three_cycles_factor_lt n k (by omega) hkn
    omega

end SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleNumerics
