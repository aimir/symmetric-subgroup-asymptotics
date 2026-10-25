import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The actual higher-Siegel numerator is (q-1) times the point-index
quantity. This arithmetic comparison retains the supplied SAME index;
it neither enlarges a group nor changes an additive kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SiegelPointIndexComparison

theorem point_index_le_of_siegel_numerator (q r n : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hnum : (q-1)*q^(r-2)*(q^r-q) ≤ 2*n) :
    (q^(r-1)-1)*q^(r-1) ≤ n := by
  have hpow : q*q^(r-1)=q^r := by
    rw [←pow_succ']
    exact congrArg (fun k : ℕ => q^k) (by omega)
  have hsub : q^r-q=q*(q^(r-1)-1) := by
    rw [Nat.mul_sub_left_distrib,mul_one,hpow]
  have hstep : q^(r-2)*q=q^(r-1) := by
    rw [←pow_succ]
    exact congrArg (fun k : ℕ => q^k) (by omega)
  have he : (q-1)*q^(r-2)*(q^r-q)=(q-1)*((q^(r-1)-1)*q^(r-1)) := by
    rw [hsub]
    calc
      _ = (q-1)*(q^(r-1)-1)*(q^(r-2)*q) := by ring
      _ = (q-1)*((q^(r-1)-1)*q^(r-1)) := by rw [hstep]; ring
  have hh : 2*((q^(r-1)-1)*q^(r-1)) ≤ 2*n :=
    ((Nat.mul_le_mul_right _ (by omega : 2 ≤ q-1)).trans_eq he.symm).trans hnum
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (2:ℕ))

end SymmetricSubgroupAsymptotics.SiegelPointIndexComparison
