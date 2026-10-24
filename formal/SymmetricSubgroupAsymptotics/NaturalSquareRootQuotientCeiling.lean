import SymmetricSubgroupAsymptotics.IntegerSquareRootQuotientCeiling
import Mathlib.Data.Nat.Sqrt

/-! A computable exact natural ceiling for n/sqrt(k). Its correctness
is proved from integer square intervals, so selected finite scalar
certificates need no floating-point approximation or real evaluation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalSquareRootQuotientCeiling

def quotientCeiling (n k : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.sqrt ((n^2-1)/k)+1

theorem quotientCeiling_eq (n k : ℕ) (hk : 0 < k) :
    quotientCeiling n k = ⌈(n : ℝ)/Real.sqrt k⌉₊ := by
  by_cases hn : n = 0
  · simp only [quotientCeiling, hn, if_true, Nat.cast_zero, zero_div, Nat.ceil_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hn2 : 0 < n^2 := pow_pos hnpos _
    let z := (n^2-1)/k
    have hlo : ((Nat.sqrt z+1)-1)^2*k < n^2 := by
      rw [Nat.add_sub_cancel]
      have hh : (Nat.sqrt z)^2*k ≤ n^2-1 :=
        (Nat.le_div_iff_mul_le hk).mp (Nat.sqrt_le' z)
      exact hh.trans_lt (Nat.sub_lt hn2 (by decide : 0 < (1 : ℕ)))
    have hi : n^2 ≤ (Nat.sqrt z+1)^2*k := by
      have hh : (n^2-1)/k < (Nat.sqrt z+1)^2 := by
        simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' z
      have hm := (Nat.div_lt_iff_lt_mul hk).mp hh
      omega
    rw [quotientCeiling, if_neg hn]
    exact (IntegerSquareRootQuotientCeiling.ceil_eq_of_square_interval
      n k (Nat.sqrt z+1) hk (by omega) hlo hi).symm

end SymmetricSubgroupAsymptotics.NaturalSquareRootQuotientCeiling
