import SymmetricSubgroupAsymptotics.OddAffineTameOrderTailNumerics

/-! Three broad dimension bands for the shared sharper ordinary margin.
Each is proved uniformly in the logarithmic window by polynomial
induction. No top degree, characteristic list or action is enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OddAffineSharpDyadicMarginNumerics

theorem dimension_one (k : ℕ) (hk : 4 ≤ k) :
    (k+4)^2*(9*k+73) ≤ 36*4^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hshift : k = (k-4)+4 := by omega
      have heq : 4*((k+4)^2*(9*k+73)) =
          ((k+1)+4)^2*(9*(k+1)+73)+(27*(k-4)^3+732*(k-4)^2+6427*(k-4)+18346) := by
        rw [hshift]
        simp only [Nat.add_sub_cancel]
        ring
      have hstep : ((k+1)+4)^2*(9*(k+1)+73) ≤
          4*((k+4)^2*(9*k+73)) := by rw [heq]; omega
      calc
        ((k+1)+4)^2*(9*(k+1)+73) ≤ 4*((k+4)^2*(9*k+73)) := hstep
        _ ≤ 4*(36*4^k) := Nat.mul_le_mul_left 4 ih
        _ = 36*4^(k+1) := by rw [pow_succ]; ring

theorem dimension_two (k : ℕ) (hk : 5 ≤ k) :
    (2*k+6)^2*(9*k+73) ≤ 36*4^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hshift : k = (k-5)+5 := by omega
      have heq : 4*((2*k+6)^2*(9*k+73)) =
          (2*(k+1)+6)^2*(9*(k+1)+73)+(108*(k-5)^3+3036*(k-5)^2+27364*(k-5)+79684) := by
        rw [hshift]
        simp only [Nat.add_sub_cancel]
        ring
      have hstep : (2*(k+1)+6)^2*(9*(k+1)+73) ≤
          4*((2*k+6)^2*(9*k+73)) := by rw [heq]; omega
      calc
        (2*(k+1)+6)^2*(9*(k+1)+73) ≤ 4*((2*k+6)^2*(9*k+73)) := hstep
        _ ≤ 4*(36*4^k) := Nat.mul_le_mul_left 4 ih
        _ = 36*4^(k+1) := by rw [pow_succ]; ring

theorem dimension_four (k : ℕ) (hk : 6 ≤ k) :
    (4*k+10)^2*(9*k+73) ≤ 36*4^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hshift : k = (k-6)+6 := by omega
      have heq : 4*((4*k+10)^2*(9*k+73)) =
          (4*(k+1)+10)^2*(9*(k+1)+73)+(432*(k-6)^3+13008*(k-6)^2+125452*(k-6)+390864) := by
        rw [hshift]
        simp only [Nat.add_sub_cancel]
        ring
      have hstep : (4*(k+1)+10)^2*(9*(k+1)+73) ≤
          4*((4*k+10)^2*(9*k+73)) := by rw [heq]; omega
      calc
        (4*(k+1)+10)^2*(9*(k+1)+73) ≤ 4*((4*k+10)^2*(9*k+73)) := hstep
        _ ≤ 4*(36*4^k) := Nat.mul_le_mul_left 4 ih
        _ = 36*4^(k+1) := by rw [pow_succ]; ring

end SymmetricSubgroupAsymptotics.OddAffineSharpDyadicMarginNumerics
