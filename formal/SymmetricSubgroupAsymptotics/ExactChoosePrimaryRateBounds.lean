import SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity

/-! Numerical comparisons for the genuine arbitrary-divisor choose
rate. The retained plus-two Wallis denominator is useful in short
primary ranges; the square-root comparison preserves older consumers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds

theorem normalized_le_sqrt_plus_two (n : ℕ) :
    (n.choose (n/2) : ℝ)/(2 : ℝ)^n ≤ Real.sqrt (2/(3*(n : ℝ)+2)) := by
  have hh := CentralBinomialSquareRootBound.normalized_square n
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3*(n : ℝ)+2)).mpr
  nlinarith only [hh]

theorem primaryRate_le_sqrt (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    ActualWreathChooseDivisorCapacity.primaryRate q e ≤
      Real.sqrt (2/(3*((q : ℝ)-1)*e)) := by
  have hqm : 1 ≤ q-1 := by omega
  have hK : 1 ≤ e*(q-1) := by nlinarith only [he,hqm]
  have hh := CentralBinomialSquareRootBound.normalized_le_sqrt (e*(q-1)) hK
  have heq : (3 : ℝ)*((e*(q-1) : ℕ) : ℝ) = 3*((q : ℝ)-1)*e := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one]
    ring
  simpa only [ActualWreathChooseDivisorCapacity.primaryRate,heq] using hh

end SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds
