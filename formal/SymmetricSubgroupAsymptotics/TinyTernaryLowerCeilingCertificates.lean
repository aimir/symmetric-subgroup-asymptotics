import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.Tactic.IntervalCases

/-! The actual dominant-ternary three/six-point shapes in dimensions
one through three. The dimension-two six-point case is excluded here:
it is paid by the checked actual shared-head theorem, not this coarse
single-divisor cost. Five small scalar squares remain. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyTernaryLowerCeilingCertificates

def headCut (d t : ℕ) : ℕ :=
  if d = 1 then t/3 else if d = 2 then 4 else if t = 3 then 8 else 17

private def topCut (t : ℕ) : ℕ := if t = 3 then 3 else 4
private def topUpper (t : ℕ) : ℕ := if t = 3 then 7 else 11

private theorem top_le (t : ℕ) (ht : t = 3 ∨ t = 6) :
    traceyPermutationGeneratorCeiling t ≤ topCut t := by
  rcases ht with rfl | rfl
  · exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 3 1 1 3
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 6 2 5 4
      (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem upper_power (d t : ℕ) (ht : t = 3 ∨ t = 6) :
    (2^d*t)^4 ≤ 2^(4*d+topUpper t) := by
  have hbase : t^4 ≤ 2^topUpper t := by rcases ht with rfl | rfl <;> decide +kernel
  have hp : (2^d : ℕ)^4 = 2^(4*d) := by rw [← pow_mul,Nat.mul_comm d 4]
  rw [mul_pow,hp,pow_add]
  exact Nat.mul_le_mul_left _ hbase

private theorem target_square (d t : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (ht : t = 3 ∨ t = 6) (hallowed : d ≠ 2 ∨ t ≠ 6) :
    (headCut d t+topCut t-1)^2*(4*d+topUpper t) < 4*(2^d*t)^2 := by
  rcases hd with rfl | rfl | rfl <;> rcases ht with rfl | rfl
  all_goals norm_num at hallowed
  all_goals decide +kernel

theorem aggregate_small (d t g : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (ht : t = 3 ∨ t = 6) (hallowed : d ≠ 2 ∨ t ≠ 6)
    (hcost : g ≤ headCut d t+traceyPermutationGeneratorCeiling t) :
    g ≤ traceyPermutationGeneratorCeiling (2^d*t) := by
  have htarget : headCut d t+topCut t ≤ traceyPermutationGeneratorCeiling (2^d*t) :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square (2^d*t) 4
      (4*d+topUpper t) (headCut d t+topCut t)
      (by
        have hp : 0 < 2^d := by positivity
        rcases ht with rfl | rfl <;> omega) (by decide)
      (by unfold topCut; split_ifs <;> omega) (upper_power d t ht)
      (target_square d t hd ht hallowed)
  exact (hcost.trans (Nat.add_le_add_left (top_le t ht) _)).trans htarget

end SymmetricSubgroupAsymptotics.TinyTernaryLowerCeilingCertificates
