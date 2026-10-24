import SymmetricSubgroupAsymptotics.FourPointSharedSmallBinaryTopCeiling

/-! The remaining two lower dimensions of the tiny binary family.
Two universal integer power brackets and eight scalar square checks
pay the literal one-dimensional and three-dimensional coefficient bounds. These are
arithmetic parameters of one recurrence, not action representatives. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyBinaryLowerCeilingCertificates
open IntegerLogSquareRootCeilingCertificate
open FourPointSharedSmallBinaryTopCeiling (topCut)

def headCut (d a : ℕ) : ℕ := if d = 1 then 2^a else 6*2^a+6

private theorem lower_power (a : ℕ) : 2^(101+64*a) ≤ (3*2^a)^64 := by
  have hbase : 2^101 ≤ (3 : ℕ)^64 := by decide +kernel
  have hp : (2^a : ℕ)^64 = 2^(64*a) := by rw [← pow_mul,Nat.mul_comm a 64]
  rw [mul_pow,hp,pow_add]
  exact Nat.mul_le_mul_right _ hbase

private theorem upper_power (a d : ℕ) : (3*2^(a+d))^64 ≤ 2^(103+64*(a+d)) := by
  have hbase : (3 : ℕ)^64 ≤ 2^103 := by decide +kernel
  have hp : (2^(a+d) : ℕ)^64 = 2^(64*(a+d)) := by rw [← pow_mul,Nat.mul_comm (a+d) 64]
  rw [mul_pow,hp,pow_add]
  exact Nat.mul_le_mul_right _ hbase

private theorem top_square (a : ℕ) (ha2 : 2 ≤ a) (ha5 : a ≤ 5) :
    64*(3*2^a)^2 ≤ (101+64*a)*(topCut a)^2 := by
  interval_cases a <;> decide +kernel

private theorem target_square (d a : ℕ) (hd : d = 1 ∨ d = 3)
    (ha2 : 2 ≤ a) (ha5 : a ≤ 5) :
    (headCut d a+topCut a-1)^2*(103+64*(a+d)) < 64*(3*2^(a+d))^2 := by
  rcases hd with rfl | rfl <;> interval_cases a <;> decide +kernel

theorem aggregate_small (d a g : ℕ) (hd : d = 1 ∨ d = 3)
    (ha2 : 2 ≤ a) (ha5 : a ≤ 5)
    (hcost : g ≤ headCut d a+traceyPermutationGeneratorCeiling (3*2^a)) :
    g ≤ traceyPermutationGeneratorCeiling (3*2^(a+d)) := by
  have htop : traceyPermutationGeneratorCeiling (3*2^a) ≤ topCut a :=
    ceil_le_of_square (3*2^a) 64 (101+64*a) (topCut a)
      (by positivity) (by decide) (by omega) (lower_power a) (top_square a ha2 ha5)
  have htarget : headCut d a+topCut a ≤ traceyPermutationGeneratorCeiling (3*2^(a+d)) :=
    le_ceil_of_square (3*2^(a+d)) 64 (103+64*(a+d)) (headCut d a+topCut a)
      (by
        have hh : 0 < 2^(a+d) := by positivity
        omega) (by decide)
      (by
        have hp : 0 < 2^a := by positivity
        unfold headCut
        split_ifs <;> omega) (upper_power a d) (target_square d a hd ha2 ha5)
  exact (hcost.trans (Nat.add_le_add_left htop _)).trans htarget

end SymmetricSubgroupAsymptotics.TinyBinaryLowerCeilingCertificates
