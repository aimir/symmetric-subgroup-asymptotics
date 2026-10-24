import SymmetricSubgroupAsymptotics.ActualWreathBoundedOrderDivisorCost
import SymmetricSubgroupAsymptotics.NaturalSquareRootQuotientCeiling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import Mathlib.NumberTheory.Divisors

/-! A single finite scalar domain: all nontrivial divisors of lcm(1,...,7).
The selected prime divisor is allowed to vary, but the actual chief cost
will stay fixed. Certificates use only exact natural arithmetic and
integer logarithm brackets at denominator64; no actions are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallAffineJointTinyCertificates
open ActualWreathBoundedOrderDivisorCost

def topDegrees : Finset ℕ :=
  {2,3,4,5,6,7,10,12,14,15,20,21,28,30,35,42,60,70,84,105,140,210,420}

def lowerLog (t : ℕ) : ℕ := Nat.log2 (t^64)
def upperLog (r t : ℕ) : ℕ := Nat.log2 ((r*t)^64)+1

def topCut (t : ℕ) : ℕ :=
  NaturalSquareRootQuotientCeiling.quotientCeiling (8*t) (lowerLog t)

def Certificate (r N t q : ℕ) : Prop :=
  q.Prime ∧ q^(t.factorization q) ∣ t ∧
    1 ≤ integerCut t N q (t.factorization q)+topCut t ∧
    (r*t)^64 ≤ 2^(upperLog r t) ∧
    (integerCut t N q (t.factorization q)+topCut t-1)^2*upperLog r t < 64*(r*t)^2

theorem mem_topDegrees (t : ℕ) (ht : 2 ≤ t) (hdiv : t ∣ 420) : t ∈ topDegrees := by
  have heq : (Nat.divisors 420).erase 1 = topDegrees := by decide +kernel
  rw [←heq]
  exact Finset.mem_erase.mpr ⟨by omega,Nat.mem_divisors.mpr ⟨hdiv,by decide⟩⟩

private theorem top_certificates : ∀ t ∈ topDegrees,
    2 ≤ t ∧ 0 < lowerLog t ∧ 2^(lowerLog t) ≤ t^64 ∧
      64*t^2 ≤ lowerLog t*(topCut t)^2 := by
  decide +kernel

theorem top_ceiling_le (t : ℕ) (ht : t ∈ topDegrees) :
    ⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ ≤ topCut t := by
  obtain ⟨ht2,hb,hpow,hsquare⟩ := top_certificates t ht
  exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square t 64 (lowerLog t) (topCut t)
    (by omega) (by decide) hb hpow hsquare

/-- Selected first order pilot, over every possible small-primary top degree. -/
theorem five_certificates : ∀ t ∈ topDegrees, ∃ q : Fin 8, Certificate 5 20 t q := by
  unfold Certificate
  decide +kernel

theorem cuts_le_target (r N t q : ℕ) (hr : 1 ≤ r) (ht : t ∈ topDegrees)
    (h : Certificate r N t q) :
    integerCut t N q (t.factorization q)+topCut t ≤
      ⌈((r*t : ℕ) : ℝ)/Real.sqrt (Real.logb 2 ((r*t : ℕ) : ℝ))⌉₊ := by
  obtain ⟨_,_,hK,hpow,hsquare⟩ := h
  have ht2 := (top_certificates t ht).1
  have hrt : 2 ≤ r*t := by
    have hh := Nat.mul_le_mul hr ht2
    simpa only [one_mul] using hh
  exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square (r*t) 64
    (upperLog r t) (integerCut t N q (t.factorization q)+topCut t)
    hrt (by decide) hK hpow hsquare

end SymmetricSubgroupAsymptotics.SmallAffineJointTinyCertificates
