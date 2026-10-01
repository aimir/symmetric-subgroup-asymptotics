import SymmetricSubgroupAsymptotics.MarkedC4BoundedWordRecurrence

/-!
# Assembling the bounded-word recurrence from the two RDT cases

The structural part of the RDT bounded-word argument partitions the count
into a nonexcessive Case-I total and Case-II peel totals.  The marked work is
the pair of estimates below: Case I uses the retained two-column Hall splice,
and every peel uses exactly the reserve `F(b,r)-F(k,r)`.

This file performs the division by `2^F` once and constructs the normalized
recurrence consumed by `MarkedC4BoundedWordRecurrence`.  Thus a later
literature interface need retain only the literal RDT partition and its
polynomial menu multiplicity; it does not assume a marked moment theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The exponential main term in the marked bound. -/
def markedBase (b r : ℕ) : ℝ :=
  (2 : ℝ) ^ markedF b r

theorem markedBase_pos (b r : ℕ) : 0 < markedBase b r := by
  unfold markedBase
  positivity

/-- Exact data left after the local Case-I and Case-II estimates have been
inserted into the RDT normal-intersection partition.  `peel b k r` is the
total of rows whose selected physical peel leaves degree `k < b`.

The factor `((b : ℝ) + r + 2)^A` includes only the bounded normal-menu,
tableau-ordering and fixed-coordinate constants. -/
structure BoundedWordCaseDecomposition (count : ℕ → ℕ → ℝ) where
  A : ℝ
  A_nonneg : 0 ≤ A
  count_nonneg : ∀ b r, 0 ≤ count b r
  caseI : ℕ → ℕ → ℝ
  peel : ℕ → ℕ → ℕ → ℝ
  caseI_nonneg : ∀ b r, 0 ≤ caseI b r
  peel_nonneg : ∀ b k r, 0 ≤ peel b k r
  zero : ∀ r, count 0 r ≤ markedBase 0 r
  partition : ∀ b r, 0 < b →
    count b r ≤ caseI b r + ∑ k ∈ Finset.range b, peel b k r
  caseI_bound : ∀ b r,
    caseI b r ≤ markedBase b r * (((b : ℝ) + r + 2) ^ A)
  peel_bound : ∀ b k r, k < b →
    peel b k r ≤ markedBase b r * (((b : ℝ) + r + 2) ^ A) *
      (count k r / markedBase k r)

namespace BoundedWordCaseDecomposition

variable {count : ℕ → ℕ → ℝ}
  (D : BoundedWordCaseDecomposition count)

/-- Normalized marked count attached to a structural Case-I/Case-II
decomposition. -/
def normalized (_D : BoundedWordCaseDecomposition count) (b r : ℕ) : ℝ :=
  count b r / markedBase b r

theorem normalized_nonneg (b r : ℕ) : 0 ≤ D.normalized b r := by
  exact div_nonneg (D.count_nonneg b r) (markedBase_pos b r).le

/-- The two local marked estimates and the literal RDT partition imply the
single normalized peel recurrence. -/
theorem normalized_recurrence (b r : ℕ) (hb : 0 < b) :
    D.normalized b r ≤ (((b : ℝ) + r + 2) ^ D.A) *
      (1 + ∑ k ∈ Finset.range b, D.normalized k r) := by
  let P : ℝ := ((b : ℝ) + r + 2) ^ D.A
  have hP : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hpeel :
      (∑ k ∈ Finset.range b, D.peel b k r) ≤
        ∑ k ∈ Finset.range b,
          markedBase b r * P * D.normalized k r := by
    apply Finset.sum_le_sum
    intro k hk
    have hkb : k < b := Finset.mem_range.mp hk
    simpa only [P, normalized] using D.peel_bound b k r hkb
  have htotal :
      count b r ≤ markedBase b r * P *
        (1 + ∑ k ∈ Finset.range b, D.normalized k r) := by
    calc
      count b r ≤ D.caseI b r +
          ∑ k ∈ Finset.range b, D.peel b k r := D.partition b r hb
      _ ≤ markedBase b r * P +
          ∑ k ∈ Finset.range b,
            markedBase b r * P * D.normalized k r :=
        add_le_add (by simpa only [P] using D.caseI_bound b r) hpeel
      _ = markedBase b r * P *
          (1 + ∑ k ∈ Finset.range b, D.normalized k r) := by
        rw [← Finset.mul_sum]
        ring
  rw [normalized, div_le_iff₀ (markedBase_pos b r)]
  simpa only [P, mul_assoc, mul_comm, mul_left_comm] using htotal

/-- Construct the normalized recurrence expected by the numerical endpoint.
No marked asymptotic estimate is present in this input. -/
noncomputable def toNormalizedRecurrence :
    BoundedWordNormalizedRecurrence count where
  A := D.A
  A_nonneg := D.A_nonneg
  normalized := D.normalized
  zero := by
    intro r
    rw [normalized, div_le_iff₀ (markedBase_pos 0 r)]
    simpa using D.zero r
  recurrence := D.normalized_recurrence
  denormalize := by
    intro b r
    change count b r ≤ markedBase b r *
      (count b r / markedBase b r)
    rw [mul_div_cancel₀ _ (markedBase_pos b r).ne']

/-- Explicit bounded-word estimate obtained from the literal two-case
decomposition. -/
theorem count_le_explicit (b r : ℕ) :
    count b r ≤
      (2 : ℝ) ^
        (markedF b r +
          ((D.A + 1) / Real.log 2) * b *
            Real.log ((b : ℝ) + r + 2)) :=
  D.toNormalizedRecurrence.count_le_explicit b r

end BoundedWordCaseDecomposition

end MarkedC4
end SymmetricSubgroupAsymptotics

end
