import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Five unavoidable tiny scalar top degrees. Only integer logarithmic
ceiling certificates are checked; no groups, subgroups or actions are
enumerated. Actual chief costs are bound separately in the consumer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OrderSixTinyCoarseCeilingCertificates

def bodyCut (t : ℕ) : ℕ := if t = 2 then 2 else if t = 3 then 2 else
  if t = 4 then 3 else if t = 6 then 5 else 9

def topCut (t : ℕ) : ℕ := if t = 2 then 2 else if t = 3 then 3 else
  if t = 4 then 3 else if t = 6 then 4 else 7

theorem top_ceiling_le (t : ℕ) (ht : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 6 ∨ t = 12) :
    ⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ ≤ topCut t := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · change ⌈(2 : ℝ)/Real.sqrt (Real.logb 2 (2 : ℝ))⌉₊ ≤ 2
    exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 2 64 64 2
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change ⌈(3 : ℝ)/Real.sqrt (Real.logb 2 (3 : ℝ))⌉₊ ≤ 3
    exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 3 64 101 3
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change ⌈(4 : ℝ)/Real.sqrt (Real.logb 2 (4 : ℝ))⌉₊ ≤ 3
    exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 4 64 128 3
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change ⌈(6 : ℝ)/Real.sqrt (Real.logb 2 (6 : ℝ))⌉₊ ≤ 4
    exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 6 64 165 4
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change ⌈(12 : ℝ)/Real.sqrt (Real.logb 2 (12 : ℝ))⌉₊ ≤ 7
    exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 12 64 229 7
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)

theorem cuts_le_target_ceiling (t : ℕ) (ht : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 6 ∨ t = 12) :
    bodyCut t+topCut t ≤
      ⌈((3*t : ℕ) : ℝ)/Real.sqrt (Real.logb 2 ((3*t : ℕ) : ℝ))⌉₊ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · change 4 ≤ ⌈(6 : ℝ)/Real.sqrt (Real.logb 2 (6 : ℝ))⌉₊
    exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 6 64 166 4
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change 5 ≤ ⌈(9 : ℝ)/Real.sqrt (Real.logb 2 (9 : ℝ))⌉₊
    exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 9 64 203 5
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change 6 ≤ ⌈(12 : ℝ)/Real.sqrt (Real.logb 2 (12 : ℝ))⌉₊
    exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 12 64 230 6
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change 9 ≤ ⌈(18 : ℝ)/Real.sqrt (Real.logb 2 (18 : ℝ))⌉₊
    exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 18 64 267 9
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
  · change 16 ≤ ⌈(36 : ℝ)/Real.sqrt (Real.logb 2 (36 : ℝ))⌉₊
    exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 36 64 331 16
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)

end SymmetricSubgroupAsymptotics.OrderSixTinyCoarseCeilingCertificates
