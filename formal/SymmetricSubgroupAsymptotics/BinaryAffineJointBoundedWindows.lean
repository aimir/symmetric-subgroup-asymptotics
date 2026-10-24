import SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics
import Mathlib.Tactic.IntervalCases

/-! Exact bounded scalar residuals for the joint binary affine charge.
This is a finite integer calculation after two selected pilots and a
universal proof of the ceiling conversion. Each dimension is checked in
a separate kernel reduction. No group catalogue, permutation input,
floating-point computation, or completion of the unpaid cases is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineJointBoundedWindows
open BinaryAffineJointSelectedWindowNumerics NaturalSquareRootQuotientCeiling

def unpaid (d e : ℕ) : Bool :=
  ((d == 2 || d == 3 || d == 4) && (e == 1 || e == 2)) || (d == 5 && e == 1)

private theorem dimension_one : ∀ e : Fin 20, 1 ≤ (e : ℕ) →
    (unpaid 1 e = true ↔ quotientCeiling (2^(1+(e : ℕ))) (1+e) < jointCost 1 e) := by
  decide +kernel

private theorem dimension_two : ∀ e : Fin 24, 1 ≤ (e : ℕ) →
    (unpaid 2 e = true ↔ quotientCeiling (2^(2+(e : ℕ))) (2+e) < jointCost 2 e) := by
  decide +kernel

private theorem dimension_three : ∀ e : Fin 36, 1 ≤ (e : ℕ) →
    (unpaid 3 e = true ↔ quotientCeiling (2^(3+(e : ℕ))) (3+e) < jointCost 3 e) := by
  decide +kernel

private theorem dimension_four : ∀ e : Fin 48, 1 ≤ (e : ℕ) →
    (unpaid 4 e = true ↔ quotientCeiling (2^(4+(e : ℕ))) (4+e) < jointCost 4 e) := by
  decide +kernel

private theorem dimension_five : ∀ e : Fin 60, 1 ≤ (e : ℕ) →
    (unpaid 5 e = true ↔ quotientCeiling (2^(5+(e : ℕ))) (5+e) < jointCost 5 e) := by
  decide +kernel

private theorem dimension_six : ∀ e : Fin 72, 1 ≤ (e : ℕ) →
    (unpaid 6 e = true ↔ quotientCeiling (2^(6+(e : ℕ))) (6+e) < jointCost 6 e) := by
  decide +kernel

private theorem dimension_seven : ∀ e : Fin 84, 1 ≤ (e : ℕ) →
    (unpaid 7 e = true ↔ quotientCeiling (2^(7+(e : ℕ))) (7+e) < jointCost 7 e) := by
  decide +kernel

private theorem dimension_eight : ∀ e : Fin 96, 1 ≤ (e : ℕ) →
    (unpaid 8 e = true ↔ quotientCeiling (2^(8+(e : ℕ))) (8+e) < jointCost 8 e) := by
  decide +kernel

private theorem dimension_nine : ∀ e : Fin 108, 1 ≤ (e : ℕ) →
    (unpaid 9 e = true ↔ quotientCeiling (2^(9+(e : ℕ))) (9+e) < jointCost 9 e) := by
  decide +kernel

/-- The exact seven remaining numerical failures of this particular
joint estimate. This says nothing about the actual group rank there. -/
theorem bounded_window_exact (d e : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (he1 : 1 ≤ e) (hew : e < max 20 (12*d)) :
    unpaid d e = true ↔ quotientCeiling (2^(d+e)) (d+e) < jointCost d e := by
  interval_cases d <;> norm_num at hew
  · exact dimension_one ⟨e, hew⟩ he1
  · exact dimension_two ⟨e, hew⟩ he1
  · exact dimension_three ⟨e, hew⟩ he1
  · exact dimension_four ⟨e, hew⟩ he1
  · exact dimension_five ⟨e, hew⟩ he1
  · exact dimension_six ⟨e, hew⟩ he1
  · exact dimension_seven ⟨e, hew⟩ he1
  · exact dimension_eight ⟨e, hew⟩ he1
  · exact dimension_nine ⟨e, hew⟩ he1

theorem bounded_window_le (d e : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (he1 : 1 ≤ e) (hew : e < max 20 (12*d)) (hpaid : unpaid d e = false) :
    jointCost d e ≤ quotientCeiling (2^(d+e)) (d+e) := by
  apply Nat.le_of_not_gt
  intro hexcess
  have htrue := (bounded_window_exact d e hd1 hd9 he1 hew).mpr hexcess
  cases hpaid.symm.trans htrue

end SymmetricSubgroupAsymptotics.BinaryAffineJointBoundedWindows
