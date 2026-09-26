import SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Summing the certified quadratic reserve over complete histories.
Every history keeps its original nonnegative weight and its own row/colour
assignment. No bound on the sum or independence of those assignments is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy

open BinaryCarrierCone JointCapacityRow

/-- A common exponent bound can be summed without forgetting multiplicity. -/
theorem weighted_rpow_sum_le {ι : Type*} [Fintype ι]
    (weight cost : ι → ℝ) (hw : ∀ h, 0 ≤ weight h) (base ceiling : ℝ)
    (hcost : ∀ h, base + cost h ≤ ceiling) :
    (2 : ℝ)^base * (∑ h, weight h * (2 : ℝ)^(cost h)) ≤
      (∑ h, weight h) * (2 : ℝ)^ceiling := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro h _
  calc
    _ = weight h * (2 : ℝ)^(base + cost h) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hcost h)) (hw h)

/-- The sum bound is derived from the individual capacity and pair
certificates on each history, including histories with different colours.
The common total mass is the only mass identification supplied here. -/
theorem weighted_histories_le_reserve {ι : Type*} [Fintype ι] {t : ℕ}
    (rows : ι → Fin t → JointCapacityRow) (color : ι → Fin t → Fin 6)
    (u : ι → Fin t → ℝ) (weight : ι → ℝ) (hw : ∀ h, 0 ≤ weight h)
    (hu : ∀ h i, 0 ≤ u h i)
    (hk : ∀ h i, ((rows h i).k : ℝ) ≤ u h i * alpha (color h i))
    (hb : ∀ h i, ((max (rows h i).m (rows h i).a₂ : ℕ) : ℝ) ≤
      u h i * beta (color h i))
    (hpair : ∀ h a i, a < i → symmetricSupport (rows h a) (rows h i) ≤
      u h a * u h i * pairMatrix64 (color h a) (color h i) / 64)
    (R T j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2)
    (hmass : ∀ h, ∑ i, u h i = 4*T) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) *
        (∑ h, weight h * (2 : ℝ)^(finiteHistoryCost (rows h) (j-ell) 0 ell)) ≤
      (∑ h, weight h) *
        (2 : ℝ)^((R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2) := by
  apply weighted_rpow_sum_le weight _ hw
  intro h
  exact critical_add_historyCost_le_reserve (rows h) (color h) (u h)
    (hu h) (hk h) (hb h) (hpair h) R T j ell hj hell (hmass h)

end SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy
