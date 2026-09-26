import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierHistorySum
import SymmetricSubgroupAsymptotics.BinaryCarrierWordOrderBound

/-! Install the numerical reserve on the actual complete carrier-word sum.
The certificates bind each literal history's group-derived rows. All original
normal multiplicities survive as the product of the actual axis-weight sums.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

open BinaryCarrierCone JointCapacityRow BinaryCarrierHistoryEnergy

attribute [local instance] Fintype.ofFinite

/-- Concrete row and pair obligations, not a subgroup-count or energy bound.
Colours may depend on the normal choice. Repeated original factors retain
distinct positions, and every complete history has the same physical mass. -/
structure CertifiedHistoryRows (w : List Factor) (T : ℝ) where
  color : History w → Fin w.length → Fin 6
  mass : History w → Fin w.length → ℝ
  mass_nonneg : ∀ h i, 0 ≤ mass h i
  head_le : ∀ h i, ((rows h i).k : ℝ) ≤ mass h i * alpha (color h i)
  second_le : ∀ h i, ((max (rows h i).m (rows h i).a₂ : ℕ) : ℝ) ≤
    mass h i * beta (color h i)
  pair_le : ∀ h a i, a < i → symmetricSupport (rows h a) (rows h i) ≤
    mass h a * mass h i * pairMatrix64 (color h a) (color h i) / 64
  total_mass : ∀ h, ∑ i, mass h i = 4*T

/-- Every actual history is included once, with its original axis weight. -/
theorem normalHistorySum_le_reserve (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (T : ℝ) (cert : CertifiedHistoryRows w T)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) * normalHistorySum w v (j-ell) 0 ell ≤
      axisWeightProduct w v *
        (2 : ℝ)^((R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2) := by
  rw [normalHistorySum_eq_finiteHistoryCost_sum,
    ← historyWeight_sum_eq_axisWeightProduct]
  exact weighted_histories_le_reserve (fun h : History w => rows h)
    cert.color cert.mass (historyWeight w v) (historyWeight_nonneg w v hv)
    cert.mass_nonneg cert.head_le cert.second_le cert.pair_le
    R T j ell hj hell cert.total_mass

/-- The complete original marked subgroup family now has a derived
quadratic reserve, with the explicit polynomial loss and literal normal
weight mass still displayed. No owner or catalogue coverage is inferred. -/
theorem markedSum_le_reserve_of_orderBound
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : Subgroup (Product w) → Prop) (T : ℝ) (cert : CertifiedHistoryRows w T)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) * markedSum w v P (j-ell) 0 ell ≤
      (((binaryStructuredOrderConstant b *
        (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length) *
        axisWeightProduct w v *
          (2 : ℝ)^((R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2) := by
  let D : ℝ := (((binaryStructuredOrderConstant b *
    (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length)
  have hD : 0 ≤ D := pow_nonneg (Nat.cast_nonneg _) _
  have hsum := markedSum_le_history_of_orderBound w b hb v hv P
    (j-ell) 0 ell le_rfl hell.1
  calc
    _ ≤ (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) *
        (D * normalHistorySum w v (j-ell) 0 ell) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
    _ = D * ((2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) *
        normalHistorySum w v (j-ell) 0 ell) := by ring
    _ ≤ D * (axisWeightProduct w v *
        (2 : ℝ)^((R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2)) :=
      mul_le_mul_of_nonneg_left (normalHistorySum_le_reserve w v hv T cert R j ell hj hell) hD
    _ = _ := by dsimp only [D]; ring

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
