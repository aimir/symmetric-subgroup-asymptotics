import SymmetricSubgroupAsymptotics.BinaryCarrierWordTerminalEnergy
import SymmetricSubgroupAsymptotics.BinaryCarrierWordWeightMass

/-! A uniform complete weighted carrier/terminal bound. Normal-history
multiplicity is derived from the actual factor orders. The only weight
upper bound is the stated bound on each original axis weight; no total
weighted-count estimate is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

attribute [local instance] Fintype.ofFinite

/-- Every remaining multiplicity and terminal factor is explicit. This
bound supports later profile estimates; it does not assert that those
factors are negligible for every value of T or that all owners are covered. -/
theorem terminal_weighted_subfamilies_le_uniform
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (M : ℝ) (hM : 0 ≤ M) (hle : WeightsLe w v M)
    (P : ∀ H : Family w, Subgroup (CriticalProductGroup a s × H.1) → Prop)
    (T : ℝ) (cert : CertifiedHistoryRows w T) :
    (∑ H : Family w, weight w v H *
      (Nat.card {K : TerminalActualSubgroups a s H.1 // P H K.1} : ℝ)) ≤
      (((binaryStructuredOrderConstant b *
        (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length) *
        (((eulerProduct⁻¹)^3 * ((criticalProductRank a s+1 : ℕ) : ℝ) *
          (∑ ell ∈ Finset.range (Fintype.card ι+1), (72 : ℝ)^ell)) *
            ((M * (2 : ℝ)^(2^b : ℕ))^w.length *
              (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*T)^2/4 -
                (25/82)*(criticalProductRank a s)*T - (29/164)*T^2))) := by
  apply (terminal_weighted_subfamilies_le_reserve a s w b hb v hv P T cert).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left _
    (by positivity [euler_positive])
  exact mul_le_mul_of_nonneg_right
    (axisWeightProduct_le_of_orderBound w b hb v hv M hM hle)
    (Real.rpow_nonneg (by norm_num) _)

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
