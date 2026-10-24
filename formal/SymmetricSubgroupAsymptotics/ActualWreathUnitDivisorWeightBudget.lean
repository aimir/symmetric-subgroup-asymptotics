import SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights
import SymmetricSubgroupAsymptotics.ElementaryChargeUnitLogarithmic
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! The SAME chief trace simultaneously retains its exact divisor rate
and the proved logarithmic constant1. Taking the minimum is valid on
actual elementary charts; both rates are at leastone, so genuine internal
simple-factor ordinary costs remain paid. No +1 premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathUnitDivisorWeightBudget
open ActualWreathChooseDivisorCapacity ActualWreathChiefWeightedPrimeBudget
open ActualWreathCharacteristicChiefProfile

def weight (t q e p : ℕ) : ℝ :=
  min ((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) (divisorWeight t q e p)

theorem one_le_weight (t : ℕ) (ht : 2 ≤ t) (q e p : ℕ) : 1 ≤ weight t q e p := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 < Real.logb 2 (t : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < t by omega))
  have hroot := Real.sqrt_pos.mpr hL
  have hsle : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ (t : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,LargeOrbitGeneratorNumerics.logb_le_square htR⟩
  exact le_min ((le_div_iff₀ hroot).mpr (by simpa only [one_mul] using hsle))
    (one_le_divisorWeight t q e p)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem layerCapacity_le_weight (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] (phi : S.D →* D')
    (C : ElementaryMinimalNormalChart phi.ker) (i : I) (hI : 2 ≤ Fintype.card I)
    (q e : ℕ) (hq : q.Prime) (hd : q^e ∣ Fintype.card I) :
    (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*weight (Fintype.card I) q e C.p := by
  let c := actualCharge S phi C i hI
  have hlog := ElementaryChargeUnitLogarithmic.logarithmic_real c hI
  have hlog' : (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*
        ((Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ))) := by
    simpa only [c,actualCharge,mul_div_assoc] using hlog
  have hdiv := layerCapacity_le_divisorWeight S phi C i hI q e hq hd
  rw [weight,mul_min_of_nonneg _ _ (show (0 : ℝ) ≤ Module.finrank (ZMod C.p) C.V by positivity)]
  exact le_min hlog' hdiv

theorem cost_le_weightedOrder {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (q e : ℕ) (hq : q.Prime)
    (hd : q^e ∣ Fintype.card I) :
    (n : ℝ) ≤ weightedOrder (weight (Fintype.card I) q e) (Nat.card S.D) := by
  apply ActualWreathChiefLayerWeightBudget.cost_le_weightedOrder h _
    (one_le_weight (Fintype.card I) hI q e)
  intro T D' _ _ phi C
  exact layerCapacity_le_weight T phi C i hI q e hq hd

end SymmetricSubgroupAsymptotics.ActualWreathUnitDivisorWeightBudget
