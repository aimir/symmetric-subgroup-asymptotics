import SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost

/-! Arbitrary actual primary divisors on the SAME order-six chief trace.
This extends the existing binary presentation of the cost to every
prime, retaining a fixed cost proof for later simultaneous estimates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixOrderDivisorCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    {i : I} {S : ActualWreathCompressionState Q I} {c : ℕ}

theorem cost_le_divisor_rates (hc : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S c)
    (hI : 2 ≤ Fintype.card I) (horder : Nat.card S.D ∣ 6)
    (q a : ℕ) (hq : q.Prime) (hdiv : q^a ∣ Fintype.card I) :
    (c : ℝ) ≤ divisorRate (Fintype.card I) q a 2+divisorRate (Fintype.card I) q a 3 := by
  have hcost := ActualWreathChiefChooseDivisorWeights.cost_le_divisorWeight hc hI q a hq hdiv
  have hlocal := weightedOrder_mono_of_dvd (divisorWeight (Fintype.card I) q a)
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_divisorWeight _ _ _ p))
    (Nat.card_pos (α := S.D)).ne' (by norm_num : (6 : ℕ) ≠ 0) horder
  rw [ActualWreathSixOrderChooseCost.weightedOrder_six] at hlocal
  have htwo := divisorWeight_le_divisorRate (Fintype.card I) q a 2 (by omega) hq hdiv
  have hthree := divisorWeight_le_divisorRate (Fintype.card I) q a 3 (by omega) hq hdiv
  exact (hcost.trans hlocal).trans (add_le_add htwo hthree)

theorem cost_le_two_primeTo (hc : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S c)
    (hI : 2 ≤ Fintype.card I) (horder : Nat.card S.D ∣ 6)
    (q a : ℕ) (hq : q.Prime) (hdiv : q^a ∣ Fintype.card I)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    (c : ℝ) ≤ 2*(Fintype.card I : ℝ)/(q : ℝ)^a := by
  have hh := cost_le_divisor_rates hc hI horder q a hq hdiv
  simp only [divisorRate,if_neg (Ne.symm hq2),if_neg (Ne.symm hq3)] at hh
  convert hh using 1 <;> ring

end SymmetricSubgroupAsymptotics.ActualWreathSixOrderDivisorCost
