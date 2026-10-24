import SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost

/-! The same actual order-six chief trace retains the minimum of two
divisor capacities at each prime. This improves the small shared-head
windows without replacing the source by a split or independent model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixOrderTwoDivisorCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity
open ActualWreathChiefChooseDivisorWeights ActualWreathOrdinaryChiefRecurrence

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)

theorem genRank_le_two_divisor_min (i : I) (hI : 2 ≤ Fintype.card I)
    (horder : Nat.card S.D ∣ 6) (a : ℕ)
    (h2 : 2^a ∣ Fintype.card I) (h3 : 3 ∣ Fintype.card I) :
    (MarkedC4.genRank S.A : ℝ) ≤
      (Fintype.card I : ℝ)*min (primaryRate 2 a) (1/3) +
      (Fintype.card I : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1) +
        MarkedC4.genRank Q := by
  let t := Fintype.card I
  let W : ℕ → ℝ := fun p => min (divisorWeight t 2 a p) (divisorWeight t 3 1 p)
  have ht : 0 < t := by dsimp only [t]; omega
  have htR : (0 : ℝ) ≤ t := by positivity
  have h31 : 3^1 ∣ Fintype.card I := by simpa only [pow_one] using h3
  obtain ⟨c,hc⟩ := exists_chiefCost i S
  have hcost : (c : ℝ) ≤ weightedOrder W (Nat.card S.D) :=
    cost_le_min_divisorWeights hc hI 2 a 3 1 Nat.prime_two h2 Nat.prime_three h31
  have hlocal := weightedOrder_mono_of_dvd W
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans
      (le_min (one_le_divisorWeight t 2 a p) (one_le_divisorWeight t 3 1 p)))
    (Nat.card_pos (α := S.D)).ne' (by norm_num : (6 : ℕ) ≠ 0) horder
  rw [ActualWreathSixOrderChooseCost.weightedOrder_six] at hlocal
  have h22 := divisorWeight_le_divisorRate t 2 a 2 ht Nat.prime_two h2
  have h32 := divisorWeight_le_divisorRate t 3 1 2 ht Nat.prime_three h31
  have h23 := divisorWeight_le_divisorRate t 2 a 3 ht Nat.prime_two h2
  have h33 := divisorWeight_le_divisorRate t 3 1 3 ht Nat.prime_three h31
  change divisorWeight t 2 a 2 ≤ (t : ℝ)*primaryRate 2 a at h22
  simp only [divisorRate,if_neg (by decide : (2 : ℕ) ≠ 3),pow_one] at h32
  change divisorWeight t 2 a 3 ≤ (t : ℝ)/(2 : ℝ)^a at h23
  change divisorWeight t 3 1 3 ≤ (t : ℝ)*primaryRate 3 1 at h33
  have htwo : W 2 ≤ (t : ℝ)*min (primaryRate 2 a) (1/3) := by
    have hb := min_le_min h22 h32
    simpa only [W,mul_min_of_nonneg _ _ htR,mul_one_div] using hb
  have hthree : W 3 ≤ (t : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1) := by
    have hb := min_le_min h23 h33
    simpa only [W,mul_min_of_nonneg _ _ htR,mul_one_div] using hb
  have hgenR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast genRank_le_cost_add_top hc
  change (MarkedC4.genRank S.A : ℝ) ≤
    (t : ℝ)*min (primaryRate 2 a) (1/3) +
      (t : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1) + MarkedC4.genRank Q
  linarith only [hcost,hlocal,htwo,hthree,hgenR]

end SymmetricSubgroupAsymptotics.ActualWreathSixOrderTwoDivisorCost
