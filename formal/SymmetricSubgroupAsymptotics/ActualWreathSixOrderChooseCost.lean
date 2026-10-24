import SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights

/-! A local component whose ACTUAL order divides six costs one binary
exact-choose rate and one binary-prime-to rate on the same chief trace.
This is an order-divisibility consumer, not a supplied generator bound or
a split description of the actual source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity

theorem weightedOrder_six (weight : ℕ → ℝ) :
    weightedOrder weight 6 = weight 2 + weight 3 := by
  have hsix : (6 : ℕ) = 2 ^ 1 * 3 ^ 1 := by norm_num
  rw [hsix,weightedOrder_mul weight (by norm_num) (by norm_num),
    weightedOrder_prime_pow weight Nat.prime_two,
    weightedOrder_prime_pow weight (by norm_num : Nat.Prime 3)]
  norm_num

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)

theorem genRank_le_primary_choose_add_primeTo (i : I) (hI : 2 ≤ Fintype.card I)
    (horder : Nat.card S.D ∣ 6) (a : ℕ) (hd : 2 ^ a ∣ Fintype.card I) :
    (MarkedC4.genRank S.A : ℝ) ≤ (Fintype.card I : ℝ) * primaryRate 2 a +
      (Fintype.card I : ℝ) / (2 : ℝ) ^ a + MarkedC4.genRank Q := by
  obtain ⟨c,hc,hcost,hgen⟩ := ActualWreathChiefChooseDivisorWeights.exists_divisorWeight_bound
    S i hI 2 a Nat.prime_two hd
  have ht : 0 < Fintype.card I := by omega
  have hlocal := weightedOrder_mono_of_dvd (divisorWeight (Fintype.card I) 2 a)
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_divisorWeight _ _ _ p))
    (Nat.card_pos (α := S.D)).ne' (by norm_num : (6 : ℕ) ≠ 0) horder
  rw [weightedOrder_six] at hlocal
  have htwo := divisorWeight_le_divisorRate (Fintype.card I) 2 a 2 ht Nat.prime_two hd
  have hthree := divisorWeight_le_divisorRate (Fintype.card I) 2 a 3 ht Nat.prime_two hd
  change divisorWeight (Fintype.card I) 2 a 2 ≤ (Fintype.card I : ℝ) * primaryRate 2 a at htwo
  change divisorWeight (Fintype.card I) 2 a 3 ≤ (Fintype.card I : ℝ) / (2 : ℝ) ^ a at hthree
  have hgenR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ) + MarkedC4.genRank Q := by
    exact_mod_cast hgen
  linarith

end SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost
