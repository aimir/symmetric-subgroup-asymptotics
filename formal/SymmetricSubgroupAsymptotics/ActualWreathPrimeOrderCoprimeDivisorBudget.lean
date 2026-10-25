import SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights

/-! A literal prime-order local component has only its own characteristic
on the SAME chief trace. A distinct actual prime-power divisor of the top
degree therefore pays the genuine prime-to capacity. No independent full
base or prescribed local module capacity is substituted for the source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathPrimeOrderCoprimeDivisorBudget
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem genRank_le_primeTo_divisor_add_top (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) (p q a : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (horder : Nat.card S.D ∣ p) (hdiv : q^a ∣ Fintype.card I) :
    (MarkedC4.genRank S.A : ℝ) ≤ (Fintype.card I : ℝ)/(q : ℝ)^a + MarkedC4.genRank Q := by
  obtain ⟨c,hc,hcost,hgen⟩ := ActualWreathChiefChooseDivisorWeights.exists_divisorWeight_bound
    S i hI q a hq hdiv
  have hlocal := weightedOrder_mono_of_dvd (divisorWeight (Fintype.card I) q a)
    (fun r => (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_divisorWeight _ _ _ r))
    (Nat.card_pos (α := S.D)).ne' hp.ne_zero horder
  have hprime : weightedOrder (divisorWeight (Fintype.card I) q a) p =
      divisorWeight (Fintype.card I) q a p := by
    simpa only [pow_one,Nat.cast_one,one_mul] using
      (weightedOrder_prime_pow (divisorWeight (Fintype.card I) q a) (a := 1) hp)
  rw [hprime] at hlocal
  have ht : 0 < Fintype.card I := by omega
  have hr := divisorWeight_le_divisorRate (Fintype.card I) q a p ht hq hdiv
  simp only [divisorRate,if_neg hne] at hr
  have hgenR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hgen
  linarith only [hcost,hlocal,hr,hgenR]

end SymmetricSubgroupAsymptotics.ActualWreathPrimeOrderCoprimeDivisorBudget
