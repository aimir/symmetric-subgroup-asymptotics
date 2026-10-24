import SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget

/-! SAME-chief weighted ordinary costs from bounds on the literal local
induced capacities. Unlike an abstract ElementaryCharge callback, this
interface can consume stronger theorems about actual local charts without
adding unproved fields to the older charge structure. No extension-rank
claim or final scalar estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefLayerWeightBudget
open ActualWreathChiefWeightedPrimeBudget ActualWreathChiefPrimeMultiplicityBudget

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_weightedOrder {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (hcap : ∀ (T : ActualWreathCompressionState Q I) {D' : Type}
      [Group D'] [Finite D'] (phi : T.D →* D') (C : ElementaryMinimalNormalChart phi.ker),
      (ActualWreathElementaryOrdinaryStep.layerCapacity T phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p) :
    (n : ℝ) ≤ weightedOrder weight (Nat.card S.D) := by
  have hw0 : ∀ p, 0 ≤ weight p := fun p => le_trans (by norm_num) (hw p)
  induction h with
  | terminal S hD =>
      simpa only [Nat.cast_zero] using weightedOrder_nonneg weight hw0 (Nat.card S.D)
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (weightedOrder_mono_of_dvd weight hw0
        (Nat.card_pos (α := D')).ne' (Nat.card_pos (α := S.D)).ne'
        (Subgroup.card_dvd_of_surjective phi hphi))
  | elementary S D' phi hphi hmin C n next ih =>
      have hc := hcap S phi C
      change (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p at hc
      have heq : (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p =
          weightedOrder weight (Nat.card phi.ker) := by
        rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C,
          weightedOrder_prime_pow weight C.p_prime]
      have hc' := hc.trans_eq heq
      change (n : ℝ) ≤ weightedOrder weight (Nat.card D') at ih
      have hh := add_le_add hc' ih
      rw [←weightedOrder_mul weight (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      simpa only [Nat.cast_add] using hh
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hc := factor_genRank_le_local_cardFactors S.rho phi S.rho_injective C j
      have hcR : (MarkedC4.genRank (C.factor j) : ℝ) ≤
          ArithmeticFunction.cardFactors (Nat.card phi.ker) := by exact_mod_cast hc
      have hc' := hcR.trans (cardFactors_le_weightedOrder weight hw (Nat.card phi.ker))
      change (n : ℝ) ≤ weightedOrder weight (Nat.card D') at ih
      have hh := add_le_add hc' ih
      rw [←weightedOrder_mul weight (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      simpa only [Nat.cast_add] using hh

theorem exists_weightedOrder_bound (S : ActualWreathCompressionState Q I)
    (i : I) (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (hcap : ∀ (T : ActualWreathCompressionState Q I) {D' : Type}
      [Group D'] [Finite D'] (phi : T.D →* D') (C : ElementaryMinimalNormalChart phi.ker),
      (ActualWreathElementaryOrdinaryStep.layerCapacity T phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      (n : ℝ) ≤ weightedOrder weight (Nat.card S.D) ∧
      MarkedC4.genRank S.A ≤ n + MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,cost_le_weightedOrder hn weight hw hcap,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn⟩

end SymmetricSubgroupAsymptotics.ActualWreathChiefLayerWeightBudget
