import SymmetricSubgroupAsymptotics.PairedEightNaturalDualCapacityDispatch
import SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics
import SymmetricSubgroupAsymptotics.SocleTwoTopEpimorphismEnvelopes

/-! Independent top cost on every literal normal quotient of every one of
the 24 nonbinary eight-point tops. The module cold cost remains separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops

variable (j : Fin 24) (N : Subgroup (interface j).top) [N.Normal]

def quotientTopCost : ℝ :=
  if IsPGroup 2 ((interface j).top ⧸ N) then 2*Real.logb 2 (38/25)
  else if naturalCapacity j=2 then Real.logb 2 5/3+Real.logb 2 (38/25)
  else 2*(Real.logb 2 5/3)

/-- All actual epimorphisms to the actual top quotient are counted. -/
theorem quotient_top_epi_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J ((interface j).top ⧸ N)) : ℝ) ≤
      (Nat.card (((interface j).top ⧸ N) ≃* ((interface j).top ⧸ N)) : ℝ)*
        (2 : ℝ)^(quotientTopCost j N*b) := by
  have hs := (DegreeTwoPairedEightCompleteCatalogue.completeRow j).topSocle
    ⟨N,inferInstance⟩
  by_cases hQ : IsPGroup 2 ((interface j).top ⧸ N)
  · simpa only [quotientTopCost,if_pos hQ] using
      socleTwo_binary_epi_le hZmud lit hQ hs b J
  · by_cases hc : naturalCapacity j=2
    · have hj := (naturalCapacity_two_iff j).mp hc
      obtain ⟨a,ha⟩ := moduleTwoRow_card j hj
      have hd : Nat.card ((interface j).top ⧸ N) ∣ 2^a*3 := by
        rw [←ha]
        exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N)
      simpa only [quotientTopCost,if_neg hQ,if_pos hc] using
        ternaryOddPart_top_anchor_epi_le hZmud lit hd hQ hs b J
    · simpa only [quotientTopCost,if_neg hQ,if_neg hc] using
        socleTwo_general_epi_le hZmud lit hs b J

/-- The proved module bound and the top count jointly fit one fixed slope. -/
theorem quotient_topCost_plus_module_le :
    quotientTopCost j N+(51/200 : ℝ)*naturalCapacity j ≤ 31/16 := by
  rcases naturalCapacity_one_or_two j with hc|hc
  · by_cases hQ : IsPGroup 2 ((interface j).top ⧸ N)
    · simp only [quotientTopCost,if_pos hQ,hc,Nat.cast_one]
      linarith [PairedEightTopCostNumerics.relative_le]
    · simp only [quotientTopCost,if_neg hQ,hc,show (1:ℕ)≠2 by decide,
        if_false,Nat.cast_one]
      exact PairedEightTopCostNumerics.general_two_plus_one_cold
  · by_cases hQ : IsPGroup 2 ((interface j).top ⧸ N)
    · simp only [quotientTopCost,if_pos hQ,hc,Nat.cast_ofNat]
      exact PairedEightTopCostNumerics.binary_plus_two_cold
    · simp only [quotientTopCost,if_neg hQ,hc,if_pos rfl,Nat.cast_ofNat]
      exact PairedEightTopCostNumerics.anchor_plus_two_cold

/-- Module cold characters are charged alongside every top map, with the
actual top automorphism coefficient kept visible. -/
theorem quotient_top_epi_mul_module_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J ((interface j).top ⧸ N)) : ℝ)*
      (2 : ℝ)^(((51/200 : ℝ)*naturalCapacity j)*b) ≤
      (Nat.card (((interface j).top ⧸ N) ≃* ((interface j).top ⧸ N)) : ℝ)*
        (2 : ℝ)^((31/16 : ℝ)*b) := by
  have h := mul_le_mul_of_nonneg_right
    (quotient_top_epi_le j N hZmud lit b J)
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2)
      (((51/200 : ℝ)*naturalCapacity j)*b))
  have hp : (2 : ℝ)^(quotientTopCost j N*b)*
      (2 : ℝ)^(((51/200 : ℝ)*naturalCapacity j)*b) ≤
      (2 : ℝ)^((31/16 : ℝ)*b) := by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    have := mul_le_mul_of_nonneg_right (quotient_topCost_plus_module_le j N)
      (Nat.cast_nonneg b : (0:ℝ)≤b)
    nlinarith
  exact h.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops
