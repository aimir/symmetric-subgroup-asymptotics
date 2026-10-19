import SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceBudget
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientBudget

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
open Non2UnipotentPrefixFiniteMenu
variable {Q : Type} [Group Q] [Finite Q]

theorem axis_sum_le (hQ : Nat.card Q≤2^15) (hchoice : Choice Q)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        (BinaryKernelRankTailNumerics.raw 1 21 b+MarkedC4KernelRankTailNumerics.raw 1 21 b) := by
  have hb : 0≤BinaryKernelRankTailNumerics.raw 1 21 b := by
    unfold BinaryKernelRankTailNumerics.raw; positivity
  have h4 : 0≤MarkedC4KernelRankTailNumerics.raw 1 21 b := by
    unfold MarkedC4KernelRankTailNumerics.raw markedC4Moment; positivity
  unfold Choice at hchoice
  rcases hchoice with ⟨C,hC⟩ | hbinary | hfour
  · have haut : (Nat.card (Q ≃* Q) : ℝ)≤(2 : ℝ)^(225 : ℕ) := by
      exact_mod_cast aut_card_le hQ
    have he (J : Subgroup (Equiv.Perm (Fin b))) :
        (Nat.card (GroupEpimorphism J Q) : ℝ)≤
          (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) := by
      exact (C.envelope lit b J).trans (mul_le_mul haut
        (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right hC (by positivity))) (by positivity) (by positivity))
    have hh : (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ))≤
        (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
      calc
        _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),
            (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
          Finset.sum_le_sum (fun J _ => he J)
        _ = _ := by simp [subgroupCount,mul_comm]
    exact hh.trans (le_add_of_nonneg_right (add_nonneg hb h4))
  · obtain ⟨B⟩ := hbinary
    have ht := ScalarFourCentralC4TopCoordinates.embedded_top_card_le B.topEmbedding B.topEmbedding_injective
    have hraw := B.coordinates.raw_summed_count B.central_rank B.active_rank
      B.topEmbedding B.topEmbedding_injective hZmud lit 15 hQ b
    have hr : (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J Q) : ℝ))≤
        BinaryKernelRankTailNumerics.raw 1 (15+Nat.card B.T) b+
          (subgroupCount b : ℝ)*(B.coordinates.coldCoefficient*
            (2 : ℝ)^(ScalarFourCentralTopCoordinates.coldSlope*b)) := by
      simpa only [BinaryKernelRankTailNumerics.raw,one_mul] using hraw
    have hhot := binary_raw_mono (15+Nat.card B.T) b (by omega)
    have hcold : (subgroupCount b : ℝ)*(B.coordinates.coldCoefficient*
        (2 : ℝ)^(ScalarFourCentralTopCoordinates.coldSlope*b))≤
        (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
      have hpow : (2 : ℝ)^(ScalarFourCentralTopCoordinates.coldSlope*(b : ℝ))≤
          (2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
          (mul_le_mul_of_nonneg_right ScalarFourCentralTopCoordinates.coldSlope_le_common
            (show 0≤(b : ℝ) by positivity))
      have hh := mul_le_mul (binary_coefficient_le B.coordinates hQ B.topEmbedding B.topEmbedding_injective)
        hpow (by positivity) (by positivity)
      simpa only [mul_comm (subgroupCount b : ℝ)] using mul_le_mul_of_nonneg_left hh
        (show 0≤(subgroupCount b : ℝ) by positivity)
    exact hr.trans (by linarith)
  · obtain ⟨B⟩ := hfour
    have ht := ScalarFourCentralC4TopCoordinates.embedded_top_card_le B.topEmbedding B.topEmbedding_injective
    have hr := B.coordinates.raw_summed_count B.central_rank B.active_rank
      B.topEmbedding B.topEmbedding_injective hZmud lit 15 hQ b
    have hhot := c4_raw_mono (15+Nat.card B.T) b (by omega)
    have hs : ScalarFourCentralC4TopCoordinates.coldSlope≤(381/192 : ℝ) :=
      ScalarFourCentralTopCoordinates.coldSlope_le_common
    have hcold : (subgroupCount b : ℝ)*(B.coordinates.coldCoefficient*
        (2 : ℝ)^(ScalarFourCentralC4TopCoordinates.coldSlope*b))≤
        (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
      have hpow : (2 : ℝ)^(ScalarFourCentralC4TopCoordinates.coldSlope*(b : ℝ))≤
          (2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
          (mul_le_mul_of_nonneg_right hs (show 0≤(b : ℝ) by positivity))
      have hh := mul_le_mul (c4_coefficient_le B.coordinates hQ B.topEmbedding B.topEmbedding_injective)
        hpow (by positivity) (by positivity)
      simpa only [mul_comm (subgroupCount b : ℝ)] using mul_le_mul_of_nonneg_left hh
        (show 0≤(subgroupCount b : ℝ) by positivity)
    exact hr.trans (by linarith)

end SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
