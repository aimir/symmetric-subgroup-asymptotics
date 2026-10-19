import SymmetricSubgroupAsymptotics.Selected1542TwoLayerQuotient
import SymmetricSubgroupAsymptotics.Selected1542MonolithicSocles
import SymmetricSubgroupAsymptotics.Selected1542ActualCentralRepeat
import SymmetricSubgroupAsymptotics.Selected1542LiteralActionClass
import SymmetricSubgroupAsymptotics.MonolithicCompleteSourceSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientReserve
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailResidual
import SymmetricSubgroupAsymptotics.CyclicThreeRegularPermutation

/-! The selected literal action has a complete source from two actual
monoliths and the same original N8 quotient. All original normal axes are
retained; no finite normal registry or numerical capacity premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
open Non2UnipotentPrefixFiniteMenu

theorem complete_sum_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Original) J) ≤
      (2 : ℝ)^(322 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 19 b := by
  have hG : Nat.card Original ≤ 2^12 := by rw [original_card]; norm_num
  letI : (show Subgroup (Original ⧸ originalFirstAxis) from secondAxis).Normal := by
    change secondAxis.Normal
    infer_instance
  have hm := MonolithicCompleteSourceSum.complete_sum_le_two hG originalFirstAxis
    (fun N hNN hN => original_first_monolith N hNN hN) secondAxis
    (fun N hNN hN => original_second_monolith N hNN hN)
    original_socle_bound_one firstQuotient_socle_bound_one hZmud lit b
  change (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Original) J) ≤
      (2 : ℝ)^(145 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := FirstQuotient ⧸ secondAxis) J at hm
  simp_rw [completeQuotientWeight_congr twoLayerQuotientEquiv] at hm
  have hq := actualCentralRepeat.complete_quotient_envelope_with_reserve
    (by decide) (by decide) rfl CyclicThreeRegularPermutation.representation
    CyclicThreeRegularPermutation.representation_injective hZmud lit b
  have hp : (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) ≤
      (2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right (by norm_num : (43/30 : ℝ) ≤ 381/192)
        (Nat.cast_nonneg b))
  have hc : (2 : ℝ)^(145 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) ≤
      (2 : ℝ)^(321 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 145 ≤ 321))
        hp (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have hh := hm.trans (add_le_add le_rfl hq)
  calc
    _ ≤ _ := hh
    _ ≤ (2 : ℝ)^(321 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        ((2 : ℝ)^(321 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
          BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 19 b) :=
      add_le_add hc le_rfl
    _ = _ := by
      rw [pow_succ (2 : ℝ) 321]
      generalize (2 : ℝ)^(321 : ℕ)=z
      ring

def sourceDataOfEquivalence (U : PreE7NonPairActionClass 16)
    (e : preE7NonPairAction 16 U ≃* Original)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    BinaryKernelRankTailResidual.Data 16 U where
  cold := (2 : ℝ)^(322 : ℕ)
  theta := 381/192
  hot := (2 : ℝ)^(256 : ℕ)
  factorialPower := 19
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 322 ≤ 512)
  width := Or.inr rfl
  tail_gap := by norm_num [halfDegree, preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction 16 U) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Original) J := by
      apply Finset.sum_le_sum
      intro J _
      rw [← completeQuotientWeight_congr e J]
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction 16 U) P N J)
    exact hphysical.trans (complete_sum_le hZmud lit b)

def sourceOfEquivalence (U : PreE7NonPairActionClass 16)
    (e : preE7NonPairAction 16 U ≃* Original)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 16 U :=
  (sourceDataOfEquivalence U e hZmud lit).finalSource

def literalSource (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 16 literalRepresentative :=
  sourceOfEquivalence literalRepresentative literalRepresentativeEquiv hZmud lit

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
