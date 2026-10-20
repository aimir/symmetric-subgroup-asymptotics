import SymmetricSubgroupAsymptotics.SixPairFullKernelOriginalQuotientSum
import SymmetricSubgroupAsymptotics.SixPairFullKernelCenterQuotientEnvelope
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! Actual representative-facing source for the full-independent
three-pair kernel model. All original normal axes are summed internally.
Physical independence is explicit and is not claimed for arbitrary
proper or correlated subdirect kernels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairFullIndependentSource
open Non2UnipotentPrefixFiniteMenu

variable (p : PreE7PairActionClass 6)
  [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
  (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def data : BinaryKernelRankTailResidual.Data 12 (preE7SixPairNonPairAction p) where
  cold := (2 : ℝ)^(289 : ℕ)
  theta := 43/30
  hot := (2 : ℝ)^(81 : ℕ)
  factorialPower := 15
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 289≤512)
  width := Or.inl rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum (preE7PairAction 6 p) P J)≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := preE7PairAction 6 p) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7PairAction 6 p) P N J)
    have hwhole :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := preE7PairAction 6 p) J)≤
        (2 : ℝ)^(289 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
          BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b := by
      calc
        _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
            ((2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
              completeQuotientWeight
                (R := (preE7PairAction 6 p) ⧸ SixPairFullKernelCenter.centerImage F E) J) :=
          Finset.sum_le_sum (fun J _ =>
            SixPairFullKernelOriginalQuotientSum.complete_weight_le F E hfull hZmud lit b J)
        _ = (2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
            ∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight
              (R := (preE7PairAction 6 p) ⧸ SixPairFullKernelCenter.centerImage F E) J := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
            Fintype.card_eq_nat_card,subgroupCount]
          ring
        _ ≤ (2 : ℝ)^(288 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
            ((2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
              BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b) :=
          add_le_add le_rfl
            (SixPairFullKernelCenterQuotientEnvelope.complete_sum_le F E hfull hZmud lit b)
        _ = ((2 : ℝ)^(288 : ℕ)+(2 : ℝ)^(256 : ℕ))*
            ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ))+
              BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b := by ring
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          have hn : (2 : ℝ)^(288 : ℕ)+(2 : ℝ)^(256 : ℕ)≤(2 : ℝ)^(289 : ℕ) := by
            calc
              _ ≤ (2 : ℝ)^(288 : ℕ)+(2 : ℝ)^(288 : ℕ) :=
                add_le_add le_rfl (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
                  (by decide : 256≤288))
              _ = _ := by
                rw [pow_succ' (2 : ℝ) 288]
                exact (two_mul _).symm
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hn
            (show 0≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) by positivity)
    exact hphysical.trans hwhole

/-- Complete actual original-action source; no quotient census or supplied
count inequality appears among its premises. -/
def source : PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  (data p F E hfull hZmud lit).finalSource

end SymmetricSubgroupAsymptotics.SixPairFullIndependentSource
