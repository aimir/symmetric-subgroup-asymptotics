import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailResidual
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! A reusable width-twelve source from actual symmetric central-repeat
coordinates. Its complete physical quotient sum is proved internally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {U : PreE7NonPairActionClass 12} {T : Type} [Group T] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates (preE7NonPairAction 12 U) T c d)
  (e : T ≃* Equiv.Perm (Fin 3))
  (hc : c≤2) (hd : d≤2) (hcubic : orderOf D.cubic=3)
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def symmetricActualSourceTwoData : BinaryKernelRankTailResidual.Data 12 U where
  cold := (2 : ℝ)^(512 : ℕ)
  theta := 43/30
  hot := (2 : ℝ)^(256 : ℕ)
  factorialPower := 22
  cold_nonneg := by positivity
  hot_nonneg := by positivity
  cold_le := le_rfl
  width := Or.inl rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction 12 U) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := preE7NonPairAction 12 U) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction 12 U) P N J)
    exact hphysical.trans (D.symmetric_complete_quotient_envelope_two e hc hd hcubic hZmud lit b)

def symmetricActualSourceTwo : PreE7RankTailSourceOrYonedaTopData 12 U :=
  (D.symmetricActualSourceTwoData e hc hd hcubic hZmud lit).finalSource

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
