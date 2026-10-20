import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CompleteActualQuotientEnvelope
import SymmetricSubgroupAsymptotics.MixedKernelRankTailResidual
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! Actual central-C4 coordinates yield complete width-sixteen sources.
The marked moment is explicit only at this local numerical composition;
its ordinary-literature construction is separate from action recognition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {U : PreE7NonPairActionClass 16}

private def dataOfEnvelope
    (henvelope : ∀ b : ℕ,
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := preE7NonPairAction 16 U) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 7 b+
        MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b) :
    MixedKernelRankTailResidual.Data 16 U where
  cold := (2 : ℝ)^(512 : ℕ)
  theta := 381/192
  hotBinary := (2 : ℝ)^(256 : ℕ)
  factorialPowerBinary := 7
  hotC4 := (2 : ℝ)^(256 : ℕ)
  factorialPowerC4 := 22
  cold_nonneg := by positivity
  hotBinary_nonneg := by positivity
  hotC4_nonneg := by positivity
  cold_le := le_rfl
  width := Or.inr rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction 16 U) P J) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := preE7NonPairAction 16 U) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction 16 U) P N J)
    exact hphysical.trans (by simpa only [add_assoc] using henvelope b)

variable {c d : ℕ}
  (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)

def cubicActualSourceData
    (D : ScalarFourCentralC4TopCoordinates (preE7NonPairAction 16 U) CyclicThree c d)
    (hc : c≤3) (hd : d≤3) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f) :
    MixedKernelRankTailResidual.Data 16 U :=
  dataOfEnvelope (fun b => D.complete_cubic_quotient_envelope hc hd hcubic f hf hZmud lit b)

def cubicActualSource
    (D : ScalarFourCentralC4TopCoordinates (preE7NonPairAction 16 U) CyclicThree c d)
    (hc : c≤3) (hd : d≤3) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hM4 : GlobalMarkedC4MomentBound) : PreE7RankTailSourceOrYonedaTopData 16 U :=
  (cubicActualSourceData hZmud lit D hc hd hcubic f hf).finalSource hM4

def symmetricActualSourceData {T : Type} [Group T] [Finite T]
    (D : ScalarFourCentralC4TopCoordinates (preE7NonPairAction 16 U) T c d)
    (e : T ≃* Equiv.Perm (Fin 3)) (hc : c≤3) (hd : d≤3)
    (hcubic : orderOf D.cubic=3) : MixedKernelRankTailResidual.Data 16 U :=
  dataOfEnvelope (fun b => D.complete_symmetric_quotient_envelope e hc hd hcubic hZmud lit b)

def symmetricActualSource {T : Type} [Group T] [Finite T]
    (D : ScalarFourCentralC4TopCoordinates (preE7NonPairAction 16 U) T c d)
    (e : T ≃* Equiv.Perm (Fin 3)) (hc : c≤3) (hd : d≤3)
    (hcubic : orderOf D.cubic=3) (hM4 : GlobalMarkedC4MomentBound) :
    PreE7RankTailSourceOrYonedaTopData 16 U :=
  (symmetricActualSourceData hZmud lit D e hc hd hcubic).finalSource hM4

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
