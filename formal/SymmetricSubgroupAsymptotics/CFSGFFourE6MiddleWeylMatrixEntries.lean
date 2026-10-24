import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylBasisLabels
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction

/-! Actual signed parameter-one matrix entries for the selected middle
rank-two word. The finite matrices are identified with the same faithful
norm26 action through an explicit bijection of its proved basis labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylMatrixEntries
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylBasisLabels
open CFSGFFourE6NormMatrixAction CFSGFFourE6NormMatrixNegativeAction
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormSimpleCoefficientPilot
open CFSGFFourE6NormSimpleParameters CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6NormQuotientOppositionLabels CFSGFFourE6CharacteristicTwoNormImage

private def signedBasisIndex (neg : Bool) (j : Fin 26) : PairIndex :=
  if neg then negativePair (basisIndex j) else basisIndex j

private theorem signedBasisIndex_injective (neg : Bool) :
    Function.Injective (signedBasisIndex neg) := by
  cases neg
  · exact basisIndex_bijective.1
  · exact negativePair_involutive.injective.comp basisIndex_bijective.1

private theorem normIndex_signed (neg : Bool) (j : Fin 26) :
    normIndex (signedBasisIndex neg j)=
      if neg then negativeLabel (columnLabels j) else columnLabels j := by
  cases neg
  · exact normIndex_basisIndex j
  · exact normIndex_negative_basisIndex j

theorem normMatrixAction_middle_one_entry (K : Type) [Field K] [CharP K 2]
    (neg : Bool) (axis : Fin 4) (haxis : axis=1∨axis=2) (j k : Fin 26) :
    normMatrixAction K (foldedRoot K neg axis 1) (basisIndex j) (basisIndex k)=
      ZMod.castHom (dvd_refl 2) K (oneEntry neg axis j k) := by
  have hactual : normMatrixAction K (foldedRoot K neg axis 1) (basisIndex j) (basisIndex k)=
      normMatrixAction K (foldedRoot K false axis 1) (signedBasisIndex neg j) (signedBasisIndex neg k) := by
    cases neg
    · rfl
    · exact normMatrixAction_negative_entry K axis 1 (basisIndex j) (basisIndex k)
  have hE : firstEntry axis=(if axis=1 then shortFirst else longFirst) := by
    rcases haxis with rfl|rfl <;> rfl
  have hD : quadraticEntry axis=(if axis=1 then shortSecond else longSecond) := by
    rcases haxis with rfl|rfl <;> rfl
  have hdelta : signedBasisIndex neg j=signedBasisIndex neg k ↔ j=k :=
    (signedBasisIndex_injective neg).eq_iff
  rw [hactual,normMatrixAction_positive_entry,first_norm_coefficient,quadratic_norm_coefficient,hE,hD]
  simp only [normCoefficient,normIndex_signed,oneEntry,normEntry,Pi.single_apply,hdelta,
    one_pow,one_mul]
  by_cases hjk : j=k <;>
    simp only [hjk,if_true,if_false,map_add,map_one,map_zero,map_intCast]

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylMatrixEntries
