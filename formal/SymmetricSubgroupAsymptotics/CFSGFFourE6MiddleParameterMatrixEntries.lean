import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylMatrixEntries

/-! All-parameter entries on the same proved norm26 basis. The middle
axes retain their genuine linear and quadratic coefficients; no finite
candidate or separate natural rank-one representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries
open scoped Classical
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

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries
end

namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6NormQuotientCoefficientPilot

-- This polynomial expression is computable even over F2 polynomial rings.
def parameterEntry {R : Type*} [Ring R] (neg : Bool) (axis : Fin 4) (t : R)
    (j k : Fin 26) : R :=
  let r := if neg then negativeLabel (columnLabels j) else columnLabels j
  let s := if neg then negativeLabel (columnLabels k) else columnLabels k
  (if j=k then 1 else 0)+
    t*(normEntry (if axis=1 then shortFirst else longFirst) r s : R)+
    t^2*(normEntry (if axis=1 then shortSecond else longSecond) r s : R)

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries

noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries
open scoped Classical
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylBasisLabels
open CFSGFFourE6NormMatrixAction CFSGFFourE6NormMatrixNegativeAction
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormSimpleCoefficientPilot
open CFSGFFourE6NormSimpleParameters CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6NormQuotientOppositionLabels CFSGFFourE6CharacteristicTwoNormImage

theorem normMatrixAction_middle_parameter_entry (K : Type) [Field K] [CharP K 2]
    (neg : Bool) (axis : Fin 4) (haxis : axis=1∨axis=2) (t : K) (j k : Fin 26) :
    normMatrixAction K (foldedRoot K neg axis t) (basisIndex j) (basisIndex k)=
      parameterEntry neg axis t j k := by
  have hactual : normMatrixAction K (foldedRoot K neg axis t) (basisIndex j) (basisIndex k)=
      normMatrixAction K (foldedRoot K false axis t) (signedBasisIndex neg j) (signedBasisIndex neg k) := by
    cases neg
    · rfl
    · exact normMatrixAction_negative_entry K axis t (basisIndex j) (basisIndex k)
  have hE : firstEntry axis=(if axis=1 then shortFirst else longFirst) := by
    rcases haxis with rfl|rfl <;> rfl
  have hD : quadraticEntry axis=(if axis=1 then shortSecond else longSecond) := by
    rcases haxis with rfl|rfl <;> rfl
  have hdelta : signedBasisIndex neg j=signedBasisIndex neg k ↔ j=k :=
    (signedBasisIndex_injective neg).eq_iff
  rw [hactual,normMatrixAction_positive_entry,first_norm_coefficient,quadratic_norm_coefficient,hE,hD]
  simp only [normCoefficient,normIndex_signed,parameterEntry,normEntry,Pi.single_apply,hdelta]

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleParameterMatrixEntries
