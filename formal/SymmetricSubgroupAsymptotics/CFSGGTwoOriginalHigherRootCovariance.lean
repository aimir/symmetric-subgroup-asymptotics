import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalWeylWords
import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalPositiveDirections

/-! The signed higher-root calculation is reflected back into the SAME
original Model through its proved unconditional native equivalence. The
2/4 exchange has a minus sign; no unsigned root-family identification
or original image-faithfulness premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherRootCovariance
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGGTwoPositiveDirections
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalExceptionalWeylWords
open CFSGGTwoOriginalExceptionalModel CFSGGTwoOriginalExceptionalRootCovariance
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoExceptionalPositiveDirections
open CFSGGTwoPositiveRootMatrices
variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem reflectedModel_native (j : Fin 6) :
    (modelEquivNatural K (reflectedModel K j)).val=reflectedUnit K j := by
  fin_cases j
  · exact congrArg Subtype.val (map_one (modelEquivNatural K))
  · exact congrArg Subtype.val (map_one (modelEquivNatural K))
  · change (modelEquivNatural K ((shortWord K)⁻¹)).val=(shortWeyl K)⁻¹
    rw [map_inv,shortWord_native]
    rfl
  · change (modelEquivNatural K ((longWord K)⁻¹ * (shortWord K)⁻¹)).val=
      (longWeyl K)⁻¹ * (shortWeyl K)⁻¹
    rw [map_mul,map_inv,map_inv,longWord_native,shortWord_native]
    rfl
  · change (modelEquivNatural K ((longWord K)⁻¹)).val=(longWeyl K)⁻¹
    rw [map_inv,longWord_native]
    rfl
  · change (modelEquivNatural K ((shortWord K)⁻¹ * (longWord K)⁻¹)).val=
      (shortWeyl K)⁻¹ * (longWeyl K)⁻¹
    rw [map_mul,map_inv,map_inv,shortWord_native,longWord_native]
    rfl

theorem exceptional_positiveModel (j : Fin 6) (t : K) :
    exceptionalModelEquiv K (positiveModel K j t)=
      positiveModel K (exchangedDirection j)
        (signedParameter K j (exceptionalParameter K (rootNode j) t)) := by
  apply (modelEquivNatural K).injective
  rw [exceptional_positiveModel_expression,positiveModel_native]
  apply Subtype.ext
  simp only [map_mul,map_inv]
  change (modelEquivNatural K (reflectedModel K j)).val *
      (modelEquivNatural K (modelRoot CartanMatrix.G₂ K false (exchangedNode (rootNode j))
        (exceptionalParameter K (rootNode j) t))).val *
      ((modelEquivNatural K (reflectedModel K j)).val)⁻¹=
    positiveRoot K (exchangedDirection j)
      (signedParameter K j (exceptionalParameter K (rootNode j) t))
  rw [reflectedModel_native,modelEquivNatural_root]
  change reflectedRoot K j (exceptionalParameter K (rootNode j) t)=
    positiveRoot K (exchangedDirection j)
      (signedParameter K j (exceptionalParameter K (rootNode j) t))
  apply Units.ext
  rw [reflectedRoot_val,positiveRoot_val]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherRootCovariance
