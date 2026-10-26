import SymmetricSubgroupAsymptotics.CFSGTitsFourOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionOuterWord

/-! Evaluation at the actual outer root determines the literal opposed
Sylow pair stabilizer. The other three genuine generators are recovered
from that root and the already-fixed intrinsic opposition, middle Weyl
and middle square. No automorphism is extended to the full fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterEvaluation
open CFSGTitsAmbientPairAlignment CFSGTitsMiddleWeylRecovery
open CFSGTitsIntrinsicMiddleSquare CFSGReeFFourSignedOuterOddProduct
open CFSGReeFFourOppositionOuterWord CFSGReeFFourOuterThreeWord
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourFixedModelEquivalence
private abbrev D := commutator (originalModelFixed 0)

theorem outerWeyl_recovery : originalOuterWeyl 0=
    originalOuterRoot 0*(oppositionRoot*originalOuterRoot 0*oppositionRoot⁻¹)*
      originalOuterRoot 0 := by
  have hs : derivedOuterWeyl 0=derivedOuterRoot 0*
      (derivedOuterWeyl 0*derivedOuterRoot 0*(derivedOuterWeyl 0)⁻¹)*
        derivedOuterRoot 0 := Subtype.ext (outerWeyl_three_word 0)
  have hm := congrArg (derivedReeHom 0) hs
  simp only [map_mul,map_inv] at hm
  change originalOuterWeyl 0=originalOuterRoot 0*negativeOriginalOuterRoot 0*
    originalOuterRoot 0 at hm
  have hO := congrArg (fun F : MulAut CFSG.Models.Tits => F (originalOuterRoot 0))
    oppositionRoot_action
  change oppositionRoot*originalOuterRoot 0*oppositionRoot⁻¹=
    CFSGReeFFourAmbientCentralQuotientAction.ambientAction 0
      (CFSGReeFFourOppositionFixedPositiveNegative.oppositionFixed 0)
      (originalOuterRoot 0) at hO
  have hn := hO.trans (original_opposition_outer_conjugation 0)
  exact hm.trans (congrArg (fun z : CFSG.Models.Tits =>
    originalOuterRoot 0*z*originalOuterRoot 0) hn.symm)

theorem outerEvaluation_injective :
    Function.Injective (fun f : pairStabilizer => f.val (originalOuterRoot 0)) := by
  intro f g hx
  apply Subtype.ext
  apply MulEquiv.toMonoidHom_injective
  apply CFSGTitsFourOrdinaryGenerators.hom_ext
  intro i
  fin_cases i
  · exact hx
  · change f.val (originalOuterWeyl 0)=g.val (originalOuterWeyl 0)
    rw [outerWeyl_recovery]
    simp only [map_mul,map_inv,pairStabilizer_fixes_oppositionRoot,hx]
  · change f.val middleWeylRoot=g.val middleWeylRoot
    rw [pairStabilizer_fixes_middleWeylRoot,pairStabilizer_fixes_middleWeylRoot]
  · change f.val middleSquareRoot=g.val middleSquareRoot
    rw [pairStabilizer_fixes_middleSquareRoot,pairStabilizer_fixes_middleSquareRoot]

end SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterEvaluation
