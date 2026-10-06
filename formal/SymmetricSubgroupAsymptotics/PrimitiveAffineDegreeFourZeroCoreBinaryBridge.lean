import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySocle
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreResidualAssembly

/-!
# Close the degree-four zero-core bridge callbacks

The binary Schur assembly is uniform in the original action, block system,
and retained normal axis.  It therefore supplies both exact finite-frame
callbacks required by the residual dispatcher.  The eight- and
sixteen-block callbacks remain distinct, so the five-slot row cannot be
applied to the sixteen-block frame.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Uniform five-slot callback for the literal eight-block frame. -/
noncomputable def degreeFourZeroCoreEightBridgeInput_of_binarySchur
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreEightBridgeInput := by
  intro w U basePoint block P _inst
  exact degreeFourZeroCoreEightNoncentralSocleBridge
    block P hMN hTraceyPerm

/-- Uniform ten-slot callback for the literal sixteen-block frame. -/
noncomputable def degreeFourZeroCoreSixteenBridgeInput_of_binarySchur
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreSixteenBridgeInput := by
  intro w U basePoint block P _inst
  exact degreeFourZeroCoreSixteenNoncentralSocleBridge
    block P hMN hTraceyPerm

/-- Residual zero-core source with the project-owned noncentral-socle
callbacks discharged by the literal binary Schur theorem. -/
noncomputable def degreeFourZeroCoreResidualSource_of_binarySchur
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (degreeSixteenOwner : ∀ V : PreE7NonPairActionClass 16,
      PreE7RankTailSourceOrYonedaTopData 16 V)
    (frames8 : DegreeFourZeroCoreEightFrameBoundsInput)
    (frames16 : DegreeFourZeroCoreSixteenFrameBoundsInput) :
    DegreeFourZeroCoreResidualSource :=
  degreeFourZeroCoreResidualSource_of_finiteFrames
    hZmud lit hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    degreeSixteenOwner
    (degreeFourZeroCoreEightBridgeInput_of_binarySchur hMN hTraceyPerm)
    (degreeFourZeroCoreSixteenBridgeInput_of_binarySchur hMN hTraceyPerm)
    frames8 frames16

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
