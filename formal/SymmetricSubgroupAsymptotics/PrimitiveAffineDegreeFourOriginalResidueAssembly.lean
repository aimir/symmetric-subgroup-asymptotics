import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFourBlockOriginalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinaryBridge

/-!
The residual assembly with its four-block boundary restricted to the
actual original zero-ternary actions. This removes the unnecessarily
general degree-sixteen owner from the earlier assembler. The remaining
four-block coverage and eight-block and sixteen-block bounds are project-owned
construction boundaries; this conditional assembler does not assert that
they have been populated.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- A source on exactly the four-by-four residue, preserving the original
minimal block, profile, zero-core equation and original action class. -/
abbrev DegreeFourZeroCoreFourBlockOriginalSource :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    Nat.card block.Points = 4 →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Exhaust all numerical residues using only sources for the actual
four-block class, and the unchanged original-frame bounds at eight and
sixteen blocks. -/
noncomputable def degreeFourZeroCoreResidualSource_of_originalResidues
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (fourBlocks : DegreeFourZeroCoreFourBlockOriginalSource)
    (frames8 : DegreeFourZeroCoreEightFrameBoundsInput)
    (frames16 : DegreeFourZeroCoreSixteenFrameBoundsInput) :
    DegreeFourZeroCoreResidualSource := by
  intro w U _hw basePoint block P _inst _hres hr hs hD
  exact match degreeFourZeroCoreExceptionalExhaustion block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD hs with
    | .inl source => source
    | .inr residue => Classical.choice (by
        rcases residue.down with hs2 | hs4 | hs8 | hs16
        · exact ⟨degreeFourZeroCoreTwoBlockSource block P hr hD hs2⟩
        · exact ⟨fourBlocks block P hr hD hs4⟩
        · exact ⟨degreeFourZeroCoreEightBlockSource_of_verifiedFrames block P
            hZmud lit (degreeFourZeroCoreEightBridgeInput_of_binarySchur
              hMN hTraceyPerm block P) hr hD hs8 (frames8 block P hr hD hs8)⟩
        · exact ⟨degreeFourZeroCoreSixteenBlockSource_of_verifiedFrames block P
            hZmud lit (degreeFourZeroCoreSixteenBridgeInput_of_binarySchur
              hMN hTraceyPerm block P) hr hD hs16 (frames16 block P hr hD hs16)⟩)

/-- Final degree-four plumbing, with the three actual unfinished source
boundaries still explicit rather than disguised as published hypotheses. -/
noncomputable def degreeFourResidualSource_of_originalResidues
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (fourBlocks : DegreeFourZeroCoreFourBlockOriginalSource)
    (frames8 : DegreeFourZeroCoreEightFrameBoundsInput)
    (frames16 : DegreeFourZeroCoreSixteenFrameBoundsInput) :
    PrimitiveAffineResidualDegreeSource 4 :=
  degreeFourResidualSource_of_zeroCore hZmud lit hTracey hMN hClifford hTraceyPerm
    (degreeFourZeroCoreResidualSource_of_originalResidues hZmud lit hMN
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm fourBlocks frames8 frames16)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
