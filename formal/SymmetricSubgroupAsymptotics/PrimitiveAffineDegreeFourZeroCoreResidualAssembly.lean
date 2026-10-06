import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreTwoBlocks
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFiniteFrameSource

/-!
# Assembly of the degree-four zero-core residual lane

The generic zero-core capacity theorem leaves only two, four, eight, or
sixteen literal blocks.  Two blocks are impossible.  Four blocks are the
already assigned width-sixteen owner, while eight and sixteen blocks use
the checked finite-frame bounds and the common noncentral-socle bridge.

This file performs that exhaustive dispatch without duplicating any finite
frame or Schur-module argument.  Its inputs are exactly the concrete frame
objects consumed by `degreeFourZeroCoreFiniteResidueSource`; they are
temporary construction boundaries to be instantiated by the adjacent
certificate modules.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Concrete five-slot frame rows for every literal eight-block zero-core
action.  The degree and zero-core equations are retained because they are
the hypotheses used to construct the row from the actual block frame. -/
abbrev DegreeFourZeroCoreEightFrameBoundsInput :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    Nat.card block.Points = 8 →
    DegreeFourZeroCoreFiniteFrameBounds block P 5

/-- Concrete ten-slot frame rows for every literal sixteen-block zero-core
action. -/
abbrev DegreeFourZeroCoreSixteenFrameBoundsInput :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    Nat.card block.Points = 16 →
    DegreeFourZeroCoreFiniteFrameBounds block P 10

/-- The common five-slot noncentral-socle bridge at eight blocks. -/
abbrev DegreeFourZeroCoreEightBridgeInput :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    DegreeFourZeroCoreFixedFrameNoncentralSocleBridge block P 8 5

/-- The common ten-slot noncentral-socle bridge at sixteen blocks. -/
abbrev DegreeFourZeroCoreSixteenBridgeInput :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    DegreeFourZeroCoreFixedFrameNoncentralSocleBridge block P 16 10

/-- Assemble the zero-core callback required by the complete degree-four
dispatcher.  Large and odd-divisor block counts are consumed first by the
proved zero-core capacity exhaustion.  The only remaining cases are sent to
the impossible two-block theorem or to the literal finite-frame source. -/
noncomputable def degreeFourZeroCoreResidualSource_of_finiteFrames
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (degreeSixteenOwner : ∀ V : PreE7NonPairActionClass 16,
      PreE7RankTailSourceOrYonedaTopData 16 V)
    (bridge8 : DegreeFourZeroCoreEightBridgeInput)
    (bridge16 : DegreeFourZeroCoreSixteenBridgeInput)
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
        · exact ⟨degreeFourZeroCoreFiniteResidueSource block P hZmud lit
            degreeSixteenOwner (bridge8 block P) (bridge16 block P)
            hr hD (frames8 block P hr hD) (frames16 block P hr hD)
            (Or.inl hs4)⟩
        · exact ⟨degreeFourZeroCoreFiniteResidueSource block P hZmud lit
            degreeSixteenOwner (bridge8 block P) (bridge16 block P)
            hr hD (frames8 block P hr hD) (frames16 block P hr hD)
            (Or.inr (Or.inl hs8))⟩
        · exact ⟨degreeFourZeroCoreFiniteResidueSource block P hZmud lit
            degreeSixteenOwner (bridge8 block P) (bridge16 block P)
            hr hD (frames8 block P hr hD) (frames16 block P hr hD)
            (Or.inr (Or.inr hs16))⟩)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
