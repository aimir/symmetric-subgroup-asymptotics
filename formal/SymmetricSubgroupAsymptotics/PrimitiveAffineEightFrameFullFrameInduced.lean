import SymmetricSubgroupAsymptotics.PermutationalWreathFunctionCoinduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal

/-!
# The literal affine frame in induced coordinates

The emitted eight-frame certificates use a right-coset induced basis.  This
file places the actual full translation frame in exactly that model.  The
remaining row-specific check is therefore only the finite comparison of two
induced bases (the actual point chart and the emitted coset/binary basis).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime :=
  (chart block P).primeFact

/-- The exact point stabilizer used by the induced full-frame model. -/
abbrev fullFrameInducedStabilizer (i : block.Points) :
    Subgroup (DegreeFourComplementQuotient block P) :=
  PermutationalWreathProduct.FunctionCoinduced.stabilizer
    (quotientEmbedding block P) i

/-- The exact local representation used by the induced full-frame model. -/
abbrev fullFrameInducedLocalRepresentation (i : block.Points) :
    Representation (ZMod P.p) (fullFrameInducedStabilizer block P i)
      (chart block P).V :=
  PermutationalWreathProduct.FunctionCoinduced.localRepresentation
    (quotientEmbedding block P)
    (binaryAffineLocalLinearRepresentation block P).ρ i

/-- Canonical injection from the full literal frame into the induced model
at one actual block. -/
def fullTranslationFrameToInduced (i : block.Points) :
    (fullTranslationFrameRepresentation block P).IntertwiningMap
      (Representation.ind (fullFrameInducedStabilizer block P i).subtype
        (fullFrameInducedLocalRepresentation block P i)) :=
  PermutationalWreathProduct.FunctionCoinduced.toInduced
    (quotientEmbedding block P)
    (binaryAffineLocalLinearRepresentation block P).ρ i

/-- The actual top is transitive and the quotient embedding has full top
projection, so the canonical induced-coordinate map is injective. -/
theorem fullTranslationFrameToInduced_injective (i : block.Points) :
    Function.Injective (fullTranslationFrameToInduced block P i) := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  exact PermutationalWreathProduct.FunctionCoinduced.toInduced_injective
    (quotientEmbedding block P)
    (binaryAffineLocalLinearRepresentation block P).ρ i
    (binaryAffineQuotientTopMap_surjective block P)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
