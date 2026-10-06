import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleCoordinateTransport

/-!
# Embedding the correlated translation module in the full affine frame

The finite eight-block calculation is performed on the full sixteen
dimensional induced frame.  The actual translation layer can be correlated,
so it is only an invariant submodule of that frame.  This file constructs
the literal equivariant injection used by the finite importer.
-/

set_option autoImplicit false
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

/-- The full coordinate frame attached to the literal quotient wreath
embedding.  In degree four with eight blocks its dimension is sixteen. -/
def fullTranslationFrameRepresentation :
    Representation (ZMod P.p)
      (DegreeFourComplementQuotient block P)
  (block.Points → (chart block P).V) :=
  (PermutationalWreathProduct.functionRepresentation
      (binaryAffineLocalLinearRepresentation block P).ρ).comp
    (quotientEmbedding block P)

/-- The actual correlated translation representation embeds in the full
coordinate frame by its literal coordinate inclusion. -/
def translationSubmoduleFullFrameEmbedding :
    (show Representation (ZMod P.p)
        (DegreeFourComplementQuotient block P)
        (TranslationSubmodule block P) from
      (elementaryChart block P).quotientRepresentation.ρ).IntertwiningMap
      (fullTranslationFrameRepresentation block P) where
  toLinearMap := (TranslationSubmodule block P).subtype
  isIntertwining' := by
    intro q
    apply LinearMap.ext
    intro v
    funext j
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (E block P) q
    let i : block.Points := (ambientEmbedding block a).right⁻¹ • j
    have hij : (ambientEmbedding block a).right • i = j := by
      simp only [i, smul_inv_smul]
    have h := translationSubmodule_quotientRepresentation_coordinate_transport
      block P a v i
    change (((elementaryChart block P).quotientRepresentation.ρ
      (QuotientGroup.mk' (E block P) a) v).1 j) =
        (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P ((ambientEmbedding block a).left j))
          (v.1 ((ambientEmbedding block a).right⁻¹ • j))
    simpa only [i, hij] using h

theorem translationSubmoduleFullFrameEmbedding_injective :
    Function.Injective (translationSubmoduleFullFrameEmbedding block P) :=
  (TranslationSubmodule block P).subtype_injective

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
