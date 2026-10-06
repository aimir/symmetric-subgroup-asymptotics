import SymmetricSubgroupAsymptotics.PrimitiveAffineLocalKernelConjugation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTranslationCoordinates

/-!
# Linear conjugation on a literal translation coordinate

Combine the actual wreath-coordinate conjugation identity with the local
affine-kernel chart.  The result keeps the transported block coordinate and
the exact local-complement element; no product translation kernel is
introduced.
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

/-- Ambient conjugation transports one translation coordinate and acts on
its value through the literal compressed local representation. -/
theorem translationCoordinate_conjugation_linear
    (a : preE7NonPairAction w U) (e : E block P) (i : block.Points) :
    (coordinate block P
      ((ambientEmbedding block a).right • i)
      (MulAut.conjNormal a e)).toAdd =
        (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P
            ((ambientEmbedding block a).left
              ((ambientEmbedding block a).right • i)))
          (coordinate block P i e).toAdd := by
  have hraw := rawTranslationCoordinate_conjugation block P a e i
  change ((localKernelEquiv block P).symm
      (PermutationalWreathProduct.Compression.kernelCoordinate
        (ambientEmbedding block) (localMap block P)
        ((ambientEmbedding block a).right • i)
        (MulAut.conjNormal a e))).toAdd = _
  rw [hraw]
  exact localKernelEquiv_conjugation block P
    ((ambientEmbedding block a).left
      ((ambientEmbedding block a).right • i))
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (ambientEmbedding block) (localMap block P) i e)

/-- On a block fixed by the quotient top, the same identity is diagonal on
that original coordinate. -/
theorem translationCoordinate_conjugation_linear_of_fixed
    (a : preE7NonPairAction w U) (e : E block P) (i : block.Points)
    (hi : (ambientEmbedding block a).right • i = i) :
    (coordinate block P i (MulAut.conjNormal a e)).toAdd =
      (binaryAffineLocalLinearRepresentation block P).ρ
        (localMap block P ((ambientEmbedding block a).left i))
        (coordinate block P i e).toAdd := by
  simpa only [hi] using
    translationCoordinate_conjugation_linear block P a e i

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
