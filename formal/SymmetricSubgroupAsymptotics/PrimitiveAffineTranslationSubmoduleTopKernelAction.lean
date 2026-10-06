import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleDiagonalAction

/-!
# Top-kernel action on the literal translation submodule

Descend the ambient coordinate formula to the actual quotient `U / E`.
An element in the kernel of the block top has a diagonal action on the
correlated translation submodule, with its `i`-th scalar supplied by the
`i`-th local component of the literal quotient wreath embedding.
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

/-- The descended quotient representation is diagonal on every element of
the literal block-top kernel. -/
theorem translationSubmodule_quotientRepresentation_coordinate_of_top_eq_one
    (q : preE7NonPairAction w U ⧸ E block P)
    (hq : (quotientEmbedding block P q).right = 1)
    (v : TranslationSubmodule block P) (i : block.Points) :
    (((elementaryChart block P).quotientRepresentation.ρ q v).1 i) =
      (binaryAffineLocalLinearRepresentation block P).ρ
        ((quotientEmbedding block P q).left i) (v.1 i) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (E block P) q
  have ha : (ambientEmbedding block a).right = 1 := by
    change (ambientEmbedding block a).right = 1 at hq
    exact hq
  simpa only [quotientEmbedding] using
    translationSubmodule_quotientRepresentation_coordinate
      block P a ha v i

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
