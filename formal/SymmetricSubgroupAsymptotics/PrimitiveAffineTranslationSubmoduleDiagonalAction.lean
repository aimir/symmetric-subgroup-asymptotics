import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationCoordinateLinearAction

/-!
# Diagonal action on the correlated translation submodule

When an ambient element fixes every original block, its quotient action on
the bundled correlated translation submodule is coordinatewise.  The scalar
on a coordinate is the exact compressed local-complement representation at
that block.

The statement remains on the actual `TranslationSubmodule`; it neither
replaces the subgroup by a direct product nor chooses independent local
translations.
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

/-- The literal quotient representation is diagonal on coordinates for an
ambient element whose block-top permutation is trivial. -/
theorem translationSubmodule_quotientRepresentation_coordinate
    (a : preE7NonPairAction w U)
    (ha : (ambientEmbedding block a).right = 1)
    (v : TranslationSubmodule block P) (i : block.Points) :
    (((elementaryChart block P).quotientRepresentation.ρ
      (QuotientGroup.mk' (E block P) a) v).1 i) =
        (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P ((ambientEmbedding block a).left i))
          (v.1 i) := by
  let e : E block P :=
    ((translationAddEquiv block P).symm v).toMul
  have hev : ((elementaryChart block P).equiv e).toAdd = v := by
    exact (translationAddEquiv block P).apply_symm_apply v
  have hrep := (elementaryChart block P).quotientRepresentation_apply a e
  rw [hev] at hrep
  have hcoordinate := congrArg
    (fun x : TranslationSubmodule block P => x.1 i) hrep
  have hfix : (ambientEmbedding block a).right • i = i := by
    rw [ha]
    exact one_smul _ _
  have hlinear := translationCoordinate_conjugation_linear_of_fixed
    block P a e i hfix
  have hvi : (coordinate block P i e).toAdd = v.1 i := by
    have := congrArg (fun x : TranslationSubmodule block P => x.1 i) hev
    exact this
  calc
    (((elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) a) v).1 i) =
        (coordinate block P i (MulAut.conjNormal a e)).toAdd := hcoordinate
    _ = (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P ((ambientEmbedding block a).left i))
          (coordinate block P i e).toAdd := hlinear
    _ = (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P ((ambientEmbedding block a).left i))
          (v.1 i) := by rw [hvi]

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
