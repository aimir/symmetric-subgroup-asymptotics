import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationCoordinateLinearAction

/-!
# Full coordinate transport on the literal translation submodule

The quotient representation on the correlated affine translation layer is
monomial in the original block coordinates.  This is the unrestricted
version of the diagonal formula: an ambient lift transports coordinate `i`
to its actual block-top image and applies the corresponding invertible local
linear map to the value at `i`.

Keeping the formula on the literal `TranslationSubmodule` is useful in the
four-distinct-sign branch.  It lets a nonzero vector in an invariant
subrepresentation be moved to every block before the diagonal character
projectors are applied.
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

/-- The exact monomial coordinate formula for an arbitrary ambient lift.
The diagonal theorem is the special case in which the displayed block-top
image equals `i`. -/
theorem translationSubmodule_quotientRepresentation_coordinate_transport
    (a : preE7NonPairAction w U)
    (v : TranslationSubmodule block P) (i : block.Points) :
    (((elementaryChart block P).quotientRepresentation.ρ
      (QuotientGroup.mk' (E block P) a) v).1
        ((ambientEmbedding block a).right • i)) =
      (binaryAffineLocalLinearRepresentation block P).ρ
        (localMap block P
          ((ambientEmbedding block a).left
            ((ambientEmbedding block a).right • i)))
        (v.1 i) := by
  let e : E block P :=
    ((translationAddEquiv block P).symm v).toMul
  have hev : ((elementaryChart block P).equiv e).toAdd = v :=
    (translationAddEquiv block P).apply_symm_apply v
  have hrep := (elementaryChart block P).quotientRepresentation_apply a e
  rw [hev] at hrep
  have hcoordinate := congrArg
    (fun x : TranslationSubmodule block P =>
      x.1 ((ambientEmbedding block a).right • i)) hrep
  have hlinear := translationCoordinate_conjugation_linear block P a e i
  have hvi : (coordinate block P i e).toAdd = v.1 i := by
    have := congrArg (fun x : TranslationSubmodule block P => x.1 i) hev
    exact this
  calc
    (((elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) a) v).1
          ((ambientEmbedding block a).right • i)) =
        (coordinate block P
          ((ambientEmbedding block a).right • i)
          (MulAut.conjNormal a e)).toAdd := hcoordinate
    _ = (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P
            ((ambientEmbedding block a).left
              ((ambientEmbedding block a).right • i)))
          (coordinate block P i e).toAdd := hlinear
    _ = (binaryAffineLocalLinearRepresentation block P).ρ
          (localMap block P
            ((ambientEmbedding block a).left
              ((ambientEmbedding block a).right • i)))
          (v.1 i) := by rw [hvi]

/-- Nonzero coordinate values remain nonzero after literal block transport.
This is the only consequence of the local factor needed for irreducibility. -/
theorem translationSubmodule_coordinate_ne_zero_of_transport
    (a : preE7NonPairAction w U)
    (v : TranslationSubmodule block P) (i : block.Points)
    (hvi : v.1 i ≠ 0) :
    (((elementaryChart block P).quotientRepresentation.ρ
      (QuotientGroup.mk' (E block P) a) v).1
        ((ambientEmbedding block a).right • i)) ≠ 0 := by
  rw [translationSubmodule_quotientRepresentation_coordinate_transport
    block P a v i]
  intro hzero
  apply hvi
  apply ((binaryAffineLocalLinearRepresentation block P).ρ.apply_bijective
    (localMap block P
      ((ambientEmbedding block a).left
        ((ambientEmbedding block a).right • i)))).1
  simpa only [map_zero] using hzero

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
