import SymmetricSubgroupAsymptotics.BinaryFourOriginalSourceAmbientStability
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalBottomAugmentationMaps

/-! The literal-L bottom case embeds in the same middle active support
as the proper-nonbottom quotient source. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

variable {G : Type} [Group G] (gamma : G →* SymmetricComplement)
    (L : Subrepresentation (canonicalFull.comp gamma))
    (hbottom : ∀ x : L.toSubmodule, ∃ a : Local, fullChart x.1 = diagonal a)

def originalBottomEnvelopeMap : L.toRepresentation.IntertwiningMap
    (symmetricEnvelopeRepresentation.comp gamma) where
  toLinearMap := localMiddleInclusionLinear.comp
    (bottomProjectionLinear.comp L.toSubmodule.subtype)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change localMiddleInclusionLinear (bottomProjectionLinear (canonicalFull (gamma g) x.1)) =
      symmetricEnvelopeRepresentation (gamma g) (localMiddleInclusionLinear (bottomProjectionLinear x.1))
    rw [bottomProjection_action (gamma g) x.1 (hbottom x)]
    exact Representation.IntertwiningMap.isIntertwining _ _ canonicalLocalMiddleInclusion
      (gamma g) (bottomProjectionLinear x.1)

theorem originalBottomEnvelopeMap_injective :
    Function.Injective (originalBottomEnvelopeMap gamma L hbottom) := by
  intro x y h
  have hp : bottomProjectionLinear x.1 = bottomProjectionLinear y.1 :=
    canonicalLocalMiddleInclusion_injective h
  apply Subtype.ext
  calc
    x.1 = bottomCoordinatesLinear (bottomProjectionLinear x.1) :=
      (bottom_coordinates_of_diagonal x.1 (hbottom x)).symm
    _ = bottomCoordinatesLinear (bottomProjectionLinear y.1) := congrArg bottomCoordinatesLinear hp
    _ = y.1 := bottom_coordinates_of_diagonal y.1 (hbottom y)

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
