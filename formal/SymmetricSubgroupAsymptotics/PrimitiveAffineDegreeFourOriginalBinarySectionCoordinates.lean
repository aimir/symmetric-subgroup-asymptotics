import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalTranslationCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFullBinarySection

/-! The literal source L of the original binary-socle intersection map
in the actual canonical eight-coordinate action, inflated to the unchanged
original group. The target map is the already constructed original epi. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalBinarySectionCoordinates_localFact1 : Fact P.p.Prime := (chart block P).primeFact

local instance binarySectionCoordinates_coordinateModule :
    Module (ZMod (elementaryChart block P).p) (Fin 8 → ZMod P.p) := by
  change Module (ZMod P.p) (Fin 8 → ZMod P.p)
  infer_instance

namespace DegreeFourA4OriginalPointChart

variable (C : DegreeFourA4OriginalPointChart block)

def binarySectionCoordinates
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap
      ((BinaryFourOriginalScalarCharts.a4Frame (degreeFour_profilePrime_eq_two block P hr)
        ((groupEquiv (block := block) (P := P) (C := C) hr hD))).comp (QuotientGroup.mk' (E block P))) where
  toLinearMap := ((translationCoordinates (block := block) (P := P) (C := C) hr hD)).toLinearMap.comp
    (DegreeFourFullBinarySourceSection block P N).toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact Representation.IntertwiningMap.isIntertwining _ _
      ((translationCoordinates (block := block) (P := P) (C := C) hr hD)) (QuotientGroup.mk' (E block P) g) x.1

theorem binarySectionCoordinates_injective
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Injective ((binarySectionCoordinates (block := block) (P := P) (C := C) hr hD) N) :=
  ((translationCoordinates_injective (block := block) (P := P) (C := C) hr hD)).comp Subtype.val_injective

end DegreeFourA4OriginalPointChart

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)

def binarySectionCoordinates
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap
      ((BinaryFourOriginalScalarCharts.s4Frame (degreeFour_profilePrime_eq_two block P hr)
        ((groupEquiv (block := block) (P := P) (C := C) hr hD))).comp (QuotientGroup.mk' (E block P))) where
  toLinearMap := ((translationCoordinates (block := block) (P := P) (C := C) hr hD)).toLinearMap.comp
    (DegreeFourFullBinarySourceSection block P N).toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact Representation.IntertwiningMap.isIntertwining _ _
      ((translationCoordinates (block := block) (P := P) (C := C) hr hD)) (QuotientGroup.mk' (E block P) g) x.1

theorem binarySectionCoordinates_injective
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Injective ((binarySectionCoordinates (block := block) (P := P) (C := C) hr hD) N) :=
  ((translationCoordinates_injective (block := block) (P := P) (C := C) hr hD)).comp Subtype.val_injective

end DegreeFourS4OriginalPointChart

/-- The existing original target map remains the onto map in these
coordinates. It is not replaced by an abstract quotient of the same size. -/
theorem originalBinarySectionCoordinates_target_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective (degreeFourFullBinaryTranslationSectionIntertwiner block P N) :=
  degreeFourFullBinaryTranslationSectionLinearMap_surjective block P N

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
