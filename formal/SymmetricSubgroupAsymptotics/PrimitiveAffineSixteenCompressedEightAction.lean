import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixteenCoordinateAction
import SymmetricSubgroupAsymptotics.GeneralFourTwoAlternatingEquiv

/-! Replace the fifteen nonzero-translation points per local affine16
component by the proved faithful eight-point GL4(2) action. The compressed
group is the original quotient by its actual correlated translation kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

namespace PermutationalWreathProduct

theorem mapBase_injective_of_injective
    {D D' Q I : Type} [Group D] [Group D'] [Group Q] [MulAction Q I]
    (f : D →* D') (hf : Function.Injective f) :
    Function.Injective (mapBase (Q := Q) (I := I) f) := by
  intro a b hab
  apply PermutationalWreathProduct.ext
  · funext i
    exact hf (congrArg (fun z : PermutationalWreathProduct D' Q I => z.left i) hab)
  · exact congrArg (fun z : PermutationalWreathProduct D' Q I => z.right) hab

end PermutationalWreathProduct

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre=16)

include hr in
/-- The actual local compressed group is the actual point stabilizer,
represented faithfully through GL4(2) on eight points. -/
def localSixteenEightMap : LocalQuotient block P →* Equiv.Perm (Fin 8) :=
  let e := MonoidHom.ofInjective (f := complementAction block P)
    (complementAction_injective block P)
  (GeneralFourTwoAlternatingEquiv.eightAction.comp
    (P.complementLinearMap_degreeSixteen block.component_preprimitive
      (origin block) hr)).comp e.symm.toMonoidHom

theorem localSixteenEightMap_injective :
    Function.Injective (localSixteenEightMap block P hr) :=
  (GeneralFourTwoAlternatingEquiv.eightAction_injective.comp
    (P.complementLinearMap_degreeSixteen_injective block.component_preprimitive
      (origin block) hr)).comp
    (MonoidHom.ofInjective (f := complementAction block P)
      (complementAction_injective block P)).symm.injective

include hr in
/-- Faithful8s action of the SAME quotient, retaining every local coordinate
and the original block permutation. -/
def quotientSixteenEightAction :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin (8*Fintype.card block.Points)) :=
  (PermutationalWreathProduct.toFintypePerm
    (u := 8) (Equiv.Perm (Fin 8)) block.Top block.Points).comp
      ((PermutationalWreathProduct.mapBase (localSixteenEightMap block P hr)).comp
        (quotientEmbedding block P))

theorem quotientSixteenEightAction_injective :
    Function.Injective (quotientSixteenEightAction block P hr) :=
  (PermutationalWreathProduct.toFintypePerm_injective
    (u := 8) (Equiv.Perm (Fin 8)) block.Top block.Points).comp
      ((PermutationalWreathProduct.mapBase_injective_of_injective
        (localSixteenEightMap block P hr)
        (localSixteenEightMap_injective block P hr)).comp
          (quotientEmbedding_injective block P))

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
