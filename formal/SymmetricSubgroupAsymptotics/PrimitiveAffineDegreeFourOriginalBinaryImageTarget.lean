import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinarySectionCoordinates
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! Put the original target epi on the literal coordinate image L.
This is the invariant L to which the concrete bottom/middle/augmentation
case split applies. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalBinaryImageTarget_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

local instance originalBinaryImageTarget_module {M : Type} [AddCommGroup M]
    [Module (ZMod P.p) M] : Module (ZMod (elementaryChart block P).p) M := by
  change Module (ZMod P.p) M
  infer_instance

def originalBinaryImageTargetMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    {M : Type} [AddCommGroup M] [Module (ZMod P.p) M]
    (rho : Representation (ZMod P.p) (preE7NonPairAction w U) M)
    (i : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap rho)
    (hi : Function.Injective i) :
    i.range.toRepresentation.IntertwiningMap
      ((DegreeFourFullBinaryTargetSection block P N).toRepresentation.comp
        (degreeFourFullBinarySocleTopMap block P N)) := by
  let q := RepresentationHeadExact.rangeProjection i
  have hq : Function.Bijective q := by
    constructor
    · intro x y h
      exact hi (congrArg Subtype.val h)
    · exact RepresentationHeadExact.rangeProjection_surjective i
  exact (degreeFourFullBinaryTranslationSectionIntertwiner block P N).comp
    (q.ofBijective hq).symm.toIntertwiningMap

theorem originalBinaryImageTargetMap_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    {M : Type} [AddCommGroup M] [Module (ZMod P.p) M]
    (rho : Representation (ZMod P.p) (preE7NonPairAction w U) M)
    (i : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap rho)
    (hi : Function.Injective i) :
    Function.Surjective (originalBinaryImageTargetMap block P N rho i hi) := by
  let q := RepresentationHeadExact.rangeProjection i
  have hq : Function.Bijective q := by
    constructor
    · intro x y h
      exact hi (congrArg Subtype.val h)
    · exact RepresentationHeadExact.rangeProjection_surjective i
  let e := q.ofBijective hq
  change Function.Surjective (fun x =>
    degreeFourFullBinaryTranslationSectionIntertwiner block P N (e.symm.toLinearEquiv x))
  exact (originalBinarySectionCoordinates_target_surjective block P N).comp
    e.symm.toLinearEquiv.surjective

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
