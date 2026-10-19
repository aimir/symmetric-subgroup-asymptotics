import SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameKernel
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Actual physical edge-pair frames consume the shared original quotient
socle theorem and retain their checked original natural-module bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameJointData
open AlternatingEdgeOriginalProjectorHeads (Top)
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (e : Top ≃* F.top.range)
    (he : ∀ p : Top, (e p).val=SymmetricFourTwelvePointSocles.edge p.val)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 :=
  AlternatingEdgeOriginalQuotientSocles.quotientSocle
    (AlternatingEdgePairFrameKernel.top F e)
    (AlternatingEdgePairFrameKernel.top_surjective F e)
    (AlternatingEdgePairFrameKernel.kernelModule F e)
    (AlternatingEdgePairFrameKernel.originalKernelChart F e)
    (AlternatingEdgePairFrameKernel.inclusion F e he)
    (AlternatingEdgePairFrameKernel.inclusion_injective F e he) N

def jointData (C : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame C.top (Fin 6)) (e : Top ≃* F.top.range)
    (he : ∀ p : Top, (e p).val=SymmetricFourTwelvePointSocles.edge p.val)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) C.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData C 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    C.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle F e he N.1)
  natural := hnatural

end SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameJointData
