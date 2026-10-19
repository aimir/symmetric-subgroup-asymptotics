import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.OriginalKernelTargetEquivTransport
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads

/-! A physical six-pair frame with its actual A4 edge image yields the
literal original kernel chart and an injective edge-coordinate map.
No primitive action or split extension is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameKernel
open AlternatingEdgeOriginalProjectorHeads (Top beta)

variable {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (e : Top ≃* F.top.range)
    (he : ∀ p : Top, (e p).val=SymmetricFourTwelvePointSocles.edge p.val)

def top : U →* Top := e.symm.toMonoidHom.comp F.top.rangeRestrict

theorem top_surjective : Function.Surjective (top F e) :=
  e.symm.surjective.comp F.top.rangeRestrict_surjective

def kernelModule : Rep (ZMod 2) Top :=
  OriginalKernelModuleChart.targetRep (SixPairPrimitiveAllNormalB6.kernelModule F) e.symm

def originalKernelChart : OriginalKernelModuleChart (top F e) (kernelModule F e) :=
  OriginalKernelModuleChart.ofTargetEquiv F.top.rangeRestrict
    (SixPairPrimitiveAllNormalB6.kernelModule F)
    (SixPairPrimitiveAllNormalB6.originalKernelChart F) e.symm

include he in
def inclusion : Representation.IntertwiningMap (kernelModule F e).ρ beta where
  toLinearMap := F.kernelSpace.subtype
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    change (fun i => v.val ((e p).val⁻¹ i)) =
      (fun i => v.val ((SymmetricFourTwelvePointSocles.edge p.val)⁻¹ i))
    rw [he]

include he in
theorem inclusion_injective : Function.Injective (inclusion F e he) :=
  fun _ _ h => Subtype.ext h

end SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameKernel
