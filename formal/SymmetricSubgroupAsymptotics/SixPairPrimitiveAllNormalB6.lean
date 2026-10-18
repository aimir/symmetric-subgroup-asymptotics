import SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomy
import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.BinaryPairUniformQuotientSocles

/-! Primitive six-pair B6 source on the physical original twelve-point
action. Actual kernel bits give the module chart, and the original normal
quotient dichotomy supplies one general character or a small binary target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
open Non2UnipotentPrefixFiniteMenu

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

def kernelModule : Rep (ZMod 2) F.top.range :=
  Rep.of F.kernelTopPermutationSubrepresentation.toRepresentation

private def rangeKernelEquiv : F.top.rangeRestrict.ker ≃* F.top.ker :=
  MulEquiv.subgroupCongr (by
    ext u
    change F.top.rangeRestrict u=1 ↔ F.top u=1
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h)

/-- Exact original correlated kernel, not the full six-dimensional flip
space. Conjugation is the physical permutation of its coordinates. -/
def originalKernelChart : OriginalKernelModuleChart F.top.rangeRestrict (kernelModule F) where
  equiv := F.kernelChart.symm.trans (rangeKernelEquiv F).symm
  conjugate u v := by
    let k : F.top.ker := F.kernelChart.symm (Multiplicative.ofAdd v)
    have hk : F.bits k=v.val :=
      congrArg (fun z : F.kernelSpace => (z : Fin 6 → ZMod 2))
        (congrArg Multiplicative.toAdd (F.kernelChart.apply_symm_apply (Multiplicative.ofAdd v)))
    have he : F.kernelChart (MulAut.conjNormal u k)=
        Multiplicative.ofAdd ((kernelModule F).ρ (F.top.rangeRestrict u) v) := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      change F.bits (MulAut.conjNormal u k) i=v.val ((F.top u)⁻¹ i)
      rw [F.bits_conjNormal,hk]
    have hg : F.kernelChart.symm
        (Multiplicative.ofAdd ((kernelModule F).ρ (F.top.rangeRestrict u) v))=
          MulAut.conjNormal u k := by
      apply F.kernelChart.injective
      rw [F.kernelChart.apply_symm_apply]
      exact he.symm
    change ((F.kernelChart.symm
        (Multiplicative.ofAdd ((kernelModule F).ρ (F.top.rangeRestrict u) v)) : F.top.ker) : U)=
      u * ((F.kernelChart.symm (Multiplicative.ofAdd v) : F.top.ker) : U) * u⁻¹
    exact congrArg Subtype.val hg

private theorem kernel_uniform
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1) :
    UniformSubrepresentationGeneratorBound (kernelModule F).ρ 1 := by
  let j : Representation.IntertwiningMap (kernelModule F).ρ
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) :=
    { toLinearMap := F.kernelSpace.subtype, isIntertwining' _ := rfl }
  exact hu.of_injective j (fun _ _ h => Subtype.ext h)

/-- No finite normal menu or per-normal source bound is an input. -/
def actionCertificate [MulAction.IsPreprimitive F.top.range (Fin 6)]
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1) :
    PreE7B6ActionCertificate U where
  blockChart := sixPairBlockChart F
  preserves := sixPairBlockChart_preserves F
  quotient N := by
    letI := N.2
    letI : Finite (kernelModule F) := by
      change Finite F.kernelSpace
      infer_instance
    letI : FiniteDimensional (ZMod 2) (kernelModule F) := by
      change FiniteDimensional (ZMod 2) F.kernelSpace
      infer_instance
    exact PrimitiveSixOriginalQuotientDichotomy.quotientCertificate
      h6 F.top.rangeRestrict F.top.rangeRestrict_surjective (kernelModule F)
      (originalKernelChart F) (kernel_uniform F hu) hZmud N.1

end SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
