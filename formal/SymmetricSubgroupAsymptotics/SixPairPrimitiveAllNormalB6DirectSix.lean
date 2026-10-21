import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.PrimitiveSixOriginalQuotientDichotomyDirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6.DirectSix
open Non2UnipotentPrefixFiniteMenu

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

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
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
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
    exact PrimitiveSixOriginalQuotientDichotomy.DirectSix.quotientCertificate
      hindex F.top.rangeRestrict F.top.rangeRestrict_surjective (kernelModule F)
      (originalKernelChart F) (kernel_uniform F hu) hZmud N.1


end SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6.DirectSix
