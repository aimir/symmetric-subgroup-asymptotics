import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction
import SymmetricSubgroupAsymptotics.RepresentationDualComp

/-! The actual ORIGINAL six-pair kernel and every original quotient
section inherit a dual-generator bound from the proved natural module
bound of the SAME six-point top. No coarse D8 model is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairOriginalBinaryDualSections
open OriginalKernelModuleChart
variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

 theorem dual_generated {H : ℕ}
    (hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) H)
    (N : Subgroup U) [N.Normal] :
    RepresentationGeneratedBy
      ((SixPairPrimitiveAllNormalB6.originalKernelChart F).sectionRepresentation
        F.top.rangeRestrict (SixPairPrimitiveAllNormalB6.kernelModule F) N).ρ.dual H := by
  let pi := F.top.rangeRestrict
  let A := SixPairPrimitiveAllNormalB6.kernelModule F
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  let rho := permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)
  let i : A.ρ.IntertwiningMap rho :=
    { toLinearMap := F.kernelSpace.subtype,isIntertwining' _ := rfl }
  have hi : Function.Injective i := fun _ _ h => Subtype.ext h
  have hu' : UniformSubrepresentationGeneratorBound rho.dual H :=
    permutationFunctionRepresentation_dual_uniform hu
  let sigma : Representation (ZMod 2) F.top.range (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp
    (sectionTop pi N F.top.rangeRestrict_surjective)
  have hg : RepresentationGeneratedBy (Representation.dual sigma) H :=
    representationDual_generated_of_subquotient hu' i hi
      (E.sectionProjectionOnBase pi A N F.top.rangeRestrict_surjective)
      (E.sectionProjectionOnBase_surjective pi A N F.top.rangeRestrict_surjective)
  apply RepresentationGeneratedBy.of_comp (E.sectionRepresentation pi A N).ρ.dual
    (sectionTop pi N F.top.rangeRestrict_surjective)
  change RepresentationGeneratedBy (Representation.dual
    ((E.sectionRepresentation pi A N).ρ.comp
      (sectionTop pi N F.top.rangeRestrict_surjective))) H at hg
  rw [representation_dual_comp] at hg
  exact hg

end SymmetricSubgroupAsymptotics.SixPairOriginalBinaryDualSections
