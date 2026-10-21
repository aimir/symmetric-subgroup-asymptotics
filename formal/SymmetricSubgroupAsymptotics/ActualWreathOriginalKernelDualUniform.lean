import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Uniform generation of the actual correlated elementary kernel, before
choosing any normal denominator. The original orbit-evaluation inclusion
is dualized to a surjection; the actual quotient action is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (C : ElementaryMinimalNormalChart phi.ker)

/-- A uniform bound on the induced dual descends to the exact correlated
kernel, and then from its inflation to the SAME actual quotient group. -/
theorem originalKernel_dual_uniform
    (i : I) (D : RefinedCapacityData S phi C i) :
    UniformSubrepresentationGeneratorBound
      (E S phi C).quotientRepresentation.ρ.dual D.H := by
  let inc := inducedIntertwiner S phi C i
  let d := RepresentationHeadExact.dualMap inc
  have hd : Function.Surjective d :=
    LinearMap.dualMap_surjective_of_injective
      (inducedIntertwiner_injective S phi C i)
  have hu : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual D.H :=
    D.dual.of_surjective d hd
  change UniformSubrepresentationGeneratorBound
    (Representation.dual ((E S phi C).quotientRepresentation.ρ.comp
      (QuotientGroup.mk' (K S phi)))) D.H at hu
  rw [representation_dual_comp] at hu
  exact UniformSubrepresentationGeneratorBound.of_comp
    (E S phi C).quotientRepresentation.ρ.dual
    (QuotientGroup.mk' (K S phi)) hu

end SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
