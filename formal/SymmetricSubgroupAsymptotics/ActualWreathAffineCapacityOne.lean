import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity

/-!
# Capacity one from a cyclic ambient contragredient

For an actual wreath-compression state, every literal normal section is a
quotient of the correlated elementary kernel.  If every subrepresentation
of the inflated ambient contragredient is cyclic, dualizing that literal
quotient gives a cyclic section contragredient.  This file packages that
argument while retaining the fixed-top coefficient of an already
constructed joint capacity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace ActualWreathAffineCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

variable (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

/-- A cyclic ambient dual makes every inflated literal normal section
cyclic. -/
theorem inflatedSectionDual_generated_one_of_ambientDual_uniform
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual 1)
    (N : Subgroup S.A) [N.Normal] :
    RepresentationGeneratedBy
      (inflatedSectionRepresentation S phi C N).dual 1 := by
  let identity :
      (ambientRepresentation S phi C).IntertwiningMap
        (ambientRepresentation S phi C) :=
    { toLinearMap := LinearMap.id
      isIntertwining' := fun _ => rfl }
  exact representationDual_generated_of_subquotient huniform
    identity Function.injective_id
    (sectionQuotientIntertwiner S phi C N)
    (sectionQuotientIntertwiner_surjective S phi C N)

/-- Sharpen an actual-wreath joint capacity to one from a uniform cyclicity
theorem for the ambient contragredient.  The existing fixed-top coefficient
is retained exactly. -/
noncomputable def jointCapacitySharpenToOne_of_ambientDual_uniform
    (H : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual 1) :
    ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  capacity := 1
  capacity_nonneg := by norm_num
  section_capacity := by
    intro N
    letI : N.1.Normal := N.2
    letI : FiniteDimensional (ZMod C.p)
        (PermutationalWreathProduct.Compression.ElementarySubmodule
          (p := C.p) S.rho phi C.equiv.symm) := inferInstance
    letI : FiniteDimensional (ZMod (E S phi C).p) (E S phi C).V :=
      (E S phi C).finiteDimensional
    letI : FiniteDimensional (ZMod (E S phi C).p)
        ((originalChart S phi C).sectionRepresentation
          (pi S phi) (E S phi C).quotientRepresentation N.1) := by
      change FiniteDimensional (ZMod (E S phi C).p)
        ((E S phi C).V ⧸
          (originalChart S phi C).normalSpace
            (pi S phi) (E S phi C).quotientRepresentation N.1)
      infer_instance
    have hgen : RepresentationGeneratedBy
        (inflatedSectionRepresentation S phi C N.1).dual 1 :=
      inflatedSectionDual_generated_one_of_ambientDual_uniform
        S phi C huniform N.1
    have hinflated : representationSchurCapacity
        (inflatedSectionRepresentation S phi C N.1) ≤ 1 :=
      by
        simpa using representationSchurCapacity_le_of_dual_generated
          (inflatedSectionRepresentation S phi C N.1) 1 hgen
    have heq := representationSchurCapacity_comp
      (QuotientGroup.mk' ((pi S phi).ker ⊔ N.1))
      (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N.1))
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N.1).ρ
    rw [← heq]
    exact hinflated
  coefficient := H.coefficient
  coefficient_nonneg := H.coefficient_nonneg
  fixed_top_fibre := H.fixed_top_fibre

@[simp] theorem jointCapacitySharpenToOne_of_ambientDual_uniform_capacity
    (H : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual 1) :
    (jointCapacitySharpenToOne_of_ambientDual_uniform
      S phi C H huniform).capacity = 1 := rfl

@[simp] theorem jointCapacitySharpenToOne_of_ambientDual_uniform_coefficient
    (H : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual 1) :
    (jointCapacitySharpenToOne_of_ambientDual_uniform
      S phi C H huniform).coefficient = H.coefficient := rfl

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
