import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacityOne

/-!
# Sharpening an actual-wreath capacity from a uniform ambient bound

The capacity-one construction is useful more generally: a uniform
`H`-generator theorem for the ambient contragredient gives capacity `H`
for every literal normal section, while preserving the already constructed
fixed-top coefficient exactly.
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

/-- A uniform ambient dual bound passes to every inflated literal normal
section with the same number of generators. -/
theorem inflatedSectionDual_generated_of_ambientDual_uniform
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual H)
    (N : Subgroup S.A) [N.Normal] :
    RepresentationGeneratedBy
      (inflatedSectionRepresentation S phi C N).dual H := by
  let identity :
      (ambientRepresentation S phi C).IntertwiningMap
        (ambientRepresentation S phi C) :=
    { toLinearMap := LinearMap.id
      isIntertwining' := fun _ ↦ rfl }
  exact representationDual_generated_of_subquotient huniform
    identity Function.injective_id
    (sectionQuotientIntertwiner S phi C N)
    (sectionQuotientIntertwiner_surjective S phi C N)

/-- Replace an existing joint capacity by any proved uniform ambient-dual
generator bound, retaining its fixed-top coefficient. -/
noncomputable def jointCapacitySharpenTo_of_ambientDual_uniform
    (H : ℕ)
    (B : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual H) :
    ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart where
  capacity := H
  capacity_nonneg := Nat.zero_le H
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
        (inflatedSectionRepresentation S phi C N.1).dual H :=
      inflatedSectionDual_generated_of_ambientDual_uniform
        S phi C H huniform N.1
    have hinflated : representationSchurCapacity
        (inflatedSectionRepresentation S phi C N.1) ≤ H :=
      by
        simpa using representationSchurCapacity_le_of_dual_generated
          (inflatedSectionRepresentation S phi C N.1) H hgen
    have heq := representationSchurCapacity_comp
      (QuotientGroup.mk' ((pi S phi).ker ⊔ N.1))
      (QuotientGroup.mk'_surjective ((pi S phi).ker ⊔ N.1))
      ((originalChart S phi C).sectionRepresentation
        (pi S phi) (E S phi C).quotientRepresentation N.1).ρ
    rw [← heq]
    exact hinflated
  coefficient := B.coefficient
  coefficient_nonneg := B.coefficient_nonneg
  fixed_top_fibre := B.fixed_top_fibre

@[simp] theorem jointCapacitySharpenTo_of_ambientDual_uniform_capacity
    (H : ℕ)
    (B : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual H) :
    (jointCapacitySharpenTo_of_ambientDual_uniform
      S phi C H B huniform).capacity = H := rfl

@[simp] theorem jointCapacitySharpenTo_of_ambientDual_uniform_coefficient
    (H : ℕ)
    (B : ElementaryLayerJointCapacityBound C.p
      (pi S phi) (QuotientGroup.mk'_surjective (K S phi))
      (E S phi C).quotientRepresentation
      (E S phi C).originalKernelChart)
    (huniform : UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C).dual H) :
    (jointCapacitySharpenTo_of_ambientDual_uniform
      S phi C H B huniform).coefficient = B.coefficient := rfl

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
