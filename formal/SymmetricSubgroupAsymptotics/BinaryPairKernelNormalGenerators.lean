import SymmetricSubgroupAsymptotics.BinaryPairKernelHead
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead

/-! Uniform natural-module generators bound every actual normal subgroup
inside a correlated pair kernel. The elementary chart is the existing
faithful bit chart of that SAME original kernel. No full-flip product or
split extension is substituted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I) [MulAction U I]
    (hact : ∀ (u : U) (i : I), u • i = F.top u i)

/-- The actual correlated pair kernel in its original elementary bit chart. -/
def ordinaryNormalGenerationKernelChart : ElementaryMinimalNormalChart F.top.ker := by
  letI := Fintype.ofFinite I
  exact {
    p := 2
    p_prime := Nat.prime_two
    V := F.kernelSpace
    equiv := F.kernelChart }

include hact

/-- Inflation of the original quotient conjugation module embeds into the
natural module on the original pair labels. -/
def ordinaryNormalGenerationKernelInclusion :
    (show Representation (ZMod 2) U F.kernelSpace from
      (F.ordinaryNormalGenerationKernelChart).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' F.top.ker)).IntertwiningMap
        (permutationFunctionRepresentation (ZMod 2) U I) where
  toLinearMap := F.kernelSpace.subtype
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    obtain ⟨k, hk⟩ := F.kernelChart.surjective (Multiplicative.ofAdd v)
    have hv : (F.kernelChart k).toAdd = v := congrArg Multiplicative.toAdd hk
    rw [← hv]
    change F.kernelSpace.subtype
      ((F.ordinaryNormalGenerationKernelChart).quotientRepresentation.ρ
        (QuotientGroup.mk' F.top.ker u)
        (((F.ordinaryNormalGenerationKernelChart).equiv k).toAdd)) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    change F.bits (MulAut.conjNormal u k) =
      permutationFunctionRepresentation (ZMod 2) U I u (F.bits k)
    exact (F.originalCoordinateAction_bits hact u k).symm

/-- Any uniform bound on the original pair-label natural module controls
all original normals contained in its actual correlated kernel. -/
theorem normalGen_le_of_uniform_pair_module (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U I) H)
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker) :
    MarkedC4.normalGen N ≤ H := by
  have hquot : UniformSubrepresentationGeneratorBound
      (F.ordinaryNormalGenerationKernelChart).quotientRepresentation.ρ H := by
    apply UniformSubrepresentationGeneratorBound.of_comp
      (F.ordinaryNormalGenerationKernelChart).quotientRepresentation.ρ (QuotientGroup.mk' F.top.ker)
    exact huniform.of_injective (ordinaryNormalGenerationKernelInclusion F hact)
      F.kernelSpace.subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    F.top.ker F.ordinaryNormalGenerationKernelChart H hquot N hN

/-- In the nonelementary original top action, all actual normal subkernels
have the generic quarter-degree bound. -/
theorem normalGen_le_quarter_of_not_elementary
    [MulAction.IsPretransitive U I] (hU : IsPGroup 2 U)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := U) (X := I))
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker) :
    MarkedC4.normalGen N ≤ Nat.card I / 4 := by
  apply F.normalGen_le_of_uniform_pair_module hact (Nat.card I / 4) _ N hN
  exact twoGroup_permutationSubrepresentationGeneratedBy_quarter_of_not_elementary hU hnon

end SymmetricSubgroupAsymptotics.BinaryPairFrame
