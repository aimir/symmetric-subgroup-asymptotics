import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOuterNestedQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerNestedQuotient
import SymmetricSubgroupAsymptotics.RepresentationSchurCapacityExact
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual

/-!
# Three actual pair-tower layers over a cyclic natural module

A uniform cyclic-subrepresentation theorem for the literal last top
bounds every dual nested quotient by one generator. The existing exact
outer pair-constant/pair-sum sequence and inner omega image then bound
the actual direct kernel's omega socle by three. The original normal
subgroup and all quotient maps are retained. No fixed-type exception or
normal registry is needed for this stronger natural-module hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTowerCyclicCapacity

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  (uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) 1)

include uniform in
theorem nestedQuotient_dual_generated
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B) :
    RepresentationGeneratedBy (nestedQuotientRepresentation A B hAB).dual 1 := by
  let i : B.toRepresentation.IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
    { toLinearMap := B.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let q : B.toRepresentation.IntertwiningMap
      (nestedQuotientRepresentation A B hAB) :=
    { toLinearMap := (nestedSubrepresentation A B hAB).toSubmodule.mkQ
      isIntertwining' _ := rfl }
  exact representationDual_generated_of_subquotient
    (permutationFunctionRepresentation_dual_uniform uniform)
    i B.toSubmodule.injective_subtype q
    (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective

include uniform in
theorem nestedQuotient_capacity_le_one
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B) :
    representationSchurCapacity (nestedQuotientRepresentation A B hAB) ≤ 1 := by
  simpa only [Nat.cast_one] using representationSchurCapacity_le_of_dual_generated _ 1
    (nestedQuotient_dual_generated uniform A B hAB)

variable {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

local instance innerOmegaFinite
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Finite (R.innerOmegaSubrepresentation N).toSubmodule :=
  Finite.of_surjective _ (R.rawKernelOmegaInnerImageIntertwiner_surjective N)

local instance innerOmegaFiniteDimensional
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    FiniteDimensional (ZMod 2) (R.innerOmegaSubrepresentation N).toSubmodule :=
  Module.Finite.of_finite

include uniform in
theorem outerNestedQuotient_capacity_le_two
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    representationSchurCapacity (nestedQuotientRepresentation
      (R.frame.normalTopPermutationSubrepresentation N.1)
      (R.outerOmegaAxis N) (R.outerNormalAxis_le_outerOmegaAxis N)) ≤ 2 := by
  let rho := nestedQuotientRepresentation
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N) (R.outerNormalAxis_le_outerOmegaAxis N)
  let q := R.outerNestedQuotientPairSumMap N
  let K := nestedQuotientRepresentation
    (R.outerNormalConstantPullbackAxis N) (R.outerOmegaConstantPullbackAxis N)
    (R.outerNormalConstant_le_outerOmegaConstant N)
  let T := nestedQuotientRepresentation
    (R.outerNormalPairSumPullbackAxis N) (R.outerOmegaPairSumPullbackAxis N)
    (R.outerNormalPairSum_le_outerOmegaPairSum N)
  have hK : representationSchurCapacity K ≤ (1 : ℕ) := by
    apply representationSchurCapacity_le_of_equiv K _
      (R.outerConstantQuotientEquiv N) 1
    rw [representationSchurCapacity_comp R.outerTopToLiteral
      R.outerTopToLiteral_surjective]
    simpa only [Nat.cast_one] using nestedQuotient_capacity_le_one uniform
      (R.outerNormalConstantAxis N) (R.outerOmegaConstantAxis N)
      (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)
  have hT : representationSchurCapacity T ≤ (1 : ℕ) := by
    apply representationSchurCapacity_le_of_equiv T _
      (R.outerPairSumQuotientEquiv N) 1
    rw [representationSchurCapacity_comp R.outerTopToLiteral
      R.outerTopToLiteral_surjective]
    simpa only [Nat.cast_one] using nestedQuotient_capacity_le_one uniform
      (R.outerNormalPairSumAxis N) (R.outerOmegaPairSumAxis N)
      (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)
  have hker : representationSchurCapacity q.ker.toRepresentation ≤ (1 : ℕ) :=
    representationSchurCapacity_le_of_equiv _ K
      (R.outerNestedQuotientPairSumKernelEquiv N).symm 1 hK
  simpa using representationSchurCapacity_le_kernel_add_target rho T q
    (R.outerNestedQuotientPairSumMap_surjective N) 1 1 hker hT

include uniform in
theorem innerOmega_capacity_le_one
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    representationSchurCapacity
      (inflatedRepresentation (R.rawQuotientMap N)
        (R.innerOmegaSubrepresentation N).toRepresentation) ≤ 1 := by
  rw [representationSchurCapacity_comp (R.rawQuotientMap N)
    (R.rawQuotientMap_surjective N)]
  have h := representationSchurCapacity_le_of_equiv _ _
    (R.innerNestedQuotientEquivInnerOmegaInflation N).symm 1
    (by
      simpa only [Nat.cast_one] using nestedQuotient_capacity_le_one uniform
        (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
        (R.moduleAxis_le_innerOmegaNaturalAxis N))
  rw [representationSchurCapacity_comp (QuotientGroup.mk' (R.topNormal N.1))
    (QuotientGroup.mk'_surjective _)] at h
  simpa only [Nat.cast_one] using h

include uniform in
theorem outerOmega_capacity_le_two
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    representationSchurCapacity
      (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation ≤ 2 := by
  have htop : representationSchurCapacity
      ((nestedQuotientRepresentation
        (R.frame.normalTopPermutationSubrepresentation N.1)
        (R.outerOmegaAxis N) (R.outerNormalAxis_le_outerOmegaAxis N)).comp
          R.frame.top.rangeRestrict) ≤ (2 : ℕ) := by
    rw [representationSchurCapacity_comp R.frame.top.rangeRestrict
      R.frame.top.rangeRestrict_surjective]
    simpa using outerNestedQuotient_capacity_le_two uniform R N
  have h := representationSchurCapacity_le_of_equiv _ _
    (R.rawKernelOmegaOuterInflationEquivNestedQuotient N) 2 htop
  rw [representationSchurCapacity_comp (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective _)] at h
  simpa using h

include uniform in
theorem rawKernelOmega_capacity_le_three
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    representationSchurCapacity
      (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N)) ≤ 3 := by
  simpa using representationSchurCapacity_le_kernel_add_target
    (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))
    (inflatedRepresentation (R.rawQuotientMap N)
      (R.innerOmegaSubrepresentation N).toRepresentation)
    (R.rawKernelOmegaInnerImageIntertwiner N)
    (R.rawKernelOmegaInnerImageIntertwiner_surjective N) 2 1
    (by simpa using outerOmega_capacity_le_two uniform R N)
    (by simpa only [Nat.cast_one] using innerOmega_capacity_le_one uniform R N)

include uniform in
theorem omegaSocle_capacity_le_three
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N))).toRepresentation ≤ 3 := by
  let rho := binaryKernelOmegaConjugationRepresentation (R.rawQuotientMap N)
  let S := finiteRepresentationSocle rho
  let i : S.toRepresentation.IntertwiningMap rho :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  simpa using representationSchurCapacity_le_of_injective S.toRepresentation rho i
    S.toSubmodule.injective_subtype 3
    (by simpa using rawKernelOmega_capacity_le_three uniform R N)

end DegreeTwoPairTowerCyclicCapacity
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
