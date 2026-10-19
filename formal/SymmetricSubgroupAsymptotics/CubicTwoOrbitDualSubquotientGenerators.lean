import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.SixPairB6CubicOrbitCoordinates
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Two actual binary observations and their cubic translates control the
DUAL of every retained module quotient. The acting group may be larger
than the cubic subgroup; enlargement adds operators and costs nothing. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicTwoOrbitDualSubquotientGenerators

variable {T V W : Type} [Group T]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]

set_option maxHeartbeats 1000000 in
/-- A literal injected quotient of two regular cubic orbits has dual
module generation at most two, including under the original larger top. -/
theorem of_regular_subquotient
    (rho : Representation (ZMod 2) T V)
    (sigma : Representation (ZMod 2) T W) (cubic : CyclicThree →* T)
    (i : Representation.IntertwiningMap (rho.comp cubic) CubicBinaryCoordinateUniform.regular)
    (hi : Function.Injective i) (q : rho.IntertwiningMap sigma)
    (hq : Function.Surjective q) :
    RepresentationGeneratedBy sigma.dual 2 := by
  have hu : UniformSubrepresentationGeneratorBound
      CubicBinaryCoordinateUniform.regular.dual 2 :=
    permutationFunctionRepresentation_dual_uniform
      CubicBinaryCoordinateUniform.regular_uniform
  let qc : Representation.IntertwiningMap (rho.comp cubic) (sigma.comp cubic) := {
    toLinearMap := q.toLinearMap
    isIntertwining' g := q.isIntertwining' (cubic g) }
  have hg : RepresentationGeneratedBy (Representation.dual (sigma.comp cubic)) 2 :=
    representationDual_generated_of_subquotient hu i hi qc hq
  exact RepresentationGeneratedBy.of_comp sigma.dual cubic (by simpa only [representation_dual_comp] using hg)

/-- Observation at one actual coarse block, followed by the original cubic
conjugates, supplies the required regular embedding. -/
theorem of_observation
    (rho : Representation (ZMod 2) T V)
    (sigma : Representation (ZMod 2) T W) (cubic : CyclicThree →* T)
    (observation : V →ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (hseparate : ∀ v : V,
      (∀ c : CyclicThree, observation (rho (cubic c) v)=0) → v=0)
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q) :
    RepresentationGeneratedBy sigma.dual 2 :=
  of_regular_subquotient rho sigma cubic
    (SixPairB6CubicOrbitCoordinates.embedding (rho.comp cubic) observation)
    (SixPairB6CubicOrbitCoordinates.embedding_injective
      (rho.comp cubic) observation hseparate) q hq

end SymmetricSubgroupAsymptotics.CubicTwoOrbitDualSubquotientGenerators
