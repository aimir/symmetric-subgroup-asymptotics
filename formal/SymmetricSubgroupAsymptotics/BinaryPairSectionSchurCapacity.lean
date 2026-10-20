import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-!
# Schur capacity of an actual binary pair section

The finite pair-top tables control generators of submodules of the dual
permutation module.  An actual retained pair section is a quotient of the
literal correlated flip submodule.  Dualising the quotient embeds it into
the dual correlated module, so the same uniform generator bound controls
its Schur capacity.

This is the semantic bridge between a finite module registry and the
Schur-lift theorem.  It retains the actual original normal subgroup and
uses the actual quotient action supplied by `BinaryPairFrame`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)

/-- A uniform generator theorem on the dual natural permutation module
bounds the Schur capacity of every actual retained pair section. -/
theorem sectionRepresentation_schurCapacity_le_of_uniformDual
    [Finite I]
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I).dual H)
    (N : Subgroup U) [N.Normal] :
    representationSchurCapacity (F.sectionRepresentation N) ≤ H := by
  let rho := permutationFunctionRepresentation (ZMod 2) F.top.range I
  let sigma := F.kernelTopPermutationSubrepresentation.toRepresentation
  let tau := inflatedRepresentation (F.sectionTopQuotient N)
    (F.sectionRepresentation N)
  let inclusion : sigma.IntertwiningMap rho :=
    subrepresentationInclusion rho F.kernelTopPermutationSubrepresentation
  have hinclusion : Function.Injective inclusion :=
    Subtype.val_injective
  have hgenerated : RepresentationGeneratedBy tau.dual H :=
    representationDual_generated_of_subquotient
      huniform inclusion hinclusion (F.sectionTopIntertwiner N)
        (F.normalSpace N).mkQ_surjective
  have hcapacity : representationSchurCapacity tau ≤ H :=
    representationSchurCapacity_le_of_dual_generated tau H hgenerated
  simpa only [tau,
    representationSchurCapacity_comp (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N)] using hcapacity

/-- The finite generator certificate may stay on an isomorphic literal top.
Pull the actual section back along the specified top equivalence, apply the
subquotient theorem there, and use invariance of Schur capacity under a
surjective action map.  This avoids transporting generated tuples between
two different group algebras. -/
theorem sectionRepresentation_schurCapacity_le_of_uniformDualEquiv
    [Finite I]
    {HGroup : Type} [Group HGroup]
    (rho : Representation (ZMod 2) HGroup (I → ZMod 2))
    (e : HGroup ≃* F.top.range)
    (he : ∀ g v, rho g v =
      permutationFunctionRepresentation (ZMod 2) F.top.range I (e g) v)
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound rho.dual H)
    (N : Subgroup U) [N.Normal] :
    representationSchurCapacity (F.sectionRepresentation N) ≤ H := by
  let sigmaSub : Subrepresentation rho :=
    { toSubmodule := F.kernelTopPermutationSubrepresentation.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        rw [he]
        exact F.kernelTopPermutationSubrepresentation.apply_mem_toSubmodule
          (e g) hv }
  let sigma := sigmaSub.toRepresentation
  let tauTop := inflatedRepresentation (F.sectionTopQuotient N)
    (F.sectionRepresentation N)
  let tau := inflatedRepresentation e.toMonoidHom tauTop
  let inclusion : sigma.IntertwiningMap rho :=
    subrepresentationInclusion rho sigmaSub
  have hinclusion : Function.Injective inclusion :=
    Subtype.val_injective
  let quotient : sigma.IntertwiningMap tau :=
    { toLinearMap := (F.sectionTopIntertwiner N).toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        change (F.sectionTopIntertwiner N)
            ⟨rho g v.1, sigmaSub.apply_mem_toSubmodule g v.2⟩ =
          tauTop (e g)
            ((F.sectionTopIntertwiner N) v)
        simpa only [he] using
          (Representation.IntertwiningMap.isIntertwining
            _ _ (F.sectionTopIntertwiner N) (e g) v) }
  have hquotient : Function.Surjective quotient := by
    intro y
    obtain ⟨x, hx⟩ := (F.normalSpace N).mkQ_surjective y
    exact ⟨x, hx⟩
  have hgenerated : RepresentationGeneratedBy tau.dual H :=
    representationDual_generated_of_subquotient
      huniform inclusion hinclusion quotient hquotient
  have hcapacityPullback : representationSchurCapacity tau ≤ H :=
    representationSchurCapacity_le_of_dual_generated tau H hgenerated
  have hcapacityTop :
      representationSchurCapacity tauTop ≤ H := by
    simpa only [tau,
      representationSchurCapacity_comp e.toMonoidHom e.surjective] using
        hcapacityPullback
  simpa only [tauTop,
    representationSchurCapacity_comp (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N)] using hcapacityTop

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
