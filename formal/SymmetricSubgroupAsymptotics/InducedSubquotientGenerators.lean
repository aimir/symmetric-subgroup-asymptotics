import SymmetricSubgroupAsymptotics.InducedDualEquivalence
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-!
# Generator bounds for subquotients of induced representations

Tracey's theorem is stated for subrepresentations of a literal induced
module.  The affine normal-graph incidence also needs its dual consequence:
the dual of every quotient of such a subrepresentation has the same padded
generator bound.  This file proves the passage by taking the pullback of the
dual quotient inside the dual induced module and using finite-index induced
duality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {G V : Type} [Group G]

namespace InducedSubquotientGenerators

variable {p : ℕ} [Fact p.Prime]
variable (Hsub : Subgroup G)
  [AddCommGroup V] [Module (ZMod p) V]
  (rho : Representation (ZMod p) Hsub V)

/-- Tracey's uniform theorem transported to the dual of the literal induced
module. -/
theorem dualInduced_uniform
    [Finite G] [Hsub.FiniteIndex]
    (hTracey : TraceyAffineInducedModuleInput)
    (hindex : 2 ≤ Hsub.index) [FiniteDimensional (ZMod p) V] :
    UniformSubrepresentationGeneratorBound
      (Representation.ind Hsub.subtype rho).dual
      (traceyInducedGeneratorCeiling
        (Module.finrank (ZMod p) V) Hsub.index) := by
  let e := InducedDualEquivalence.inducedDualEquiv Hsub rho
  have hlocal := hTracey.uniform p G Hsub hindex
    (Module.Dual (ZMod p) V) rho.dual
  have htransport := UniformSubrepresentationGeneratorBound.of_injective
    hlocal e.symm.toIntertwiningMap e.symm.injective
  simpa only [Subspace.dual_finrank_eq] using htransport

/-- The same dual transport for the unconditional half-dimension form of
Tracey's theorem. -/
theorem dualInduced_uniform_half
    [Finite G] [Hsub.FiniteIndex]
    (hTracey : TraceyAffineHalfInducedModuleInput)
    (hindex : 2 ≤ Hsub.index) [FiniteDimensional (ZMod p) V] :
    UniformSubrepresentationGeneratorBound
      (Representation.ind Hsub.subtype rho).dual
      (Module.finrank (ZMod p) V * Hsub.index / 2) := by
  let e := InducedDualEquivalence.inducedDualEquiv Hsub rho
  have hlocal := hTracey p G Hsub hindex
    (Module.Dual (ZMod p) V) rho.dual
  have htransport := UniformSubrepresentationGeneratorBound.of_injective
    hlocal e.symm.toIntertwiningMap e.symm.injective
  simpa only [Subspace.dual_finrank_eq] using htransport

/-- The dual of every literal quotient of an induced subrepresentation has
the same padded generator bound. -/
theorem quotientDual_generated
    [Finite G] [Hsub.FiniteIndex]
    (hTracey : TraceyAffineInducedModuleInput)
    (hindex : 2 ≤ Hsub.index) [FiniteDimensional (ZMod p) V]
    (M : Subrepresentation (Representation.ind Hsub.subtype rho))
    (N : Subrepresentation M.toRepresentation) :
    let sigma := M.toRepresentation.quotient N.toSubmodule
      (fun g x hx ↦ N.apply_mem_toSubmodule g hx)
    RepresentationGeneratedBy sigma.dual
      (traceyInducedGeneratorCeiling
        (Module.finrank (ZMod p) V) Hsub.index) := by
  let T := Representation.ind Hsub.subtype rho
  let sigma := M.toRepresentation.quotient N.toSubmodule
    (fun g x hx ↦ N.apply_mem_toSubmodule g hx)
  let iM := subrepresentationInclusion T M
  let q : M.toRepresentation.IntertwiningMap sigma :=
    { toLinearMap := N.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  exact representationDual_generated_of_subquotient
    (dualInduced_uniform Hsub rho hTracey hindex)
    iM M.toSubmodule.injective_subtype q N.toSubmodule.mkQ_surjective

end InducedSubquotientGenerators
end SymmetricSubgroupAsymptotics

end
