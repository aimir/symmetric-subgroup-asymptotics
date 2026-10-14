import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32TypewiseHead
import SymmetricSubgroupAsymptotics.RepresentationSimpleTargetSurjectiveDescent
import SymmetricSubgroupAsymptotics.RepresentationSectionUniformTargetHom
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees
import SymmetricSubgroupAsymptotics.SchurMultiplicityTargetEquiv

/-!
# Degree-two sections over the original row-32 acting group

The same literal natural-module proof applies through every actual onto
map with binary kernel. Normal binary kernels fix simple binary targets;
descent therefore retains their dimensions and their exact simple type.
The quotient section and its surjective intertwiner remain over the
original group throughout the conclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32OriginalDegreeTwoSections


local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem section_multiplicity_le_two
    {G W X : Type} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (gamma : G →* PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) (hgamma : Function.Surjective gamma)
    (hker : IsPGroup 2 gamma.ker)
    (tau : Representation (ZMod 2) G W)
    (sigma : Representation (ZMod 2) G X)
    [IsSimpleModule (ZMod 2)[G] sigma.asModule]
    (hdim : Module.finrank (ZMod 2) X = 2)
    (hEnd : Module.finrank (ZMod 2) (Module.End (ZMod 2)[G] sigma.asModule) = 2)
    (M : Subrepresentation (inflatedRepresentation gamma PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation))
    (q : M.toRepresentation.IntertwiningMap tau) (hq : Function.Surjective q) :
    schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[G])
      (A := tau.asModule) (X := sigma.asModule) ≤ 2 := by
  letI : Finite X := Module.finite_of_finite (ZMod 2)
  have hfixed : gamma.ker ≤ sigma.ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro x
    exact normal_pSubgroup_simple_representation_fixed sigma gamma.ker hker ⟨g, hg⟩ x
  have hHom : ∀ N : Subrepresentation (inflatedRepresentation gamma PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation),
      Module.finrank (ZMod 2) (N.toRepresentation.IntertwiningMap sigma) ≤ 4 := by
    apply uniform_simple_targetHom_le_of_surjective gamma hgamma
      PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation sigma hfixed 2 2 4 hdim hEnd
    intro sigmaTop _hSimple hdimTop hEndTop N
    exact PrimitiveAffineDegreeTwoTwelveRow32TypewiseHead.intertwining_finrank_le_four sigmaTop hdimTop hEndTop N
  have h := representationSchurMultiplicity_mul_end_le_of_section_uniform_targetHom
    (inflatedRepresentation gamma PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation) tau sigma 4 hHom M q hq
  rw [hEnd] at h
  omega

/-- The actual selected simple-submodule API, with both dimensions derived
from its degree-two Schur profile rather than supplied as extra data. -/
theorem section_multiplicity_le_two_of_productDegree
    {G W X : Type} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (gamma : G →* PrimitiveAffineDegreeTwoTwelveRow32BinaryChart.Top) (hgamma : Function.Surjective gamma)
    (hker : IsPGroup 2 gamma.ker)
    (tau : Representation (ZMod 2) G W)
    (sigma : Representation (ZMod 2) G X)
    (S : Submodule (ZMod 2)[G] sigma.asModule)
    [IsSimpleModule (ZMod 2)[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hdegree : schurSimpleProductDegree sigma S = 2)
    (M : Subrepresentation (inflatedRepresentation gamma PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators.representation))
    (q : M.toRepresentation.IntertwiningMap tau) (hq : Function.Surjective q) :
    schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[G])
      (A := tau.asModule) (X := S) ≤ 2 := by
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let sigmaS := (Subrepresentation.ofSubmodule' S).toRepresentation
  let e := submoduleRepresentationModuleEquiv sigma S
  letI : IsSimpleModule (ZMod 2)[G] sigmaS.asModule := IsSimpleModule.congr e.symm
  have hdim : Module.finrank (ZMod 2) (Subrepresentation.ofSubmodule' S).toSubmodule = 2 := by
    calc
      _ = Module.finrank (ZMod 2) sigmaS.asModule := sigmaS.asModuleEquiv.finrank_eq.symm
      _ = Module.finrank (ZMod 2) S := (e.restrictScalars (ZMod 2)).finrank_eq.symm
      _ = 2 := (schurSimpleProductDegree_eq_two_profile sigma S hnonfixed hdegree).1
  have hEnd : Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[G] sigmaS.asModule) = 2 :=
    (moduleEnd_finrank_eq_of_linearEquiv (k := ZMod 2) e).symm.trans
      (schurSimpleProductDegree_eq_two_end_finrank sigma S hnonfixed hdegree)
  have h := section_multiplicity_le_two gamma hgamma hker tau sigmaS hdim hEnd M q hq
  rw [← schurSocleMultiplicity_eq_of_source_linearEquiv
    (k := ZMod 2) (R := (ZMod 2)[G]) (A := tau.asModule) e] at h
  exact h

end PrimitiveAffineDegreeTwoTwelveRow32OriginalDegreeTwoSections
end SymmetricSubgroupAsymptotics

end
