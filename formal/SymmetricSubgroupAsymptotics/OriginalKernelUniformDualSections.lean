import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Uniform generation on the original dual module controls the exact
kernel section of every original normal quotient and its residual top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G T : Type} [Group G] [Group T]
    (pi : G →* T) (A : Rep.{0} (ZMod 2) T)
    (E : OriginalKernelModuleChart pi A)

theorem sectionDualGeneratedBy_of_uniform
    (hpi : Function.Surjective pi) {H : ℕ}
    (hdual : UniformSubrepresentationGeneratorBound A.ρ.dual H)
    (N : Subgroup G) [N.Normal] :
    RepresentationGeneratedBy (E.sectionRepresentation pi A N).ρ.dual H := by
  let sigma : Representation (ZMod 2) T (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)
  let q : A.ρ.IntertwiningMap sigma := E.sectionProjectionOnBase pi A N hpi
  have hq : Function.Surjective q := E.sectionProjectionOnBase_surjective pi A N hpi
  have hi : Function.Injective (RepresentationHeadExact.dualMap q) :=
    LinearMap.dualMap_injective_of_surjective hq
  have hg : RepresentationGeneratedBy sigma.dual H :=
    representationGeneratedBy_of_injective_of_uniform hdual
      (RepresentationHeadExact.dualMap q) hi
  exact RepresentationGeneratedBy.of_comp
    (E.sectionRepresentation pi A N).ρ.dual (sectionTop pi N hpi) (by
      change RepresentationGeneratedBy
        (Representation.dual ((E.sectionRepresentation pi A N).ρ.comp
          (sectionTop pi N hpi))) _ at hg
      rw [representation_dual_comp] at hg
      exact hg)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
