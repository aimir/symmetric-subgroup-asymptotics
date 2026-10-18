import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Uniform generation of the exact kernel section for arbitrary original
normal denominators. No invertibility or semisimplicity is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

/-- Every invariant subspace of the actual section inherits the original
uniform bound through its literal quotient projection. -/
theorem sectionUniform (hpi : Function.Surjective pi) {n : ℕ}
    (hA : UniformSubrepresentationGeneratorBound A.ρ n) :
    UniformSubrepresentationGeneratorBound (E.sectionRepresentation pi A N).ρ n := by
  have hpull : UniformSubrepresentationGeneratorBound
      ((E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N hpi)) n :=
    hA.of_surjective (E.sectionProjectionOnBase pi A N hpi)
      (E.sectionProjectionOnBase_surjective pi A N hpi)
  exact UniformSubrepresentationGeneratorBound.of_comp
    (E.sectionRepresentation pi A N).ρ (sectionTop pi N hpi) hpull

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
