import SymmetricSubgroupAsymptotics.OriginalKernelSectionGeneration
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! Uniform generation descends through every literal original kernel
section in arbitrary prime characteristic, without averaging. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {p : ℕ} [Fact p.Prime] {G B : Type} [Group G] [Group B]
    (pi : G →* B) (A : Rep.{0} (ZMod p) B) (E : OriginalKernelModuleChart pi A)
    (N : Subgroup G) [N.Normal]

theorem sectionUniform_prime (hpi : Function.Surjective pi) {n : ℕ}
    (hu : UniformSubrepresentationGeneratorBound A.ρ n) :
    UniformSubrepresentationGeneratorBound (E.sectionRepresentation pi A N).ρ n := by
  have hi : UniformSubrepresentationGeneratorBound (A.ρ.comp pi) n :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective A.ρ pi hpi hu
  have hs := hi.of_surjective (E.sectionProjection pi A N)
    (E.sectionProjection_surjective pi A N)
  exact UniformSubrepresentationGeneratorBound.of_comp
    (E.sectionRepresentation pi A N).ρ (QuotientGroup.mk' (pi.ker ⊔ N)) hs

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
