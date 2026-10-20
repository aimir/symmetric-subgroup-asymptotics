import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {p : ℕ} [Fact p.Prime] {G B : Type} [Group G] [Finite G] [Group B]
    (pi : G →* B) (A : Rep (ZMod p) B) [FiniteDimensional (ZMod p) A]
    (E : OriginalKernelModuleChart pi A)
include E in
 theorem relative_head_le_of_uniform (hpi : Function.Surjective pi) (t : ℕ)
    (hu : UniformSubrepresentationGeneratorBound A.ρ t)
    (L : Subgroup G) [L.Normal] (hL : L≤pi.ker) :
    Module.finrank (ZMod p) (primeRelativeCharacters p L)≤t := by
  obtain ⟨x,hx⟩ := exists_normal_generating_tuple_of_normalGen_le L
    (E.kernel_normalGen_le pi A hpi t hu L hL)
  exact primeRelativeHead_le_normal_generating_tuple p L x hx
end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
