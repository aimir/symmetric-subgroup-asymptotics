import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Equal literal local kernels give equal correlated compression kernels.
The quotient of the original group is consequently equivalent to the
actual image of either local model. No equality of their ambient target
groups or surjectivity onto an oversized target is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathCompressionKernelCongruence
open PermutationalWreathProduct

variable {A D L M Q I : Type} [Group A] [Group D] [Group L] [Group M] [Group Q]
    [MulAction Q I] (rho : A →* PermutationalWreathProduct D Q I)
    (phi : D →* L) (psi : D →* M)

theorem kernel_eq_of_ker_eq (hker : phi.ker = psi.ker) :
    Compression.kernel rho phi = Compression.kernel rho psi := by
  ext g
  change rho g ∈ (mapBase phi).ker ↔ rho g ∈ (mapBase psi).ker
  rw [mem_mapBase_ker_iff,mem_mapBase_ker_iff,hker]

def quotientEquivImage (hker : phi.ker = psi.ker) :
    A ⧸ Compression.kernel rho phi ≃* (Compression.map rho psi).range :=
  (QuotientGroup.quotientMulEquivOfEq (kernel_eq_of_ker_eq rho phi psi hker)).trans
    (QuotientGroup.quotientKerEquivRange (Compression.map rho psi))

end SymmetricSubgroupAsymptotics.WreathCompressionKernelCongruence
