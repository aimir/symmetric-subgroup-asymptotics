import Mathlib.RepresentationTheory.Intertwining

set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics
variable {k G T V : Type} [Field k] [Group G] [Group T]
    [AddCommGroup V] [Module k V]

/-- Dual pullback retains the original acting homomorphism. -/
theorem representation_dual_comp (rho : Representation k T V) (f : G →* T) :
    Representation.dual (rho.comp f) = rho.dual.comp f := by
  ext g ell v
  change ell (rho (f g⁻¹) v) = ell (rho (f g)⁻¹ v)
  rw [map_inv]

end SymmetricSubgroupAsymptotics
