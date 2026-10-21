import SymmetricSubgroupAsymptotics.RepresentationCoinvariantRestrictionBound
import Mathlib.RepresentationTheory.Subrepresentation

/-! Restriction along an acting-group homomorphism with an explicit
pointwise action equation, retaining the SAME invariant vector subspace.
The generic construction avoids normalization of closed finite group
representation implementations in dependent record fields. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G H V : Type} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (tau : Representation k H V)
    (f : H →* G) (he : ∀ h v, rho (f h) v = tau h v)

def restrictionSameVectors (W : Subrepresentation rho) : Subrepresentation tau where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule h v hv := (he h v) ▸ W.apply_mem_toSubmodule (f h) hv

@[simp] theorem restrictionSameVectors_space (W : Subrepresentation rho) :
    (restrictionSameVectors rho tau f he W).toSubmodule = W.toSubmodule := rfl

theorem restrictionSameVectors_head_le (W : Subrepresentation rho) :
    Module.finrank k W.toRepresentation.Coinvariants ≤
      Module.finrank k (restrictionSameVectors rho tau f he W).toRepresentation.Coinvariants := by
  have hr : (restrictionSameVectors rho tau f he W).toRepresentation =
      W.toRepresentation.comp f := by
    apply MonoidHom.ext
    intro h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (he h v.val).symm
  rw [hr]
  exact coinvariants_finrank_le_comp_group W.toRepresentation f
end SymmetricSubgroupAsymptotics
