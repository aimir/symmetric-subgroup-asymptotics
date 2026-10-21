import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Elements acting trivially modulo a fixed linear denominator on an
original invariant subspace form a subgroup. Thus literal displacement
identities need only be checked on actual whole-source generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- No invariance premise on R is needed: the defining condition itself
implies the needed stability of the tested subspace modulo R. -/
def representationDisplacementSubgroup (rho : Representation k G V)
    (W : Subrepresentation rho) (R : Submodule k V) : Subgroup G where
  carrier := {g | ∀ v ∈ W.toSubmodule, rho g v - v ∈ R}
  one_mem' := by
    intro v _
    rw [map_one,Module.End.one_apply,sub_self]
    exact R.zero_mem
  mul_mem' := by
    intro g h hg hh v hv
    have h1 := hg (rho h v) (W.apply_mem_toSubmodule h hv)
    have h2 := hh v hv
    have he : rho (g*h) v - v = (rho g (rho h v) - rho h v) + (rho h v - v) := by
      rw [map_mul,Module.End.mul_apply]
      abel
    rw [he]
    exact R.add_mem h1 h2
  inv_mem' := by
    intro g hg v hv
    have h := hg (rho g⁻¹ v) (W.apply_mem_toSubmodule g⁻¹ hv)
    rw [rho.self_inv_apply] at h
    have he : rho g⁻¹ v - v = -(v-rho g⁻¹ v) := by abel
    rw [he]
    exact R.neg_mem h

theorem representation_displacement_mem_of_actual_generators
    (rho : Representation k G V) (W : Subrepresentation rho) (R : Submodule k V)
    {J : Type} (u : J → G) (hgen : Subgroup.closure (Set.range u) = ⊤)
    (hu : ∀ j, ∀ v ∈ W.toSubmodule, rho (u j) v - v ∈ R) :
    ∀ g, ∀ v ∈ W.toSubmodule, rho g v - v ∈ R := by
  have htop : (⊤ : Subgroup G) ≤ representationDisplacementSubgroup rho W R := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact hu j
  intro g
  exact htop (Subgroup.mem_top g)

end SymmetricSubgroupAsymptotics
