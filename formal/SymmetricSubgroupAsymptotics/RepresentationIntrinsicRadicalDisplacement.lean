import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeRadical

/-! Every actual source displacement on an invariant subspace belongs to
its full intrinsic radical. This supplies the structural state-killing
fact for sparse stabilizer counts without checking all source elements. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V]

theorem subrepresentation_displacement_mem_intrinsic_radical
    (rho : Representation k G V) (W : Subrepresentation rho)
    (g : G) (v : V) (hv : v ∈ W.toSubmodule) :
    rho g v - v ∈
      (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype := by
  let z : W.toSubmodule := ⟨v,hv⟩
  refine ⟨W.toRepresentation g z - z,
    Representation.Coinvariants.sub_mem_ker (ρ := W.toRepresentation) g z, ?_⟩
  rfl

theorem subrepresentation_displacement_mem_of_radical_eq
    (rho : Representation k G V) (W : Subrepresentation rho)
    (S R : Submodule k V) (hS : W.toSubmodule = S)
    (hR : (Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype = R)
    (g : G) (v : V) (hv : v ∈ S) : rho g v - v ∈ R := by
  rw [← hR]
  apply subrepresentation_displacement_mem_intrinsic_radical rho W g v
  rw [hS]
  exact hv

end SymmetricSubgroupAsymptotics
