import SymmetricSubgroupAsymptotics.IntrinsicRadicalOrbitWitnessKernel
import Mathlib.GroupTheory.Index
import Lean.Elab.Tactic.Omega

/-! Three actual orbit images suffice for the SAME original subgroup
of index two. No uniform stabilizer cap or larger replacement subgroup
is assumed or constructed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem submodule_le_of_intrinsic_radical_three_orbit_witnesses_index_two
    {k G V C : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
    (rho : Representation k G V) (W : Subrepresentation rho)
    (S R : Submodule k V) (hS : W.toSubmodule = S)
    (hR : (Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype = R)
    (projection : V →ₗ[k] C) (sectionMap : C →ₗ[k] V)
    (hdefect : ∀ v, v - sectionMap (projection v) ∈ S)
    (hwitness : ∀ c : C, c ≠ 0 → ∃ u : Fin 3 → G,
      ∀ i j : Fin 3, i ≠ j →
        rho (u i) (sectionMap c) - rho (u j) (sectionMap c) ∉ R)
    (D : Subgroup G) (hindex : D.index = 2)
    (K : Submodule k V)
    (hfixed : ∀ d : D, ∀ v ∈ K, rho (d : G) v - v ∈ R) : K ≤ S := by
  apply submodule_le_of_intrinsic_radical_orbit_witnesses rho W S R hS hR
    projection sectionMap hdefect 3 hwitness D _ K hfixed
  have hc := D.card_mul_index
  have hp : 0 < Nat.card D := Nat.card_pos
  rw [hindex] at hc
  omega

end SymmetricSubgroupAsymptotics
