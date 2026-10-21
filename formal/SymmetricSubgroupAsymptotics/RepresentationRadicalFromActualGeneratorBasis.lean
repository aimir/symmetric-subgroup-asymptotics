import SymmetricSubgroupAsymptotics.RepresentationDisplacementSubgroup
import SymmetricSubgroupAsymptotics.RepresentationRadicalFromOriginalRows

/-! Actual generating rows suffice to identify the entire original
radical. This avoids checking the same state displacement separately at
every source element in a selected finite affine-row packet. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem representation_radical_eq_of_actual_generators_basis
    {G J : Type} [Group G] {n d e c : ℕ}
    (rho : Representation (ZMod 2) G (Fin n → ZMod 2))
    (W : Subrepresentation rho) (S : BinaryCoordinateSpace n d) (R : BinaryCoordinateSpace n e)
    (u : J → G) (hgen : Subgroup.closure (Set.range u) = ⊤)
    (hW : W.toSubmodule = S.space)
    (hbasis : ∀ j i, rho (u j) (S.inclusion (Pi.single i 1)) -
      S.inclusion (Pi.single i 1) ∈ R.space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ c)
    (hdim : d = e + c) :
    (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype = R.space := by
  have hu : ∀ j, ∀ v ∈ W.toSubmodule, rho (u j) v - v ∈ R.space := by
    intro j v hv
    rw [hW] at hv
    let L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) := rho (u j) - LinearMap.id
    have hle : S.space ≤ R.space.comap L := by
      apply S.le_of_basis_mem
      intro i
      change L (S.inclusion (Pi.single i 1)) ∈ R.space
      simpa only [L,LinearMap.sub_apply,LinearMap.id_apply] using hbasis j i
    have hm : L v ∈ R.space := hle hv
    simpa only [L,LinearMap.sub_apply,LinearMap.id_apply] using hm
  apply representation_radical_eq_of_trivial_quotient_head_cap rho W R.space
    (representation_displacement_mem_of_actual_generators rho W R.space u hgen hu) c hcap
  rw [hW,S.finrank,R.finrank]
  exact hdim

end SymmetricSubgroupAsymptotics
