import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowNoFixedPoint

/-! Transport a moving element into an abstract raw permutation subgroup.
No concrete image-subgroup action is unfolded in the statement or proof. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGActionSubgroupMove

theorem exists_move_of_map_le {G Y : Type*} [Group G] [MulAction G Y]
    (rho : G →* Equiv.Perm Y) (hact : ∀ g y, rho g y = g • y)
    (P : Subgroup G) (K : Subgroup (Equiv.Perm Y)) (hPK : P.map rho ≤ K) (x : Y)
    (hm : ∃ h : P, h • x ≠ x) : ∃ h : K, (h : Equiv.Perm Y) x ≠ x := by
  obtain ⟨h, hh⟩ := hm
  refine ⟨⟨rho h.val, hPK ⟨h.val, h.property, rfl⟩⟩, ?_⟩
  change rho h.val x ≠ x
  rw [hact]
  exact hh

theorem alternating_exists_move {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Sylow 2 (alternatingGroup Y)) (K : Subgroup (Equiv.Perm Y))
    (hPK : (P : Subgroup (alternatingGroup Y)).map (alternatingGroup Y).subtype ≤ K)
    (hsize : 3 ≤ Nat.card Y) (heven : 2 ∣ Nat.card Y) (x : Y) :
    ∃ h : K, (h : Equiv.Perm Y) x ≠ x := by
  exact exists_move_of_map_le (alternatingGroup Y).subtype (fun _ _ => rfl)
    (P : Subgroup (alternatingGroup Y)) K hPK x
    (CFSGAlternatingSylowNoFixedPoint.exists_move hsize heven P x)

end SymmetricSubgroupAsymptotics.CFSGActionSubgroupMove
