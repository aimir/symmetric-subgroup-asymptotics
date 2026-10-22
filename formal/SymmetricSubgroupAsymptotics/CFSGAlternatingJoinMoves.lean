import Mathlib.GroupTheory.GroupAction.Hom
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowNoFixedPoint

/-! Move a point after an actual action homomorphism and subgroup inclusion.
The subgroup and action carrier remain abstract throughout the coercion proof. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingJoinMoves

theorem exists_move_map {G Y : Type*} [Group G] [MulAction G Y]
    (rho : G →* Equiv.Perm Y) (hact : ∀ g y, rho g y = g • y)
    (P J : Subgroup G) (hPJ : P ≤ J) (x : Y)
    (hm : ∃ h : P, h • x ≠ x) :
    ∃ h : J.map rho, (h : Equiv.Perm Y) x ≠ x := by
  obtain ⟨h, hh⟩ := hm
  refine ⟨⟨rho h.val, ⟨h.val, hPJ h.property, rfl⟩⟩, ?_⟩
  change rho h.val x ≠ x
  rw [hact]
  exact hh

theorem exists_move {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Sylow 2 (alternatingGroup Y)) (J : Subgroup (alternatingGroup Y))
    (hPJ : (P : Subgroup (alternatingGroup Y)) ≤ J)
    (hsize : 3 ≤ Nat.card Y) (heven : 2 ∣ Nat.card Y) (x : Y) :
    ∃ h : J.map (alternatingGroup Y).subtype, (h : Equiv.Perm Y) x ≠ x := by
  exact exists_move_map (alternatingGroup Y).subtype (fun _ _ => rfl)
    (P : Subgroup (alternatingGroup Y)) J hPJ x
    (CFSGAlternatingSylowNoFixedPoint.exists_move hsize heven P x)

end SymmetricSubgroupAsymptotics.CFSGAlternatingJoinMoves
