import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
import Mathlib.SetTheory.Cardinal.Finite

/-! The intrinsic local atom sets themselves are equivalent under
the same actual group isomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
variable {G G' : Type*} [Group G] [Group G']

theorem map_isAtom_iff (f : G ≃* G') (P H : Subgroup G) :
    IsAtom (P.map f.toMonoidHom) (H.map f.toMonoidHom) ↔ IsAtom P H := by
  constructor
  · intro h
    have hh := map_isAtom f.symm _ _ h
    have hP : (P.map f.toMonoidHom).map f.symm.toMonoidHom = P := f.mapSubgroup.symm_apply_apply P
    have hH : (H.map f.toMonoidHom).map f.symm.toMonoidHom = H := f.mapSubgroup.symm_apply_apply H
    rwa [hP, hH] at hh
  · exact map_isAtom f P H

def atomEquiv (f : G ≃* G') (P : Subgroup G) :
    {H : Subgroup G // IsAtom P H} ≃
      {H : Subgroup G' // IsAtom (P.map f.toMonoidHom) H} :=
  Equiv.subtypeEquiv f.mapSubgroup.toEquiv (fun H => (map_isAtom_iff f P H).symm)

theorem atom_card_map (f : G ≃* G') (P : Subgroup G) :
    Nat.card {H : Subgroup G' // IsAtom (P.map f.toMonoidHom) H} =
      Nat.card {H : Subgroup G // IsAtom P H} :=
  Nat.card_congr (atomEquiv f P).symm

end SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
