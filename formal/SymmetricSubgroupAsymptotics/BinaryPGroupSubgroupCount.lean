import SymmetricSubgroupAsymptotics.BinaryPGroupExteriorComparison
import SymmetricSubgroupAsymptotics.GaussianCount

/-!
# Counting an actual finite binary group and its onto images

The central comparison theorem, with a trivial exterior, bounds every
subgroup of a group of order 2^u by the actual number of binary subspaces
in dimension u. Pullback through an onto map bounds all target subgroups;
it does not claim that their character ranks equal those of the preimages.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPGroupSubgroupCount

open BinaryPGroupExteriorComparison

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

private def removeUnit (G : Type*) [Group G] : (PUnit.{1} × G) ≃* G where
  toFun := Prod.snd
  invFun g := (PUnit.unit, g)
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem binary_subgroup_card (u : ℕ) :
    Nat.card (Subgroup (Binary u)) = binarySubspaceCount u := by
  let e : Submodule (ZMod 2) (Fin u → ZMod 2) ≃o Subgroup (Binary u) :=
    (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup
  exact Nat.card_congr e.toEquiv.symm

/-- No structural or counting hypothesis beyond the actual order. -/
theorem subgroup_card_le_binarySubspaceCount (B : Type*) [Group B] [Finite B]
    (u : ℕ) (hB : Nat.card B = 2^u) :
    Nat.card (Subgroup B) ≤ binarySubspaceCount u := by
  calc
    _ = Nat.card (Subgroup (PUnit.{1} × B)) :=
      (Nat.card_congr (removeUnit B).mapSubgroup.toEquiv).symm
    _ ≤ Nat.card (Subgroup (PUnit.{1} × Binary u)) := subgroup_card_le PUnit.{1} B u hB
    _ = Nat.card (Subgroup (Binary u)) :=
      Nat.card_congr (removeUnit (Binary u)).mapSubgroup.toEquiv
    _ = _ := binary_subgroup_card u

/-- This injection counts original target subgroups separately. Ranks and
annihilators of a target must still be measured on that target. -/
theorem onto_subgroup_card_le_binarySubspaceCount
    {B A : Type*} [Group B] [Finite B] [Group A]
    (β : B →* A) (hβ : Function.Surjective β)
    (u : ℕ) (hB : Nat.card B = 2^u) :
    Nat.card (Subgroup A) ≤ binarySubspaceCount u :=
  (Nat.card_le_card_of_injective (Subgroup.comap β)
    (Subgroup.comap_injective hβ)).trans
      (subgroup_card_le_binarySubspaceCount B u hB)

theorem onto_subfamily_card_le_binarySubspaceCount
    {B A : Type*} [Group B] [Finite B] [Group A]
    (β : B →* A) (hβ : Function.Surjective β)
    (u : ℕ) (hB : Nat.card B = 2^u) (P : Subgroup A → Prop) :
    Nat.card {H : Subgroup A // P H} ≤ binarySubspaceCount u := by
  letI : Finite A := Finite.of_surjective β hβ
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    (onto_subgroup_card_le_binarySubspaceCount β hβ u hB)

end SymmetricSubgroupAsymptotics.BinaryPGroupSubgroupCount
