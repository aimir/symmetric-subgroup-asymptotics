import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Card

/-! Distinct actual normalizer-centre atoms have disjoint nonidentity
elements. Hence there are at most |Z(P)|-1 intrinsic local choices,
without classifying a group of order four or enumerating subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
variable {G : Type*} [Group G]

theorem centerImage_card (P : Subgroup G) :
    Nat.card (centerImage P) = Nat.card (Subgroup.center P) :=
  Nat.card_congr ((Subgroup.center P).equivMapOfInjective P.subtype Subtype.val_injective).symm.toEquiv

theorem eq_of_shared_nonidentity {P H J : Subgroup G} (hH : IsAtom P H) (hJ : IsAtom P J)
    {x : G} (hxH : x ∈ H) (hxJ : x ∈ J) (hx : x ≠ 1) : H = J := by
  have hne : H ⊓ J ≠ ⊥ := by
    intro h
    have hm : x ∈ H ⊓ J := ⟨hxH, hxJ⟩
    rw [h] at hm
    exact hx hm
  have hN : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((H ⊓ J : Subgroup G) : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg y hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hH.2.2.1 hg) y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp (hJ.2.2.1 hg) y).mp hy.2⟩
  exact (hH.2.2.2 _ hne inf_le_left hN).symm.trans (hJ.2.2.2 _ hne inf_le_right hN)

def atomChoice (P : Subgroup G) (a : {H : Subgroup G // IsAtom P H}) : a.val :=
  Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp a.property.1)

theorem atomChoice_ne_one (P : Subgroup G) (a : {H : Subgroup G // IsAtom P H}) :
    atomChoice P a ≠ 1 :=
  Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp a.property.1)

def atomNonidentity (P : Subgroup G) (a : {H : Subgroup G // IsAtom P H}) :
    {x : centerImage P // x ≠ 1} :=
  ⟨⟨(atomChoice P a).val, a.property.2.1 (atomChoice P a).property⟩, by
    intro h
    apply atomChoice_ne_one P a
    have hv : (atomChoice P a).val = 1 := congrArg (fun z : centerImage P => z.val) h
    exact Subtype.ext hv⟩

theorem atomNonidentity_injective (P : Subgroup G) : Function.Injective (atomNonidentity P) := by
  intro a b he
  apply Subtype.ext
  have hval := congrArg (fun x : {x : centerImage P // x ≠ 1} => x.val.val) he
  have hx : (atomChoice P a).val ≠ 1 := by
    intro h
    exact atomChoice_ne_one P a (Subtype.ext h)
  apply eq_of_shared_nonidentity a.property b.property (atomChoice P a).property ?_ hx
  rw [show (atomChoice P a).val = (atomChoice P b).val from hval]
  exact (atomChoice P b).property

theorem atom_card_le_center_sub_one [Finite G] (P : Subgroup G) :
    Nat.card {H : Subgroup G // IsAtom P H} ≤ Nat.card (centerImage P) - 1 := by
  classical
  have h := Nat.card_le_card_of_injective (atomNonidentity P) (atomNonidentity_injective P)
  have hc : Nat.card {x : centerImage P // x ≠ 1} = Nat.card (centerImage P) - 1 := by
    letI atomCount_centerFintype : Fintype (centerImage P) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : centerImage P => x = 1), Fintype.card_subtype_eq,
      Nat.card_eq_fintype_card]
  exact h.trans_eq hc

end SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
