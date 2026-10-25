import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Index

/-! Class bounds for the SAME proper subnormal subgroup across an actual
simple normal subgroup. The restricted quotient kernel is the actual
intersection, and a full intersection forces a proper quotient image.
No splitting, almost-simple recognition, or model class bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ProperSubnormalSimpleExtensionClassBound

variable {G : Type*} [Group G]

def restrictionKernelEquiv (S N : Subgroup G) [S.Normal] :
    ((QuotientGroup.mk' S).comp N.subtype).ker ≃* N.subgroupOf S where
  toFun x := ⟨⟨x.val.val, (QuotientGroup.eq_one_iff x.val.val).mp x.property⟩,
    x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, (QuotientGroup.eq_one_iff x.val.val).mpr x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem proper_subgroup_twice_card_le [Finite G] (N : Subgroup G) (hN : N ≠ ⊤) :
    2 * Nat.card N ≤ Nat.card G := by
  have hi : 2 ≤ N.index := N.one_lt_index_of_ne_top hN
  calc
    2 * Nat.card N = Nat.card N * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card N * N.index := Nat.mul_le_mul_left _ hi
    _ = Nat.card G := N.card_mul_index

private theorem two_le_class_card {S : Type*} [Group S] [Finite S] [Nontrivial S] :
    2 ≤ Nat.card (ConjClasses S) := by
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hc : ConjClasses.mk s ≠ ConjClasses.mk (1 : S) := by
    intro h
    exact hs (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  letI : Nontrivial (ConjClasses S) := ⟨⟨ConjClasses.mk s, ConjClasses.mk 1, hc⟩⟩
  have hp : 1 < Nat.card (ConjClasses S) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

theorem twice_class_card_le_quotient_mul_simple [Finite G]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    (N : Subgroup G) (hN : N.IsSubnormal) (hne : N ≠ ⊤) :
    2 * Nat.card (ConjClasses N) ≤ Nat.card (G ⧸ S) * Nat.card (ConjClasses S) := by
  let f := (QuotientGroup.mk' S).comp N.subtype
  let e := restrictionKernelEquiv S N
  have htwo : 2 ≤ Nat.card (ConjClasses S) := two_le_class_card
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup S)
      (hN.subgroupOf : (N.subgroupOf S).IsSubnormal) with hzero | hfull
  · have hkcard : Nat.card f.ker = 1 := by
      calc
        Nat.card f.ker = Nat.card (N.subgroupOf S) := Nat.card_congr e.toEquiv
        _ = 1 := by rw [hzero]; exact Nat.card_unique
    have hk : Nat.card (ConjClasses f.ker) ≤ 1 := by
      have hh := Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _) ConjClasses.mk_surjective
      simpa only [hkcard] using hh
    have hR : Nat.card (ConjClasses f.range) ≤ Nat.card (G ⧸ S) :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.range _) ConjClasses.mk_surjective).trans
        (Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective)
    have hc : Nat.card (ConjClasses N) ≤ Nat.card (G ⧸ S) :=
      (conjugacyClass_card_le_kernel_mul_range f).trans
        ((Nat.mul_le_mul hk hR).trans_eq (Nat.one_mul _))
    calc
      2 * Nat.card (ConjClasses N) ≤ 2 * Nat.card (G ⧸ S) := Nat.mul_le_mul_left 2 hc
      _ = Nat.card (G ⧸ S) * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card (G ⧸ S) * Nat.card (ConjClasses S) := Nat.mul_le_mul_left _ htwo
  · let eS : f.ker ≃* S := e.trans ((MulEquiv.subgroupCongr hfull).trans Subgroup.topEquiv)
    have hkcard : Nat.card f.ker = Nat.card S := Nat.card_congr eS.toEquiv
    have hkclass : Nat.card (ConjClasses f.ker) = Nat.card (ConjClasses S) :=
      Nat.le_antisymm
        (Nat.card_le_card_of_surjective (ConjClasses.map eS.symm.toMonoidHom)
          (ConjClasses.map_surjective eS.symm.surjective))
        (Nat.card_le_card_of_surjective (ConjClasses.map eS.toMonoidHom)
          (ConjClasses.map_surjective eS.surjective))
    have hRproper : f.range ≠ ⊤ := by
      intro htop
      apply hne
      apply N.eq_top_of_card_eq
      have hc := f.ker.card_mul_index
      rw [Subgroup.index_ker] at hc
      have hr : Nat.card f.range = Nat.card (G ⧸ S) := by
        rw [htop]
        exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ S)) ≃* (G ⧸ S)).toEquiv
      rw [hkcard, hr] at hc
      have hG : Nat.card S * Nat.card (G ⧸ S) = Nat.card G := S.card_mul_index
      exact hc.symm.trans hG
    have hRtwo : 2 * Nat.card f.range ≤ Nat.card (G ⧸ S) :=
      proper_subgroup_twice_card_le f.range hRproper
    have hRclass : Nat.card (ConjClasses f.range) ≤ Nat.card f.range :=
      Nat.card_le_card_of_surjective (@ConjClasses.mk f.range _) ConjClasses.mk_surjective
    have hc : Nat.card (ConjClasses N) ≤ Nat.card (ConjClasses S) * Nat.card f.range := by
      have hh := conjugacyClass_card_le_kernel_mul_range f
      rw [hkclass] at hh
      exact hh.trans (Nat.mul_le_mul_left _ hRclass)
    calc
      2 * Nat.card (ConjClasses N) ≤ 2 * (Nat.card (ConjClasses S) * Nat.card f.range) :=
        Nat.mul_le_mul_left 2 hc
      _ = Nat.card (ConjClasses S) * (2 * Nat.card f.range) := by ac_rfl
      _ ≤ Nat.card (ConjClasses S) * Nat.card (G ⧸ S) := Nat.mul_le_mul_left _ hRtwo
      _ = Nat.card (G ⧸ S) * Nat.card (ConjClasses S) := Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.ProperSubnormalSimpleExtensionClassBound
