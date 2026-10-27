import SymmetricSubgroupAsymptotics.SylowNormalizerImageLift
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index

/-! Frattini's argument identifies the ambient index of a Sylow
normalizer with its original normal-subgroup index. Actual subgroup and
quotient maps are retained; no splitting or group-order table is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalSubgroupSylowNormalizerIndex

theorem index_eq_of_sup_eq_top {G : Type} [Group G] [Finite G]
    (S : Subgroup G) [S.Normal] (N : Subgroup G) (hsup : N ⊔ S=⊤) :
    N.index=(N.subgroupOf S).index := by
  let NS := N.subgroupOf S
  have hcomap : N.subgroupOf S=NS := rfl
  let pi := QuotientGroup.mk' S
  let beta : N →* (G ⧸ S) := pi.comp N.subtype
  have hS0 : S.map pi=⊥ := by
    apply (Subgroup.map_eq_bot_iff S).mpr
    exact (QuotientGroup.ker_mk' S).ge
  have hmap : N.map pi=⊤ := by
    have hh := congrArg (fun K : Subgroup G => K.map pi) hsup
    change (N ⊔ S).map pi = (⊤ : Subgroup G).map pi at hh
    rw [Subgroup.map_sup,hS0,sup_bot_eq,
      Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective S)] at hh
    exact hh
  have hsurj : Function.Surjective beta := by
    intro z
    have hz : z ∈ N.map pi := by rw [hmap]; trivial
    obtain ⟨g,hg,he⟩ := hz
    exact ⟨⟨g,hg⟩,he⟩
  let e : beta.ker ≃* NS := {
    toFun := fun z => ⟨⟨z.val.val,by
      exact (QuotientGroup.eq_one_iff z.val.val).mp z.property⟩,by
        rw [←hcomap]
        exact z.val.property⟩
    invFun := fun s => ⟨⟨s.val.val,by
      have hs : s.val ∈ N.subgroupOf S := by rw [hcomap]; exact s.property
      exact hs⟩,by
        exact (QuotientGroup.eq_one_iff s.val.val).mpr s.val.property⟩
    left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro s; apply Subtype.ext; apply Subtype.ext; rfl
    map_mul' := by intro x y; apply Subtype.ext; apply Subtype.ext; rfl }
  have hN : Nat.card NS*Nat.card (G ⧸ S)=Nat.card N := by
    have hh := beta.ker.card_mul_index
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hsurj,Subgroup.card_top,
      Nat.card_congr e.toEquiv] at hh
    exact hh
  have hS : Nat.card S*Nat.card (G ⧸ S)=Nat.card G := by
    simpa only [Subgroup.index_eq_card] using S.card_mul_index
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card N from Nat.card_pos)
  calc
    Nat.card N*N.index=Nat.card G := N.card_mul_index
    _=Nat.card S*Nat.card (G ⧸ S) := hS.symm
    _=(Nat.card NS*NS.index)*Nat.card (G ⧸ S) := by rw [NS.card_mul_index]
    _=(Nat.card NS*Nat.card (G ⧸ S))*NS.index := by ac_rfl
    _=Nat.card N*NS.index := by rw [hN]

theorem index_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Subgroup G) [S.Normal] (P : Sylow p S) :
    (Subgroup.normalizer ((P.map S.subtype : Subgroup G) : Set G)).index =
      (Subgroup.normalizer (P : Set S)).index := by
  have hQS : P.map S.subtype≤S := by
    rintro x ⟨s,hs,rfl⟩
    exact s.property
  rw [index_eq_of_sup_eq_top S _ (Sylow.normalizer_sup_eq_top P),
    Subgroup.subgroupOf_normalizer_eq hQS]
  rw [←Subgroup.comap_subtype,Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  rfl

end SymmetricSubgroupAsymptotics.NormalSubgroupSylowNormalizerIndex
