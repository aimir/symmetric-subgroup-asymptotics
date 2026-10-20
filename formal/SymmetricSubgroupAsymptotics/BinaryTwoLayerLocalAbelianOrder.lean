import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Linarith

/-! Every actual abelian subgroup of the four-point physical pair
stabilizer has order at most four. The ambient stabilizer has eight
elements, verified on 24 permutations; no subgroups are enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianOrder
open BinaryTwoLayerLocalClassTwo

private theorem inverse_preserves : ∀ a : Equiv.Perm Points,Preserves a → Preserves a⁻¹ := by
  simp only [preserves_iff_pairRows]
  unfold PairRows
  decide +kernel

def pairGroup : Subgroup (Equiv.Perm Points) where
  carrier := {a | Preserves a}
  one_mem' := by intro x y h; exact h
  mul_mem' := by
    intro a b ha hb x y h
    exact ha (b x) (b y) (hb x y h)
  inv_mem' := fun {a} ha => inverse_preserves a ha

instance pairGroupFintype : Fintype pairGroup :=
  Fintype.subtype (Finset.univ.filter Preserves) (by intro a; change (a ∈ Finset.univ.filter Preserves ↔ Preserves a); simp)

 theorem pairGroup_card : Nat.card pairGroup=8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem pairGroup_not_commutative :
    ¬∀ a b : pairGroup,a*b=b*a := by
  decide +kernel

 theorem card_le_four (L : Subgroup (Equiv.Perm Points))
    (hp : ∀ a : L,Preserves a.val) (hc : ∀ a b : L,a*b=b*a) : Nat.card L≤4 := by
  let f : L →* pairGroup := L.subtype.codRestrict pairGroup (by intro a; change Preserves a.val; exact hp a)
  have hi : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun z : pairGroup => (z : Equiv.Perm Points)) h)
  have he : Nat.card L≠8 := by
    intro hcard
    have hs : Function.Surjective f :=
      ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hcard.trans pairGroup_card.symm⟩).2
    apply pairGroup_not_commutative
    intro a b
    obtain ⟨x,rfl⟩ := hs a
    obtain ⟨y,rfl⟩ := hs b
    rw [←map_mul,←map_mul,hc]
  have hd : Nat.card L∣8 := by
    have hL : L≤pairGroup := by intro a ha; change Preserves a; exact hp ⟨a,ha⟩
    have hh := (L.subgroupOf pairGroup).card_subgroup_dvd_card
    have hEq : Nat.card (L.subgroupOf pairGroup)=Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL).toEquiv
    simpa only [hEq,pairGroup_card] using hh
  have hn : 0<Nat.card L := Nat.card_pos
  by_contra hnle
  have hn5 : 5≤Nat.card L := by omega
  obtain ⟨k,hk⟩ := hd
  have hkpos : 0<k := by nlinarith
  have hklt : k<2 := by
    by_contra h
    have hm := Nat.mul_le_mul hn5 (show 2≤k by omega)
    nlinarith
  have hk1 : k=1 := by omega
  exact he (by simpa only [hk1,mul_one] using hk.symm)

end SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianOrder
