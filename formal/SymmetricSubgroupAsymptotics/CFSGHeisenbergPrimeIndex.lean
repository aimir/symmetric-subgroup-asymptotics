import SymmetricSubgroupAsymptotics.CFSGHeisenbergSymplecticQuotient
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCentralIsotropy
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Finiteness

/-! A proper intersection with the actual prime-order centre forces an
index of at least p^(m+1). The vector image is a literal additive subgroup,
not an assumed linear subgroup over a larger coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSymplecticQuotient
variable (p:ℕ) [Fact p.Prime] (m:ℕ)

private theorem prime_tag_card : Nat.card (Multiplicative (ZMod p))=p :=
  (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p)≃ZMod p)).trans (Nat.card_zmod p)

def vectorImage (H:Subgroup (Element (ZMod p) m)) :
    AddSubgroup ((Fin m→ZMod p)×(Fin m→ZMod p)) :=
  (H.map projection).toAddSubgroup'

def centralPreimage (H:Subgroup (Element (ZMod p) m)) :
    Subgroup (Multiplicative (ZMod p)) := H.comap central

theorem centralPreimage_eq_bot (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H) : centralPreimage p m H=⊥ := by
  letI : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
    ⟨by rw [prime_tag_card]; exact Fact.out⟩
  rcases (centralPreimage p m H).eq_bot_or_eq_top_of_prime_card with hb|ht
  · exact hb
  · exfalso
    apply hH
    rintro g ⟨z,rfl⟩
    have hz:z∈centralPreimage p m H := by rw [ht]; trivial
    exact hz

theorem vectorImage_pairing_zero (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H)
    (v: (Fin m→ZMod p)×(Fin m→ZMod p)) (hv:v∈vectorImage p m H)
    (w: (Fin m→ZMod p)×(Fin m→ZMod p)) (hw:w∈vectorImage p m H) :
    pairing v w=0 := by
  change Multiplicative.ofAdd v∈H.map projection at hv
  change Multiplicative.ofAdd w∈H.map projection at hw
  obtain ⟨g,hg,hgv⟩ := hv
  obtain ⟨h,hh,hhw⟩ := hw
  have hgv' : (g.a,g.b)=v := congrArg Multiplicative.toAdd hgv
  have hhw' : (h.a,h.b)=w := congrArg Multiplicative.toAdd hhw
  have hc : central (Multiplicative.ofAdd (pairing v w))∈H := by
    rw [←hgv',←hhw',←commutator_eq_pairing]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)
  have hb : Multiplicative.ofAdd (pairing v w)∈centralPreimage p m H := hc
  rw [centralPreimage_eq_bot p m H hH] at hb
  exact congrArg Multiplicative.toAdd hb

theorem vectorImage_finrank_le (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H) :
    Module.finrank (ZMod p) (AddSubgroup.toZModSubmodule p (vectorImage p m H))≤m := by
  have ht := CFSGHeisenbergCentralIsotropy.additive_twice_finrank_le p pairing
    pairing_alt (fun v hv=>pairing_full v hv) (⊥:AddSubgroup (ZMod p))
    (by intro he; have h: (1:ZMod p)∈(⊥:AddSubgroup (ZMod p)) := by rw [he]; trivial
        exact one_ne_zero h)
    (vectorImage p m H) (fun v hv w hw=>vectorImage_pairing_zero p m H hH v hv w hw)
  rw [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at ht
  omega

theorem vectorImage_card_le (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H) :
    Nat.card (vectorImage p m H)≤p^m := by
  let L:=AddSubgroup.toZModSubmodule p (vectorImage p m H)
  have hc : Nat.card (vectorImage p m H)=p^Module.finrank (ZMod p) L := by
    change Nat.card L=_
    rw [Module.natCard_eq_pow_finrank (K:=ZMod p),Nat.card_zmod]
  rw [hc]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (vectorImage_finrank_le p m H hH)

theorem subgroup_card_le (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H) : Nat.card H≤p^m := by
  let f : H→vectorImage p m H := fun g=>⟨(g.val.a,g.val.b),⟨g.val,g.property,rfl⟩⟩
  have hf : Function.Injective f := by
    intro g h he
    have he' : projection g.val=projection h.val :=
      congrArg Multiplicative.ofAdd (congrArg Subtype.val he)
    have hk : g.val*h.val⁻¹∈(projection (K:=ZMod p) (m:=m)).ker := by
      change projection (g.val*h.val⁻¹)=1
      rw [map_mul,map_inv,he',mul_inv_cancel]
    let z := (kernelChart (K:=ZMod p) (m:=m)).symm ⟨g.val*h.val⁻¹,hk⟩
    have hz : central z=g.val*h.val⁻¹ :=
      congrArg Subtype.val ((kernelChart (K:=ZMod p) (m:=m)).apply_symm_apply ⟨g.val*h.val⁻¹,hk⟩)
    have hzH : z∈centralPreimage p m H := by
      change central z∈H
      rw [hz]
      exact H.mul_mem g.property (H.inv_mem h.property)
    rw [centralPreimage_eq_bot p m H hH] at hzH
    have hgh : g.val*h.val⁻¹=1 := hz.symm.trans (congrArg central hzH |>.trans (map_one central))
    exact Subtype.ext (mul_inv_eq_one.mp hgh)
  exact (Nat.card_le_card_of_injective f hf).trans (vectorImage_card_le p m H hH)

theorem index_least (H:Subgroup (Element (ZMod p) m))
    (hH:¬(central (K:=ZMod p) (m:=m)).range≤H) : p^(m+1)≤H.index := by
  have hp := (Fact.out : p.Prime).pos
  have hcard := subgroup_card_le p m H hH
  have heq := H.card_mul_index
  rw [card,Nat.card_zmod] at heq
  apply Nat.le_of_mul_le_mul_left _ (pow_pos hp m)
  calc
    p^m*p^(m+1)=p^(2*m+1) := by rw [←pow_add];congr 1;omega
    _=Nat.card H*H.index := heq.symm
    _≤p^m*H.index := Nat.mul_le_mul_right _ hcard

end SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeIndex
