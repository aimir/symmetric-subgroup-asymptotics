import SymmetricSubgroupAsymptotics.ElevenCycleAlternatingNormalizer
import Mathlib.GroupTheory.Sylow

/-! A subgroup of order110 has a unique Sylow11 subgroup. Its generator
is an eleven-cycle in the actual twelve-point action, whose normalizer
cannot consist entirely of even permutations. -/
set_option autoImplicit false
noncomputable section
open Equiv
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- An even twelve-point permutation subgroup cannot have order110. -/
theorem no_even_twelvePoint_subgroup_order110
    (H : Subgroup (Perm (Fin 12))) (hcard : Nat.card H=110)
    (he : ∀ h∈H,Perm.sign h=1) : False := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P : Sylow 11 H := Classical.choice inferInstance
  have hP : Nat.card P=11 := by
    rw [P.card_eq_multiplicity,hcard]
    decide +kernel
  have hi : P.index=10 := by
    have hm := (P : Subgroup H).card_mul_index
    rw [hP,hcard] at hm
    omega
  have hd : Nat.card (Sylow 11 H)∣10 := by
    simpa only [hi] using P.card_dvd_index
  have hl : Nat.card (Sylow 11 H)≤10 := Nat.le_of_dvd (by decide) hd
  have hm := card_sylow_modEq_one 11 H
  change Nat.card (Sylow 11 H)%11=1%11 at hm
  have hone : Nat.card (Sylow 11 H)=1 := by omega
  letI : Subsingleton (Sylow 11 H) := (Nat.card_eq_one_iff_unique.mp hone).1
  letI : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  letI : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨u,hu⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic P)
  have huord : orderOf u=11 := (orderOf_eq_card_of_zpowers_eq_top hu).trans hP
  have hzu : Subgroup.zpowers (u : H)=(P : Subgroup H) := by
    calc
      Subgroup.zpowers (u : H)=(Subgroup.zpowers u).map (P : Subgroup H).subtype :=
        (MonoidHom.map_zpowers (P : Subgroup H).subtype u).symm
      _ = (⊤ : Subgroup P).map (P : Subgroup H).subtype := by rw [hu]
      _ = (P : Subgroup H) := by rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  let g : Perm (Fin 12) := (u : H).val
  have hg : orderOf g=11 := by
    change orderOf (H.subtype ((P : Subgroup H).subtype u))=11
    rw [orderOf_injective H.subtype Subtype.coe_injective,
      orderOf_injective (P : Subgroup H).subtype Subtype.coe_injective,huord]
  have hzg : Subgroup.zpowers g=(P : Subgroup H).map H.subtype := by
    exact (MonoidHom.map_zpowers H.subtype (u : H)).symm.trans
      (congrArg (Subgroup.map H.subtype) hzu)
  have hn : H≤Subgroup.normalizer (Subgroup.zpowers g : Set (Perm (Fin 12))) := by
    intro a ha
    rw [hzg]
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨v,hv,rfl⟩
    refine ⟨(⟨a,ha⟩ : H)*v*(⟨a,ha⟩ : H)⁻¹,?_,rfl⟩
    exact (inferInstance : (P : Subgroup H).Normal).conj_mem v hv ⟨a,ha⟩
  exact no_even_order110_elevenCycle_normalizer H hcard g hg hn he

end SymmetricSubgroupAsymptotics
