import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import Mathlib.GroupTheory.Index

/-! Normal factors of coprime order share generator slots. Their
common normal quotient is trivial by its actual order; the checked
paired-normal-generator construction therefore costs a maximum. In a
nilpotent group normal generation is ordinary generation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoprimeNormalGeneratorSharing

theorem noCommonNormalQuotient_of_coprime {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    NoCommonNormalQuotient A B := by
  intro H hH hle hHA hHB
  letI : H.Normal := hH
  let q : G→*G⧸H := QuotientGroup.mk' H
  have hHq : H.map q=⊥ := by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hA : A.map q=(A⊔B).map q := by
    calc
      _=(H⊔A).map q := by rw [Subgroup.map_sup,hHq,bot_sup_eq]
      _=(A⊔B).map q := congrArg (fun K:Subgroup G=>K.map q) hHA
  have hB : B.map q=(A⊔B).map q := by
    calc
      _=(H⊔B).map q := by rw [Subgroup.map_sup,hHq,bot_sup_eq]
      _=(A⊔B).map q := congrArg (fun K:Subgroup G=>K.map q) hHB
  have hAB : A.map q=B.map q := hA.trans hB.symm
  have hdA : Nat.card (A.map q)∣Nat.card A :=
    Subgroup.card_dvd_of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)
  have hdB : Nat.card (A.map q)∣Nat.card B := by
    rw [hAB]
    exact Subgroup.card_dvd_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  have hbotA : A.map q=⊥ :=
    (A.map q).eq_bot_of_card_eq (Nat.eq_one_of_dvd_coprimes hcop hdA hdB)
  have hbotB : B.map q=⊥ := hAB.symm.trans hbotA
  have hAH : A≤H := by
    intro x hx
    have hh : q x∈A.map q := ⟨x,hx,rfl⟩
    rw [hbotA] at hh
    exact (QuotientGroup.eq_one_iff x).mp hh
  have hBH : B≤H := by
    intro x hx
    have hh : q x∈B.map q := ⟨x,hx,rfl⟩
    rw [hbotB] at hh
    exact (QuotientGroup.eq_one_iff x).mp hh
  exact le_antisymm hle (sup_le hAH hBH)

theorem normalGen_sup_le_max {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] [B.Normal]
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    MarkedC4.normalGen (A⊔B)≤ max (MarkedC4.normalGen A) (MarkedC4.normalGen B) :=
  normalGen_sup_le_max_of_noCommonNormalQuotient A B
    (noCommonNormalQuotient_of_coprime A B hcop)

private theorem top_normalGen_le_genRank (G : Type) [Group G] [Finite G] :
    MarkedC4.normalGen (⊤:Subgroup G)≤MarkedC4.genRank G := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  have hnormal : Subgroup.normalClosure (S:Set G)=⊤ := by
    apply top_unique
    rw [←hgen]
    exact Subgroup.closure_le_normalClosure
  exact (MarkedC4.normalGen_le (N:=⊤) (s:=S) (by intro x hx; trivial) hnormal).trans_eq hS

theorem nilpotent_genRank_le_max_of_normal_join {G : Type} [Group G] [Finite G]
    [Group.IsNilpotent G] (A B : Subgroup G) [A.Normal] [B.Normal]
    (hjoin : A⊔B=⊤) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    MarkedC4.genRank G≤ max (MarkedC4.genRank A) (MarkedC4.genRank B) := by
  have hA : MarkedC4.normalGen A≤MarkedC4.genRank A :=
    (MarkedC4.normalGen_normalSubgroup_le_internal A).trans (top_normalGen_le_genRank A)
  have hB : MarkedC4.normalGen B≤MarkedC4.genRank B :=
    (MarkedC4.normalGen_normalSubgroup_le_internal B).trans (top_normalGen_le_genRank B)
  calc
    MarkedC4.genRank G≤MarkedC4.normalGen (⊤:Subgroup G) := MarkedC4.genRank_le_normalGen_top
    _=MarkedC4.normalGen (A⊔B) := congrArg MarkedC4.normalGen hjoin.symm
    _≤ max (MarkedC4.normalGen A) (MarkedC4.normalGen B) := normalGen_sup_le_max A B hcop
    _≤ max (MarkedC4.genRank A) (MarkedC4.genRank B) := max_le_max hA hB

end SymmetricSubgroupAsymptotics.CoprimeNormalGeneratorSharing
