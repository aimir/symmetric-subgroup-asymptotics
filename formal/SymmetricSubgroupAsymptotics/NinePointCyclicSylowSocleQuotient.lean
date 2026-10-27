import SymmetricSubgroupAsymptotics.NormalSubgroupSylowNormalizerIndex
import SymmetricSubgroupAsymptotics.TransitiveAbelianNormalizerDivisor
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive
import Mathlib.GroupTheory.Transfer
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! An ACTUAL transitive simple normal subgroup with cyclic Sylow3 of
order9 has ambient quotient order≤3 in a faithful nine-point action.
No model order, outer packet or original-ambient simplicity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NinePointCyclicSylowSocleQuotient
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem normalizer_card_ge_eighteen {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T]
    (hn : ¬IsMulCommutative T) (P : Sylow 3 T) [IsCyclic P]
    (hP : Nat.card P=9) :
    18≤Nat.card (Subgroup.normalizer (P : Set T)) := by
  have hNC : ¬Subgroup.normalizer (P : Set T)≤Subgroup.centralizer (P : Set T) := by
    intro hc
    let f := MonoidHom.transferSylow P hc
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hc
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · have htop : (P : Subgroup T)=⊤ := by
        have hh := hcompl.sup_eq_top
        change f.ker ⊔ (P : Subgroup T)=⊤ at hh
        simpa only [hb,bot_sup_eq] using hh
      have hT : Nat.card T=9 := by
        have hh : Nat.card P=Nat.card T := by rw [htop,Subgroup.card_top]
        exact hh.symm.trans hP
      exact hn (IsMulCommutative.of_comm
        (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by simpa using hT)))
    · have hh := MonoidHom.not_dvd_card_ker_transferSylow P hc
      change ¬3 ∣ Nat.card f.ker at hh
      rw [ht,Subgroup.card_top] at hh
      apply hh
      have hd := (P : Subgroup T).card_subgroup_dvd_card
      rw [hP] at hd
      exact (by decide : 3 ∣ 9).trans hd
  have hNne : Nat.card (Subgroup.normalizer (P : Set T))≠9 := by
    intro he
    have hPN : (P : Subgroup T)=Subgroup.normalizer (P : Set T) :=
      Subgroup.eq_of_le_of_card_ge (P : Subgroup T).le_normalizer (by rw [he,hP])
    exact hNC (hPN.symm.le.trans (P : Subgroup T).le_centralizer)
  have hd : 9 ∣ Nat.card (Subgroup.normalizer (P : Set T)) := by
    simpa only [hP] using Subgroup.card_dvd_of_le (P : Subgroup T).le_normalizer
  obtain ⟨k,hk⟩ := hd
  have hkpos : 0<k := by
    have hh : 0<Nat.card (Subgroup.normalizer (P : Set T)) := Nat.card_pos
    rw [hk] at hh
    omega
  have hk2 : 2≤k := by
    by_contra hh
    have hk1 : k=1 := by omega
    exact hNne (by simpa only [hk1,mul_one] using hk)
  rw [hk]
  omega

theorem quotient_card_le_three {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    [MulAction.IsPretransitive S (Fin 9)] (hn : ¬IsMulCommutative S)
    (P : Sylow 3 S) [IsCyclic P] (hP : Nat.card P=9) :
    Nat.card (G ⧸ S)≤3 := by
  letI : MulAction.IsPretransitive P (Fin 9) :=
    sylow_isPretransitive_of_card_eq_prime_pow (a := 2) P (by simp)
  let H : Subgroup G := P.map S.subtype
  have hH : Nat.card H=9 := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hP
  let e : P ≃* H := (P : Subgroup S).equivMapOfInjective S.subtype S.subtype_injective
  letI : IsCyclic H := isCyclic_of_surjective e.toMonoidHom e.surjective
  letI : MulAction.IsPretransitive H (Fin 9) := ⟨fun x y => by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P x y
    exact ⟨⟨(g.val : G),⟨g.val,g.property,rfl⟩⟩,hg⟩⟩
  let N := Subgroup.normalizer (H : Set G)
  let NS := Subgroup.normalizer (P : Set S)
  have hAut : Nat.card (MulAut H)=6 := by
    rw [IsCyclic.card_mulAut,hH]
    decide
  have hNdvd : Nat.card N ∣ 54 := by
    have hh := normalizer_card_dvd_degree_mul_aut_of_abelian_transitive
      (X := Fin 9) H (inferInstance : IsMulCommutative H)
    simpa only [Nat.card_fin,hAut] using hh
  have hNle : Nat.card N≤54 := Nat.le_of_dvd (by decide) hNdvd
  have hNS : 18≤Nat.card NS := normalizer_card_ge_eighteen hn P hP
  have hidx : N.index=NS.index := NormalSubgroupSylowNormalizerIndex.index_eq S P
  have hcard : Nat.card NS*Nat.card (G ⧸ S)=Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
    calc
      (Nat.card NS*Nat.card (G ⧸ S))*N.index =
          (Nat.card NS*NS.index)*Nat.card (G ⧸ S) := by rw [hidx]; ac_rfl
      _=Nat.card S*Nat.card (G ⧸ S) := by rw [NS.card_mul_index]
      _=Nat.card G := by simpa only [Subgroup.index_eq_card] using S.card_mul_index
      _=Nat.card N*N.index := N.card_mul_index.symm
  have hh := Nat.mul_le_mul_right (Nat.card (G ⧸ S)) hNS
  rw [hcard] at hh
  omega

/-- A displayed actual simple generating pair pays the full degree-nine
half-degree target in this cyclic-Sylow branch. This is an internal
conditional installer, not a new endpoint input. -/
theorem genRank_le_four_of_simple_rank_le_two {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    [MulAction.IsPretransitive S (Fin 9)] (hn : ¬IsMulCommutative S)
    (P : Sylow 3 S) [IsCyclic P] (hP : Nat.card P=9)
    (hhead : MarkedC4.genRank S≤2) : MarkedC4.genRank G≤4 := by
  have hcard := quotient_card_le_three S hn P hP
  have hQ : MarkedC4.genRank (G ⧸ S)≤2 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow _ 2
      (hcard.trans (by decide : 3≤2^2))
  have hG := MarkedC4.genRank_le_of_normal S
  omega

end SymmetricSubgroupAsymptotics.NinePointCyclicSylowSocleQuotient
