import SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! A central quotient of order four has a derived subgroup of order at
most two. This controls quotient centres when a rank-preserving binary
quotient has only a small derived subgroup; no group catalogue is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem commute_of_center_coset_eq (a b : G)
    (h : (QuotientGroup.mk' (Subgroup.center G)) a =
      (QuotientGroup.mk' (Subgroup.center G)) b) : a*b=b*a := by
  have hz : a/b∈Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp h
  have hh := congrArg (fun t : G => t*b) ((Subgroup.mem_center_iff.mp hz) b)
  simpa only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one] using hh.symm

theorem commutator_card_le_two_of_center_index_four
    (hi : (Subgroup.center G).index=4)
    (hnonab : ¬∀ a b : G,a*b=b*a) : Nat.card (commutator G)≤2 := by
  classical
  let Z := Subgroup.center G
  let T := G ⧸ Z
  let q := QuotientGroup.mk' Z
  have hT : Nat.card T=4 := hi
  have hcyc : ¬IsCyclic T := by
    intro hc
    letI := hc
    exact hnonab (commutative_of_cyclic_center_quotient q (by
      intro x hx
      exact (QuotientGroup.eq_one_iff x).mp hx))
  letI : IsKleinFour T := {
    card_four := hT
    exponent_two := (not_isCyclic_iff_exponent_eq_prime Nat.prime_two
      (by simpa using hT)).mp hcyc }
  push Not at hnonab
  obtain ⟨a,b,hab⟩ := hnonab
  have ha : q a≠1 := by
    intro h
    exact hab ((Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff a).mp h)) b).symm
  have hb : q b≠1 := by
    intro h
    exact hab ((Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff b).mp h)) a)
  have habq : q a≠q b := fun h => hab (commute_of_center_coset_eq a b h)
  letI : Fintype T := Fintype.ofFinite T
  have hcover (g : G) : q g=q (a*b) ∨ q g=q a ∨ q g=q b ∨ q g=1 := by
    have hu := IsKleinFour.eq_finset_univ ha hb habq
    have hm : q g∈({q a*q b,q a,q b,1} : Finset T) := by rw [hu]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton,←map_mul] using hm
  have hcomm : commutator G≤Z := by
    letI : IsMulCommutative T := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun t => orderOf_dvd_iff_pow_eq_one.mpr
        (by simpa only [←pow_two] using IsKleinFour.mul_self t)) x y).eq⟩⟩
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  let c := ⁅a,b⁆
  have hcZ : c∈Z := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have ha2 : a^2∈Z := (QuotientGroup.eq_one_iff _).mp (by
    change q (a^2)=1
    rw [map_pow]
    simpa only [pow_two] using IsKleinFour.mul_self (q a))
  have hc2 : c^2=1 := by
    have hz : ⁅a*a,b⁆=1 := (commutatorElement_eq_one_iff_mul_comm).mpr
      ((Subgroup.mem_center_iff.mp (by simpa only [pow_two] using ha2)) b).symm
    rw [commutatorElement_mul_left_eq_conj_mul] at hz
    have hca := (Subgroup.mem_center_iff.mp hcZ) a
    change (a*c*a⁻¹)*c=1 at hz
    rw [hca] at hz
    simp only [mul_assoc, mul_inv_cancel, one_mul] at hz
    exact (pow_two c).trans hz
  let C := Subgroup.zpowers c
  have hCZ : C≤Z := Subgroup.zpowers_le.mpr hcZ
  letI : C.Normal := ⟨fun x hx g => by
    simpa only [(Subgroup.mem_center_iff.mp (hCZ hx)) g,
      mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  let r := QuotientGroup.mk' C
  let S : Set G := (Z : Set G)∪{a,b}
  have hS : Subgroup.closure S=⊤ := by
    apply top_unique
    intro g _
    have hrep (t : G) (ht : t∈Subgroup.closure S) (he : q g=q t) :
        g∈Subgroup.closure S := by
      have hz : g/t∈Z := QuotientGroup.eq_iff_div_mem.mp he
      have hm : g/t∈Subgroup.closure S := Subgroup.subset_closure (Or.inl hz)
      simpa only [div_mul_cancel] using (Subgroup.closure S).mul_mem hm ht
    have ham : a∈Subgroup.closure S := Subgroup.subset_closure (Or.inr (by simp))
    have hbm : b∈Subgroup.closure S := Subgroup.subset_closure (Or.inr (by simp))
    rcases hcover g with h | h | h | h
    · exact hrep (a*b) ((Subgroup.closure S).mul_mem ham hbm) h
    · exact hrep a ham h
    · exact hrep b hbm h
    · exact hrep 1 (Subgroup.one_mem _) (by simpa only [map_one] using h)
  have hrcenter (z : G) (hz : z∈Z) (g : G) : r z*r g=r g*r z := by
    simpa only [←map_mul] using congrArg r ((Subgroup.mem_center_iff.mp hz) g).symm
  have hrab : r a*r b=r b*r a := commutatorElement_eq_one_iff_mul_comm.mp (by
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers c))
  have hscomm : IsMulCommutative (Subgroup.closure (r '' S)) :=
    Subgroup.isMulCommutative_closure (by
      rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
      rcases hu with hu | hu
      · exact hrcenter u hu v
      · rcases hv with hv | hv
        · exact (hrcenter v hv u).symm
        · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · rfl
          · exact hrab
          · exact hrab.symm
          · rfl)
  have hrtop : Subgroup.closure (r '' S)=⊤ := by
    rw [←MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective r (QuotientGroup.mk'_surjective C)
  rw [hrtop] at hscomm
  have hrcomm : IsMulCommutative (G ⧸ C) := ⟨⟨fun x y =>
    congrArg Subtype.val (hscomm.is_comm.comm (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup (G ⧸ C)))
      (⟨y,Subgroup.mem_top y⟩ : (⊤ : Subgroup (G ⧸ C))))⟩⟩
  have hDC : commutator G≤C := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hrcomm
  exact (Subgroup.card_le_of_le hDC).trans (by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by decide : 0<2) hc2)

/-- The centre and derived group cannot independently attain their coarse
small-order bounds. This statement concerns the same actual group. -/
theorem center_double_card_le_abelianization_card_of_small_derived
    (hG : IsPGroup 2 G) (hd : Nat.card (commutator G)≤4)
    (hnonab : ¬∀ a b : G,a*b=b*a) :
    2*Nat.card (Subgroup.center G)≤Nat.card (Abelianization G) := by
  have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
  have hz := (Subgroup.center G).card_mul_index
  have hg := (commutator G).card_eq_card_quotient_mul_card_subgroup
  change Nat.card G=Nat.card (Abelianization G)*Nat.card (commutator G) at hg
  by_cases htwo : Nat.card (commutator G)≤2
  · nlinarith
  · have hieight : 8≤(Subgroup.center G).index := by
      obtain ⟨k,hk⟩ := (hG.to_quotient (Subgroup.center G)).exists_card_eq
      change (Subgroup.center G).index=2^k at hk
      have hk3 : 3≤k := by
        by_contra hn
        have hs : k≤2 := by omega
        have hle : (Subgroup.center G).index≤4 := by
          rw [hk]
          exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hs
        have hfour : (Subgroup.center G).index=4 := by omega
        exact htwo (commutator_card_le_two_of_center_index_four hfour hnonab)
      rw [hk]
      exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hk3
    nlinarith

theorem center_card_le_sixteen_of_small_derived
    (hG : IsPGroup 2 G) (hd : Nat.card (commutator G)≤4)
    (ha : Nat.card (Abelianization G)≤32)
    (hnonab : ¬∀ a b : G,a*b=b*a) : Nat.card (Subgroup.center G)≤16 := by
  have h := center_double_card_le_abelianization_card_of_small_derived hG hd hnonab
  omega

end SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
