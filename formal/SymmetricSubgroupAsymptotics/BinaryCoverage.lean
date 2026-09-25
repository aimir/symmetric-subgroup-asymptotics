import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Atoms.Finite

/-!
# Coverage from local finite p-group transitions

These statements justify the group-theoretic coverage steps of the binary
menu.  Every subgroup and conjugation remains in the original finite group;
no catalogue or checker verdict is a premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A nontrivial normal subgroup of a finite p-group contains an element
of order p central in the whole original group. -/
theorem pGroup_normal_contains_central_prime (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ∃ z : G, z ∈ N ∧ z ∈ Subgroup.center G ∧ orderOf z = p := by
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hdiv : p ∣ Nat.card N := (hG.to_subgroup N).card_eq_or_dvd.resolve_left
    (ne_of_gt Finite.one_lt_card)
  have hc := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdiv
      (show (1 : N) ∈ MulAction.fixedPoints (ConjAct G) N by
        intro g; simp)
  obtain ⟨x, hx, hxe⟩ := hc
  have hxc : (x : G) ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have h := congrArg Subtype.val (hx (ConjAct.toConjAct g))
    change g * (x : G) * g⁻¹ = (x : G) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  let C : Subgroup G := N ⊓ Subgroup.center G
  have hC : C ≠ ⊥ := by
    intro h
    have hxC : (x : G) ∈ C := ⟨x.property, hxc⟩
    rw [h] at hxC
    change (x : G) = 1 at hxC
    exact hxe (Subtype.ext hxC).symm
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC
  have hd : p ∣ Nat.card C := (hG.to_subgroup C).card_eq_or_dvd.resolve_left
    (ne_of_gt Finite.one_lt_card)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  exact ⟨z, z.property.1, z.property.2, by simpa only [Subgroup.orderOf_coe] using hz⟩

/-- Every maximal subgroup of a finite p-group has index p. -/
theorem pGroup_coatom_index (hG : IsPGroup p G)
    (H : Subgroup G) (hH : IsCoatom H) : H.index = p := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  haveI : H.Normal := Subgroup.NormalizerCondition.normal_of_coatom H
    Group.normalizerCondition_of_isNilpotent hH
  have hQ : IsPGroup p (G ⧸ H) := hG.to_quotient H
  have hcard : Nat.card (G ⧸ H) ≠ 1 := by
    intro hc
    exact hH.ne_top (Subgroup.index_eq_one.mp (H.index_eq_card.trans hc))
  have hd : p ∣ Nat.card (G ⧸ H) := hQ.card_eq_or_dvd.resolve_left hcard
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  let q := QuotientGroup.mk' H
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective H
  have hz0 : Subgroup.zpowers z ≠ ⊥ := by
    intro hh
    have he : z = 1 := by simpa [hh] using Subgroup.mem_zpowers z
    rw [he, orderOf_one] at hz
    exact (Fact.out : p.Prime).ne_one hz.symm
  have hlt : H < (Subgroup.zpowers z).comap q := by
    have hh := (Subgroup.comap_lt_comap_of_surjective hq).mpr
      (bot_lt_iff_ne_bot.mpr hz0)
    simpa [q] using hh
  have ht : Subgroup.zpowers z = ⊤ := by
    apply Subgroup.comap_injective hq
    simpa using hH.2 _ hlt
  rw [H.index_eq_card, ← Subgroup.card_top (G := G ⧸ H), ← ht, Nat.card_zpowers, hz]

/-- Every strict interval of normal subgroups contains the exact kind of
central order-p quotient step enumerated by the certificate. -/
theorem pGroup_normal_interval_step (hG : IsPGroup p G)
    (N L : Subgroup G) [N.Normal] [L.Normal] (hNL : N < L) :
    ∃ z : G ⧸ N, z ∈ Subgroup.center (G ⧸ N) ∧ orderOf z = p ∧
      N < (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ∧
      (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ≤ L := by
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  haveI : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hL : L.map q ≠ ⊥ := by
    intro hh
    have hle := Subgroup.map_le_iff_le_comap.mp (le_of_eq hh)
    have hle' : L ≤ N := by simpa [q] using hle
    exact hNL.not_ge hle'
  obtain ⟨z, hzL, hzc, hzp⟩ := pGroup_normal_contains_central_prime
    (hG.to_quotient N) (L.map q) hL
  have hz0 : Subgroup.zpowers z ≠ ⊥ := by
    intro hh
    have he : z = 1 := by simpa [hh] using Subgroup.mem_zpowers z
    rw [he, orderOf_one] at hzp
    exact (Fact.out : p.Prime).ne_one hzp.symm
  refine ⟨z, hzc, hzp, ?_, ?_⟩
  · have hh := (Subgroup.comap_lt_comap_of_surjective hq).mpr
      (bot_lt_iff_ne_bot.mpr hz0)
    simpa [q] using hh
  · have hh := Subgroup.comap_mono (f := q) (Subgroup.zpowers_le.mpr hzL)
    have hker : q.ker ≤ L := by simpa [q] using hNL.le
    simpa only [Subgroup.comap_map_eq_self hker] using hh

omit [Finite G] [Fact p.Prime] in
/-- Central cyclic quotient steps are normal in the original group and
have the claimed relative index. -/
theorem central_prime_preimage_properties (N : Subgroup G) [N.Normal]
    (z : G ⧸ N) (hzc : z ∈ Subgroup.center (G ⧸ N)) (hzp : orderOf z = p) :
    ((Subgroup.zpowers z).comap (QuotientGroup.mk' N)).Normal ∧
      N.relIndex ((Subgroup.zpowers z).comap (QuotientGroup.mk' N)) = p := by
  haveI : (Subgroup.zpowers z).Normal := by
    constructor
    intro x hx g
    have hxc := Subgroup.zpowers_le.mpr hzc hx
    simpa [Subgroup.mem_center_iff.mp hxc g, mul_assoc] using hx
  refine ⟨inferInstance, ?_⟩
  have hh := Subgroup.relIndex_ker
    (K := (Subgroup.zpowers z).comap (QuotientGroup.mk' N)) (QuotientGroup.mk' N)
  simpa [QuotientGroup.ker_mk',
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N),
    Nat.card_zpowers, hzp] using hh

/-- Closure under the literal central-prime children forces a supplied
normal-subgroup registry to be exhaustive. Completeness is the conclusion. -/
theorem pGroup_normal_registry_complete (hG : IsPGroup p G)
    (registry : Set (Subgroup G)) (hbot : ⊥ ∈ registry)
    (hnormal : ∀ N ∈ registry, N.Normal)
    (hchildren : ∀ N ∈ registry, ∀ _hN : N.Normal, ∀ z : G ⧸ N,
      z ∈ Subgroup.center (G ⧸ N) → orderOf z = p →
      (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ∈ registry)
    (L : Subgroup G) [L.Normal] : L ∈ registry := by
  classical
  let S : Set (Subgroup G) := {N | N ∈ registry ∧ N ≤ L}
  obtain ⟨N, _, hmax⟩ := (Set.toFinite S).exists_le_maximal
    (show (⊥ : Subgroup G) ∈ S from ⟨hbot, bot_le⟩)
  have hNr : N ∈ registry := hmax.1.1
  have hNL : N ≤ L := hmax.1.2
  haveI : N.Normal := hnormal N hNr
  by_cases heq : N = L
  · exact heq ▸ hNr
  · obtain ⟨z, hzc, hzp, hlt, hle⟩ := pGroup_normal_interval_step hG N L
      (lt_of_le_of_ne hNL heq)
    have hr := hchildren N hNr inferInstance z hzc hzp
    exact False.elim (hlt.not_ge (hmax.2 ⟨hr, hle⟩ hlt.le))

/-- A proper subgroup sits below a literal index-p child of any finite
p-group overgroup. No conjugacy-class enumeration is used. -/
theorem pGroup_subgroup_interval_step (U H : Subgroup G)
    (hU : IsPGroup p U) (hHU : H < U) :
    ∃ K : Subgroup G, H ≤ K ∧ K < U ∧ K.relIndex U = p := by
  have hH : H.subgroupOf U ≠ ⊤ := fun hh =>
    hHU.not_ge (Subgroup.subgroupOf_eq_top.mp hh)
  obtain ⟨K, hK, hHK⟩ :=
    (eq_top_or_exists_le_coatom (H.subgroupOf U)).resolve_left hH
  have hindex := pGroup_coatom_index hU K hK
  refine ⟨K.map U.subtype, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hHU.le hx⟩, hHK hx, rfl⟩
  · refine lt_of_le_of_ne (by rintro x ⟨y, _, rfl⟩; exact y.property) ?_
    intro hh
    have he := congrArg (Subgroup.comap U.subtype) hh
    simp only [Subgroup.comap_map_eq_self_of_injective U.subtype_injective] at he
    have he' : K = ⊤ := he.trans (Subgroup.subgroupOf_self U)
    exact hK.ne_top he'
  · simpa only [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective] using hindex

/-- Literal local index-p closure below a registered p-group covers every
admissible subgroup. Upward admissibility allows intransitive branches to
be omitted in the permutation-action application. -/
theorem pGroup_subgroup_registry_complete (U : Subgroup G) (hU : IsPGroup p U)
    (registry : Set (Subgroup G)) (hroot : U ∈ registry)
    (A : Subgroup G → Prop)
    (hup : ∀ H K, H ≤ K → A H → A K)
    (hchildren : ∀ V ∈ registry, V ≤ U → ∀ K : Subgroup G,
      K < V → K.relIndex V = p → A K → K ∈ registry)
    (H : Subgroup G) (hHU : H ≤ U) (hAH : A H) : H ∈ registry := by
  classical
  let S : Set (Subgroup G) := {V | V ∈ registry ∧ H ≤ V ∧ V ≤ U}
  obtain ⟨V, _, hmin⟩ := (Set.toFinite S).exists_le_minimal
    (show U ∈ S from ⟨hroot, hHU, le_rfl⟩)
  have hVr : V ∈ registry := hmin.1.1
  have hHV : H ≤ V := hmin.1.2.1
  have hVU : V ≤ U := hmin.1.2.2
  by_cases heq : H = V
  · exact heq ▸ hVr
  · obtain ⟨K, hHK, hKV, hidx⟩ := pGroup_subgroup_interval_step V H
      (hU.to_le hVU) (lt_of_le_of_ne hHV heq)
    have hKr := hchildren V hVr hVU K hKV hidx (hup H K hHK hAH)
    exact False.elim (hKV.not_ge (hmin.2 ⟨hKr, hHK, hKV.le.trans hVU⟩ hKV.le))

end SymmetricSubgroupAsymptotics
