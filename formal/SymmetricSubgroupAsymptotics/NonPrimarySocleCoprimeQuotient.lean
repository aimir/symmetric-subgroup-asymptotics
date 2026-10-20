import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles

/-! The non-p socle of a finite group with a normal p-kernel and a
coprime quotient is disjoint from that kernel. The quotient need not be
cyclic or soluble, and the selected minimal normal factors need not be
abelian. Their orders are coprime to p because each embeds in the quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace NonPrimarySocleCoprimeQuotient

private theorem finset_sup_normal
    {G : Type} [Group G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, M.Normal) :
    (S.sup (fun M : Subgroup G => M) : Subgroup G).Normal := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert M S hMS ih =>
      letI : M.Normal := hS M (Finset.mem_insert_self M S)
      letI : (S.sup (fun K : Subgroup G => K) : Subgroup G).Normal :=
        ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
      simpa only [Finset.sup_insert] using
        (inferInstance : (M ⊔ S.sup (fun K : Subgroup G => K)).Normal)

private theorem card_sup_eq_mul_of_minimal_not_le
    {G : Type} [Group G] [Finite G]
    (M K : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    [K.Normal] (hnot : ¬ M ≤ K) :
    Nat.card ↥(M ⊔ K) = Nat.card M * Nat.card K := by
  letI : M.Normal := hM.1
  have hinf : M ⊓ K = ⊥ := by
    by_contra hne
    have heq : M ⊓ K = M :=
      hM.2.2 (M ⊓ K) (inferInstance : (M ⊓ K).Normal)
        hne inf_le_left
    exact hnot (by rw [← heq]; exact inf_le_right)
  have hle : M ≤ M ⊔ K := le_sup_left
  have hcard := (M.subgroupOf (M ⊔ K)).card_mul_index
  have hsubcard : Nat.card (M.subgroupOf (M ⊔ K)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hindex : (M.subgroupOf (M ⊔ K)).index = Nat.card K := by
    change M.relIndex (M ⊔ K) = Nat.card K
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf,
      Subgroup.relIndex_bot_left]
  rw [hsubcard, hindex] at hcard
  exact hcard.symm


private theorem finset_sup_card_coprime
    {G : Type} [Group G] [Finite G] (p : ℕ)
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, IsMinimalNormalSubgroup M ∧ Nat.Coprime (Nat.card M) p) :
    Nat.Coprime (Nat.card ↥(S.sup (fun M : Subgroup G => M))) p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert M S hMS ih =>
      have hM := hS M (Finset.mem_insert_self M S)
      have hrest : ∀ K ∈ S, IsMinimalNormalSubgroup K ∧
          Nat.Coprime (Nat.card K) p := by
        intro K hK
        exact hS K (Finset.mem_insert_of_mem hK)
      letI : M.Normal := hM.1.1
      letI : (S.sup (fun K : Subgroup G => K) : Subgroup G).Normal :=
        finset_sup_normal S (fun K hK => (hrest K hK).1.1)
      by_cases hle : M ≤ S.sup (fun K : Subgroup G => K)
      · have heq := sup_eq_right.mpr hle
        simpa only [Finset.sup_insert, heq] using ih hrest
      · rw [Finset.sup_insert,
          card_sup_eq_mul_of_minimal_not_le M
            (S.sup (fun K : Subgroup G => K)) hM.1 hle]
        exact Nat.coprime_mul_iff_left.mpr ⟨hM.2, ih hrest⟩

/-- Finite joins of minimal normal factors with orders coprime to p
still have order coprime to p. No commutativity hypothesis is needed. -/
theorem selectedSocle_card_coprime
    {G : Type} [Group G] [Finite G] (p : ℕ) (P : Subgroup G → Prop)
    (hP : ∀ M, IsMinimalNormalSubgroup M → P M → Nat.Coprime (Nat.card M) p) :
    Nat.Coprime (Nat.card ↥(minimalNormalSoclePart G P)) p := by
  unfold minimalNormalSoclePart
  apply finset_sup_card_coprime
  intro M hM
  have hm := (Finset.mem_filter.mp hM).2
  exact ⟨hm.1, hP M hm.1 hm.2⟩

theorem minimalNormal_card_coprime
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E)))
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hnot : ¬ IsPGroup p M) : Nat.Coprime (Nat.card M) p := by
  letI : M.Normal := hM.1
  have hinf : M ⊓ E = ⊥ := by
    by_contra hne
    have heq := hM.2.2 (M ⊓ E) inferInstance hne inf_le_left
    apply hnot
    apply hE.to_le
    rw [← heq]
    exact inf_le_right
  have hinj := CoprimeCyclicQuotientSocles.quotientRestriction_injective E M hinf
  exact hcop.symm.of_dvd_left
    (Subgroup.card_dvd_of_injective ((QuotientGroup.mk' E).comp M.subtype) hinj)

theorem nonprimarySocle_card_coprime
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) :
    Nat.Coprime (Nat.card ↥(minimalNormalSoclePart G (fun M => ¬ IsPGroup p M))) p :=
  selectedSocle_card_coprime p _ (minimalNormal_card_coprime p E hE hcop)

theorem nonprimarySocle_inf_kernel_eq_bot
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ E))) :
    minimalNormalSoclePart G (fun M => ¬ IsPGroup p M) ⊓ E = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := hE (⟨x, hx.2⟩ : E)
    have hpow : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have hcard : orderOf x ∣ Nat.card
        ↥(minimalNormalSoclePart G (fun M => ¬ IsPGroup p M)) :=
      Subgroup.orderOf_dvd_natCard _ hx.1
    have hprimePow : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      ((nonprimarySocle_card_coprime p E hE hcop).pow_right k) hcard hprimePow
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  · exact bot_le

end NonPrimarySocleCoprimeQuotient
end SymmetricSubgroupAsymptotics

end
