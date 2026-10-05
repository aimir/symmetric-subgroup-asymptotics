import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-!
# Abelian socle factors away from one prime

The sum of the ambient abelian minimal normal subgroups whose characteristic
is not `p` has order coprime to `p`.  Consequently it is disjoint from every
ambient normal `p`-subgroup.  This is an intrinsic finite-group statement:
no catalogue of the simple or elementary factors is used.

The proof chooses the already-proved elementary prime-field chart on each
abelian minimal normal factor.  Independent factors multiply cardinalities;
redundant factors do not change the selected sum.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

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

/-- An abelian ambient minimal normal subgroup which is not a `p`-group has
order coprime to `p`. -/
theorem abelianMinimalNormal_card_coprime_of_not_isPGroup
    {G : Type} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hcomm : IsMulCommutative M) (hnot : ¬ IsPGroup p M) :
    Nat.Coprime (Nat.card M) p := by
  letI : M.Normal := hM.1
  let C := Classical.choice (elementaryMinimalNormalChart_nonempty M
    hM.2.1 hcomm (fun K hK hKM => by
      by_cases hbot : K = ⊥
      · exact Or.inl hbot
      · exact Or.inr (hM.2.2 K hK hbot hKM)))
  have hcard : Nat.card M =
      C.p ^ Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card M = Nat.card (Multiplicative C.V) :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card C.V := Nat.card_congr Multiplicative.toAdd
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hne : C.p ≠ p := by
    intro hp
    apply hnot
    apply IsPGroup.of_card
      (n := Module.finrank (ZMod C.p) C.V)
    simpa only [hp] using hcard
  rw [hcard]
  exact ((Nat.coprime_primes C.p_prime (Fact.out : p.Prime)).2 hne).pow_left _

private theorem finset_sup_abelian_nonprimary_card_coprime
    {G : Type} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, IsMinimalNormalSubgroup M ∧
      IsMulCommutative M ∧ ¬ IsPGroup p M) :
    Nat.Coprime
      (Nat.card ↥(S.sup (fun M : Subgroup G => M))) p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert M S hMS ih =>
      have hM := hS M (Finset.mem_insert_self M S)
      have hrest : ∀ K ∈ S, IsMinimalNormalSubgroup K ∧
          IsMulCommutative K ∧ ¬ IsPGroup p K := by
        intro K hK
        exact hS K (Finset.mem_insert_of_mem hK)
      letI : M.Normal := hM.1.1
      letI : (S.sup (fun K : Subgroup G => K) : Subgroup G).Normal :=
        finset_sup_normal S (fun K hK => (hrest K hK).1.1)
      by_cases hle : M ≤ S.sup (fun K : Subgroup G => K)
      · have heq : M ⊔ S.sup (fun K : Subgroup G => K) =
            S.sup (fun K : Subgroup G => K) := sup_eq_right.mpr hle
        simpa only [Finset.sup_insert, heq] using ih hrest
      · rw [Finset.sup_insert,
          card_sup_eq_mul_of_minimal_not_le M
            (S.sup (fun K : Subgroup G => K)) hM.1 hle]
        exact (Nat.coprime_mul_iff_left).2
          ⟨abelianMinimalNormal_card_coprime_of_not_isPGroup
              p M hM.1 hM.2.1 hM.2.2,
            ih hrest⟩

/-- The selected sum of all abelian non-`p` ambient minimal normal factors
has order coprime to `p`. -/
theorem abelianNonPrimarySoclePart_card_coprime
    (G : Type) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    Nat.Coprime
      (Nat.card ↥(minimalNormalSoclePart G
        (fun M => ¬ IsPGroup p M ∧ IsMulCommutative M))) p := by
  let S : Finset (Subgroup G) :=
    Finset.univ.filter (fun M : Subgroup G =>
      IsMinimalNormalSubgroup M ∧
        (¬ IsPGroup p M ∧ IsMulCommutative M))
  have hcop : Nat.Coprime
      (Nat.card ↥(S.sup (fun M : Subgroup G => M))) p := by
    apply finset_sup_abelian_nonprimary_card_coprime p
    intro M hM
    have hm := (Finset.mem_filter.mp hM).2
    exact ⟨hm.1, hm.2.2, hm.2.1⟩
  have hpart : minimalNormalSoclePart G
        (fun M => ¬ IsPGroup p M ∧ IsMulCommutative M) =
      S.sup (fun M : Subgroup G => M) := by
    apply le_antisymm
    · apply minimalNormalSoclePart_le_of
      intro M hM htype
      apply Finset.le_sup (f := fun M : Subgroup G => M)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ M, hM, htype⟩
    · apply Finset.sup_le
      intro M hMS
      have hm := (Finset.mem_filter.mp hMS).2
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup G => ¬ IsPGroup p K ∧ IsMulCommutative K)
        M hm.1 hm.2
  rw [hpart]
  exact hcop

/-- The selected abelian non-`p` socle part is disjoint from every normal
`p`-subgroup of the ambient finite group. -/
theorem abelianNonPrimarySoclePart_inf_isPGroup_eq_bot
    {G : Type} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (D : Subgroup G) [D.Normal] (hD : IsPGroup p D) :
    minimalNormalSoclePart G
        (fun M => ¬ IsPGroup p M ∧ IsMulCommutative M) ⊓ D = ⊥ := by
  apply le_antisymm
  · intro x hx
    let xd : D := ⟨x, hx.2⟩
    obtain ⟨k, hk⟩ := hD xd
    have hpow : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have hcard : orderOf x ∣ Nat.card
        ↥(minimalNormalSoclePart G
          (fun M => ¬ IsPGroup p M ∧ IsMulCommutative M)) :=
      Subgroup.orderOf_dvd_natCard _ hx.1
    have hprimePow : orderOf x ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one hpow
    have hcop := (abelianNonPrimarySoclePart_card_coprime G p).pow_right k
    have hone : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hcard hprimePow
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  · exact bot_le

end SymmetricSubgroupAsymptotics

end
