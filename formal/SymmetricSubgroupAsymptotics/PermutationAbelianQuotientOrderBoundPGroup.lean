import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBoundExtension
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-!
# Full abelianization order of a faithful permutation `p`-group

Strong degree induction uses the same original central-prime block frames
and complementary orbit kernels as the elementary rank theorem. The
induction invariant is the full order of the abelianization. Only the
exponent-`p` central-block kernel is estimated by its relative scalar head;
the smaller top and the intransitive kernel retain their complete orders.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

private theorem abelianization_card_eq_one_of_subsingleton_action
    {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X] [Subsingleton X] :
    Nat.card (Abelianization G) = 1 := by
  letI : Subsingleton G := ⟨fun a b =>
    eq_of_smul_eq_smul (α := X) (fun x => Subsingleton.elim (a • x) (b • x))⟩
  letI : Subsingleton (Abelianization G) := by
    change Subsingleton (G ⧸ commutator G)
    infer_instance
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

private theorem translation_kernel_pow
    (p : ℕ) [Fact p.Prime]
    {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : PrimeTranslationFrame p U I) (k : F.top.ker) : (k : U) ^ p = 1 := by
  have hk : k ^ p = 1 := by
    apply F.kernelChart.injective
    apply Multiplicative.toAdd.injective
    simp only [map_pow, map_one, toAdd_pow, toAdd_one]
    exact ZModModule.char_nsmul_eq_zero p _
  exact congrArg Subtype.val hk

private theorem transitive_step
    (p : ℕ) [Fact p.Prime]
    {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup p U)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup p H → Nat.card Y < Nat.card X →
        Nat.card (Abelianization H) ≤ p ^ (Nat.card Y / p)) :
    Nat.card (Abelianization U) ≤ p ^ (Nat.card X / p) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hnt : Nontrivial U := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
    refine ⟨⟨u, 1, fun h => hxy ?_⟩⟩
    rw [← hu, h, one_smul]
  obtain ⟨z, hz, hzp⟩ := CentralPrimeFrame.exists_central_order U hU hnt
  let F := CentralPrimeFrame.translationFrame z hz hzp
  letI : MulAction U (CentralPrimeFrame.Blocks z) :=
    MulAction.compHom _ (CentralPrimeFrame.topHom z hz)
  have hact : ∀ (u : U) (i : CentralPrimeFrame.Blocks z), u • i = F.top u i := fun _ _ => rfl
  have hker : F.top.rangeRestrict.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  have hpow : ∀ k : F.top.rangeRestrict.ker, (k : U) ^ p = 1 := by
    intro k
    exact translation_kernel_pow p F (⟨k, by rw [← hker]; exact k.2⟩ : F.top.ker)
  have hdim (K L : Subgroup U) [K.Normal] [L.Normal] (h : K = L) :
      Module.finrank (ZMod p) (primeRelativeCharacters p K) =
        Module.finrank (ZMod p) (primeRelativeCharacters p L) := by
    subst L
    rfl
  have hkerdim := hdim F.top.rangeRestrict.ker F.top.ker hker
  have hext := abelianization_card_elementary_kernel p F.top.rangeRestrict
    F.top.rangeRestrict_surjective hpow
  rw [hkerdim] at hext
  have hcard := CentralPrimeFrame.card_blocks z hz hzp
  have hdeg : Nat.card X / p = Nat.card (CentralPrimeFrame.Blocks z) := by
    rw [← hcard, Nat.mul_div_cancel_left _ hp]
  haveI : Finite (CentralPrimeFrame.Blocks z) := inferInstance
  haveI : Nonempty (CentralPrimeFrame.Blocks z) :=
    ⟨⟦Classical.choice (inferInstance : Nonempty X)⟧⟩
  have hpos : 0 < Nat.card (CentralPrimeFrame.Blocks z) := Nat.card_pos
  rcases subsingleton_or_nontrivial (CentralPrimeFrame.Blocks z) with hI | hI
  · letI : Subsingleton (CentralPrimeFrame.Blocks z) := hI
    have htop : Nat.card (Abelianization F.top.range) = 1 :=
      abelianization_card_eq_one_of_subsingleton_action (X := CentralPrimeFrame.Blocks z)
    have hkernel := F.kernel_relativeHead_le_card hact
    rw [htop, mul_one] at hext
    rw [hdeg]
    exact hext.trans (Nat.pow_le_pow_right hp hkernel)
  · letI : Nontrivial (CentralPrimeFrame.Blocks z) := hI
    letI : MulAction.IsPretransitive U (CentralPrimeFrame.Blocks z) :=
      ⟨fun i j => CentralPrimeFrame.topHom_transitive z hz i j⟩
    letI : MulAction.IsPretransitive F.top.range (CentralPrimeFrame.Blocks z) := by
      constructor
      intro i j
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
      exact ⟨F.top.rangeRestrict u, hu⟩
    have hTop : IsPGroup p F.top.range :=
      hU.of_surjective F.top.rangeRestrict F.top.rangeRestrict_surjective
    letI : Finite F.top.range := Finite.of_surjective F.top.rangeRestrict
      F.top.rangeRestrict_surjective
    have hlt : Nat.card (CentralPrimeFrame.Blocks z) < Nat.card X := by
      rw [← hcard]
      nlinarith
    have htop := hsmaller F.top.range (CentralPrimeFrame.Blocks z) hTop hlt
    have hkernel := F.kernel_relativeHead_le_div hact hU
    have hsum : Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) +
        Nat.card (CentralPrimeFrame.Blocks z) / p ≤ Nat.card (CentralPrimeFrame.Blocks z) := by
      have htwo : 2 * (Nat.card (CentralPrimeFrame.Blocks z) / p) ≤
          Nat.card (CentralPrimeFrame.Blocks z) := by
        calc
          2 * (Nat.card (CentralPrimeFrame.Blocks z) / p) ≤
              p * (Nat.card (CentralPrimeFrame.Blocks z) / p) := Nat.mul_le_mul_right _ hpp
          _ ≤ Nat.card (CentralPrimeFrame.Blocks z) := Nat.mul_div_le _ _
      omega
    calc
      Nat.card (Abelianization U) ≤
          p ^ Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) *
            Nat.card (Abelianization F.top.range) := hext
      _ ≤ p ^ Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) *
          p ^ (Nat.card (CentralPrimeFrame.Blocks z) / p) := Nat.mul_le_mul_left _ htop
      _ = p ^ (Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) +
          Nat.card (CentralPrimeFrame.Blocks z) / p) := (pow_add _ _ _).symm
      _ ≤ p ^ Nat.card (CentralPrimeFrame.Blocks z) := Nat.pow_le_pow_right hp hsum
      _ = p ^ (Nat.card X / p) := by rw [hdeg]

/-- A full-order version of the prime-rank theorem. Higher `p`-power cyclic
factors of the abelianization are included in this bound. -/
theorem pGroup_abelianization_card_le
    (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup p G) :
    Nat.card (Abelianization G) ≤ p ^ (Nat.card X / p) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmain : ∀ n : ℕ,
      ∀ (G₀ X₀ : Type) [Group G₀] [Finite G₀] [Finite X₀]
        [MulAction G₀ X₀] [FaithfulSMul G₀ X₀], Nat.card X₀ = n →
        IsPGroup p G₀ → Nat.card (Abelianization G₀) ≤ p ^ (Nat.card X₀ / p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ X₀ _ _ _ _ _ hdegree hG₀
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup p H →
            Nat.card Y < Nat.card X₀ → Nat.card (Abelianization H) ≤ p ^ (Nat.card Y / p) := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl hH
      rcases subsingleton_or_nontrivial X₀ with hX | hX
      · letI : Subsingleton X₀ := hX
        rw [abelianization_card_eq_one_of_subsingleton_action (X := X₀)]
        exact Nat.succ_le_of_lt (Nat.pow_pos hp)
      · letI : Nontrivial X₀ := hX
        by_cases ht : MulAction.IsPretransitive G₀ X₀
        · letI : MulAction.IsPretransitive G₀ X₀ := ht
          let phi : G₀ →* Equiv.Perm X₀ := MulAction.toPermHom G₀ X₀
          let U : Subgroup (Equiv.Perm X₀) := phi.range
          let e : G₀ ≃* U := MonoidHom.ofInjective
            (show Function.Injective phi from MulAction.toPerm_injective)
          letI : MulAction.IsPretransitive U X₀ := by
            constructor
            intro x y
            obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ x y
            exact ⟨phi.rangeRestrict g, hg⟩
          have hU : IsPGroup p U :=
            hG₀.of_surjective phi.rangeRestrict phi.rangeRestrict_surjective
          rw [Nat.card_congr e.abelianizationCongr.toEquiv]
          exact transitive_step p U hU hsmaller
        · obtain ⟨S, hS, hC⟩ := PermutationCharacterRankSplit.exists_nonempty_proper_invariant ht
          letI : FaithfulSMul (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ) :=
            PermutationCharacterRankSplit.kernel_complement_faithful S
          have hlt := PermutationCharacterRankSplit.degrees_lt S hS hC
          have hI := hsmaller (PermutationCharacterRankSplit.Image S) S
            (PermutationCharacterRankSplit.image_isPGroup S p hG₀) hlt.1
          have hK := hsmaller (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ)
            (PermutationCharacterRankSplit.kernel_isPGroup S p hG₀) hlt.2
          have hsplit := Nat.add_div_le_add_div (Nat.card S) (Nat.card ↥(Sᶜ)) p
          rw [PermutationCharacterRankSplit.card_split S] at hsplit
          calc
            Nat.card (Abelianization G₀) ≤
                Nat.card (Abelianization (PermutationCharacterRankSplit.Kernel S)) *
                  Nat.card (Abelianization (PermutationCharacterRankSplit.Image S)) :=
              abelianization_card_extension (PermutationCharacterRankSplit.projection S)
                (PermutationCharacterRankSplit.projection_surjective S)
            _ ≤ p ^ (Nat.card ↥(Sᶜ) / p) * p ^ (Nat.card S / p) := Nat.mul_le_mul hK hI
            _ = p ^ (Nat.card ↥(Sᶜ) / p + Nat.card S / p) := (pow_add _ _ _).symm
            _ ≤ p ^ (Nat.card X₀ / p) :=
              Nat.pow_le_pow_right hp (by simpa only [add_comm] using hsplit)
  exact hmain (Nat.card X) G X rfl hG

end SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

end
