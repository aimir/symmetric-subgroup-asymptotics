import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFiveWholeSocle

/-!
# The three-point seam in the sharp permutation-section socle bound

McIver--Neumann's sharp subgroup generator theorem has one exception: the
full three-point symmetric group needs two ordinary generators.  The degree
four consumer asks instead for a selected sum of ambient minimal normal
subgroups.  That socle part still needs only one ambient normal generator.

Indeed its actual faithful retained-top section has derived length two, so
every selected minimal normal factor is abelian.  Its intrinsic elementary
prime divides the order-three-or-six actual top, hence is two or three.
The two prime-primary sums each cost one slot by the exact three-point
sectional-rank bound and share that slot by the existing no-common-quotient
theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev LiteralNormalAxisSmallThree (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- Every selected minimal normal factor in a faithful three-block section
is elementary of prime two or three. -/
theorem threeBlockSelectedMinimal_isPGroup_two_or_three
    (hs : Nat.card block.Points = 3)
    (N : LiteralNormalAxisSmallThree (preE7NonPairAction w U))
    (R : Subgroup (preE7NonPairAction w U ⧸ N.1) → Prop)
    (hdisjoint : minimalNormalSoclePart
        (preE7NonPairAction w U ⧸ N.1) R ⊓
          degreeFiveRetainedBlockKernel block P N = ⊥)
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hMR : R M) :
    IsPGroup 2 M ∨ IsPGroup 3 M := by
  let Q := preE7NonPairAction w U ⧸ N.1
  let H := minimalNormalSoclePart Q R
  have hMH : M ≤ H :=
    minimalNormal_le_minimalNormalSoclePart R M hM hMR
  have hMdisjoint : M ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have : x ∈ H ⊓ degreeFiveRetainedBlockKernel block P N :=
      ⟨hMH hx.1, hx.2⟩
    rw [hdisjoint] at this
    exact this
  have hderived : derivedSeries M 2 = ⊥ :=
    degreeFiveRetainedBlockKernelDisjoint_secondDerived_eq_bot
      block P (Or.inr hs) N M hMdisjoint
  have hcomm : IsMulCommutative M := by
    by_contra hnoncomm
    letI : M.Normal := hM.1
    letI : Group.IsPerfect M :=
      nonabelian_minimal_normal_perfect M (fun K hK hKM ↦ by
        by_cases hKbot : K = ⊥
        · exact Or.inl hKbot
        · exact Or.inr (hM.2.2 K hK hKbot hKM)) hnoncomm
    have htop : derivedSeries M 2 = ⊤ := by
      have hfirst : derivedSeries M 1 = ⊤ := by
        rw [derivedSeries_one]
        exact Group.IsPerfect.commutator_eq_top
      rw [show 2 = 1 + 1 by norm_num, derivedSeries_succ, hfirst]
      exact Group.IsPerfect.commutator_eq_top
    have htopbot : (⊤ : Subgroup M) = ⊥ := htop.symm.trans hderived
    apply hM.2.1
    apply le_bot_iff.mp
    intro x hx
    let y : M := ⟨x, hx⟩
    have hy : y ∈ (⊥ : Subgroup M) := by
      rw [← htopbot]
      exact Subgroup.mem_top y
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hy))
  letI : M.Normal := hM.1
  let C := Classical.choice (elementaryMinimalNormalChart_nonempty M
    hM.2.1 hcomm (fun K hK hKM ↦ by
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hM.2.2 K hK hKbot hKM)))
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  have hcard : Nat.card M =
      C.p ^ Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card M = Nat.card (Multiplicative C.V) :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card C.V := rfl
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hcard_ne_one : Nat.card M ≠ 1 := by
    intro hone
    apply hM.2.1
    rw [← Subgroup.card_eq_one]
    exact hone
  have hdpos : 0 < Module.finrank (ZMod C.p) C.V := by
    by_contra hnot
    have hdzero : Module.finrank (ZMod C.p) C.V = 0 :=
      Nat.eq_zero_of_not_pos hnot
    apply hcard_ne_one
    rw [hcard, hdzero, pow_zero]
  let f := degreeFiveRestrictedRetainedTopMap block P N M
  have hf : Function.Injective f :=
    degreeFiveRestrictedRetainedTopMap_injective_of_disjoint
      block P N M hMdisjoint
  have hMtop : Nat.card M ∣ Nat.card block.Top :=
    (Subgroup.card_dvd_of_injective f hf).trans
      (degreeFiveRetainedTop_card_dvd_top block P N)
  have hpM : C.p ∣ Nat.card M := by
    rw [hcard]
    exact dvd_pow_self C.p hdpos.ne'
  have hpTop : C.p ∣ Nat.card block.Top := hpM.trans hMtop
  have finish (p : ℕ) (hp : C.p = p) : IsPGroup p M := by
    apply IsPGroup.of_card
    simpa only [hp] using hcard
  rcases degreeFive_top_card_eq_three_or_six block hs with htop | htop
  · have hp3 : C.p ∣ 3 := by simpa only [htop] using hpTop
    have hp : C.p = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hp3).resolve_left C.p_prime.ne_one
    exact Or.inr (finish 3 hp)
  · have hp6 : C.p ∣ 2 * 3 := by
      simpa only [show 2 * 3 = 6 by norm_num, htop] using hpTop
    rcases C.p_prime.dvd_mul.mp hp6 with hp2 | hp3
    · have hp : C.p = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left C.p_prime.ne_one
      exact Or.inl (finish 2 hp)
    · have hp : C.p = 3 :=
        ((Nat.dvd_prime Nat.prime_three).mp hp3).resolve_left C.p_prime.ne_one
      exact Or.inr (finish 3 hp)

/-- The exact small seam: any selected ambient socle part which embeds in
the actual retained three-block section needs at most one normal generator. -/
theorem threeBlockSelectedSoclePart_normalGen_le_one
    (hs : Nat.card block.Points = 3)
    (N : LiteralNormalAxisSmallThree (preE7NonPairAction w U))
    (R : Subgroup (preE7NonPairAction w U ⧸ N.1) → Prop)
    (hdisjoint : minimalNormalSoclePart
        (preE7NonPairAction w U ⧸ N.1) R ⊓
          degreeFiveRetainedBlockKernel block P N = ⊥) :
    MarkedC4.normalGen
      (minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1) R) ≤ 1 := by
  let Q := preE7NonPairAction w U ⧸ N.1
  let H₂ := minimalNormalSoclePart Q (fun M ↦ R M ∧ IsPGroup 2 M)
  let H₃ := minimalNormalSoclePart Q (fun M ↦ R M ∧ IsPGroup 3 M)
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsplit := normalGen_minimalNormalSoclePart_le_max_primePrimaryParts
    2 Q R
  have hcomp : minimalNormalSoclePart Q
        (fun M ↦ R M ∧ ¬ IsPGroup 2 M) = H₃ := by
    apply minimalNormalSoclePart_congr
    intro M hM
    constructor
    · rintro ⟨hR, hnot2⟩
      refine ⟨hR, ?_⟩
      rcases threeBlockSelectedMinimal_isPGroup_two_or_three
          block P hs N R hdisjoint M hM hR with hp2 | hp3
      · exact False.elim (hnot2 hp2)
      · exact hp3
    · rintro ⟨hR, hp3⟩
      refine ⟨hR, ?_⟩
      intro hp2
      apply hM.2.1
      simpa only [inf_idem] using
        (isPGroup_inf_eq_bot_of_coprime 2 3 (by norm_num) M M hp2 hp3)
  have hH₂le : H₂ ≤ minimalNormalSoclePart Q R := by
    apply minimalNormalSoclePart_le_of
    intro M hMmin hMR
    exact minimalNormal_le_minimalNormalSoclePart R M hMmin hMR.1
  have hH₃le : H₃ ≤ minimalNormalSoclePart Q R := by
    apply minimalNormalSoclePart_le_of
    intro M hMmin hMR
    exact minimalNormal_le_minimalNormalSoclePart R M hMmin hMR.1
  have hdisjoint₂ : H₂ ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have : x ∈ minimalNormalSoclePart Q R ⊓
        degreeFiveRetainedBlockKernel block P N := ⟨hH₂le hx.1, hx.2⟩
    rw [hdisjoint] at this
    exact this
  have hdisjoint₃ : H₃ ⊓ degreeFiveRetainedBlockKernel block P N = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have : x ∈ minimalNormalSoclePart Q R ⊓
        degreeFiveRetainedBlockKernel block P N := ⟨hH₃le hx.1, hx.2⟩
    rw [hdisjoint] at this
    exact this
  have hgen₂ : MarkedC4.normalGen H₂ ≤ 1 := by
    have hrank :=
      degreeFiveRetainedBlockKernelDisjoint_primeCharacterRank_le
        block P 2 N H₂ hdisjoint₂
    rw [hs] at hrank
    norm_num at hrank
    exact (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 2 H₂
      (primePrimarySoclePart_isPGroup_of_predicate 2 Q R)).trans hrank
  have hgen₃ : MarkedC4.normalGen H₃ ≤ 1 := by
    have hrank :=
      degreeFiveRetainedBlockKernelDisjoint_primeCharacterRank_le
        block P 3 N H₃ hdisjoint₃
    rw [hs] at hrank
    norm_num at hrank
    exact (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 3 H₃
      (primePrimarySoclePart_isPGroup_of_predicate 3 Q R)).trans hrank
  rw [hcomp] at hsplit
  have hmax : max (MarkedC4.normalGen H₂) (MarkedC4.normalGen H₃) ≤ 1 :=
    max_le hgen₂ hgen₃
  exact hsplit.trans hmax

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
