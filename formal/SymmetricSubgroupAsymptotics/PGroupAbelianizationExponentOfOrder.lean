import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! Saturating the minimal possible full abelianization order forces
that FULL abelianization to have exponent p. The proof uses its actual
surjection to the complete prime-character quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- Higher cyclic factors are excluded by order equality, not assumed. -/
theorem pGroup_abelianization_exponent_of_card_le_pow_genRank
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (hG : IsPGroup p G) (hcard : Nat.card (Abelianization G)≤p^MarkedC4.genRank G) :
    ∀ a : Abelianization G, a^p=1 := by
  let V := Multiplicative (PrimeAbelianization p G)
  let f : Abelianization G →* V := Abelianization.lift (primeAbelianizationGroupMap p G)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,hg⟩ := primeAbelianizationGroupMap_surjective p G x
    exact ⟨Abelianization.of g,(Abelianization.lift_apply_of _ _).trans hg⟩
  have hVcard : Nat.card V=p^Module.finrank (ZMod p) (PrimeCharacters p G) := by
    rw [Nat.card_congr (Multiplicative.toAdd : V ≃ PrimeAbelianization p G)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod,
      Subspace.dual_finrank_eq]
  have hle : Nat.card (Abelianization G)≤Nat.card V := by
    rw [hVcard]
    exact hcard.trans (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (pGroup_genRank_le_primeCharacterRank p hG))
  have hi := (hf.bijective_of_nat_card_le hle).1
  have hVexp (v : V) : v^p=1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    exact ZModModule.char_nsmul_eq_zero p _
  intro a
  apply hi
  rw [map_pow,hVexp,map_one]

end SymmetricSubgroupAsymptotics
