import SymmetricSubgroupAsymptotics.C1SplitCharacters

/-! # Capacity with the actual retained annihilator
Exact counts are proved for any retained character subspace containing the
nonsplit annihilator, and for annihilators of actual selected order-three
witnesses. No capacity loss follows merely from the action having odd order.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

/-- Characters not detected by the actual selected order-three witnesses. -/
def ternaryRetainedAnnihilator (X : Set G) : Submodule (ZMod 3) (PrimeCharacters 3 G) where
  carrier := {χ | ∀ x ∈ X, χ (Additive.ofMul x) = 0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by
    intro χ ψ hχ hψ x hx
    change χ (Additive.ofMul x) + ψ (Additive.ofMul x) = 0
    rw [hχ x hx,hψ x hx,zero_add]
  smul_mem' := by
    intro c χ hχ x hx
    change c * χ (Additive.ofMul x) = 0
    rw [hχ x hx,mul_zero]

theorem ternaryNonsplit_le_retained (X : Set G) (hX : ∀ x ∈ X, orderOf x = 3) :
    ternaryNonsplitAnnihilator G ≤ ternaryRetainedAnnihilator X := by
  intro χ hχ x hx
  exact hχ x (hX x hx)

/-- Exact split capacity inside the retained subspace, before any unrelated
owner/survival exclusions. The same global nonsplit dimension is retained. -/
theorem ternaryRetainedSplit_card [Finite G]
    (A : Submodule (ZMod 3) (PrimeCharacters 3 G))
    (hA : ternaryNonsplitAnnihilator G ≤ A) :
    Nat.card {χ : A // TernarySplit χ.1} =
      3^(Module.finrank (ZMod 3) A) - 3^(ternaryNonsplitRank G) := by
  letI := Fintype.ofFinite A
  let e : ternaryNonsplitAnnihilator G ≃ {χ : A // ¬ TernarySplit χ.1} :=
    { toFun := fun χ => ⟨⟨χ.1,hA χ.2⟩,(ternaryNonsplitAnnihilator_mem_iff χ.1).mp χ.2⟩
      invFun := fun χ => ⟨χ.1.1,(ternaryNonsplitAnnihilator_mem_iff χ.1.1).mpr χ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : Nat.card {χ : A // ¬ TernarySplit χ.1} =
      Nat.card (ternaryNonsplitAnnihilator G) := (Nat.card_congr e).symm
  let ee : {χ : A // TernarySplit χ.1} ≃ {χ : A // ¬ ¬ TernarySplit χ.1} :=
    Equiv.subtypeEquivRight (fun _ => not_not.symm)
  rw [Nat.card_congr ee,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,he]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := A),
    Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ternaryNonsplitAnnihilator G)]
  simp only [Nat.card_zmod,ternaryNonsplitRank]

theorem ternaryRetainedSurviving_card_le [Finite G]
    (A : Submodule (ZMod 3) (PrimeCharacters 3 G))
    (hA : ternaryNonsplitAnnihilator G ≤ A) (S : PrimeCharacters 3 G → Prop) :
    Nat.card {χ : A // TernarySplit χ.1 ∧ S χ.1} ≤
      3^(Module.finrank (ZMod 3) A) - 3^(ternaryNonsplitRank G) := by
  rw [← ternaryRetainedSplit_card A hA]
  exact Nat.card_le_card_of_injective
    (fun χ : {χ : A // TernarySplit χ.1 ∧ S χ.1} =>
      (⟨χ.1,χ.2.1⟩ : {χ : A // TernarySplit χ.1}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun χ : {χ : A // TernarySplit χ.1} => χ.1) h))

/-- Exhausting the actual retained split subspace makes every further
surviving incidence empty; no numerical owner claim is postulated. -/
theorem ternaryRetainedSplit_empty_of_eq_nonsplit
    (A : Submodule (ZMod 3) (PrimeCharacters 3 G))
    (hA : A = ternaryNonsplitAnnihilator G) :
    IsEmpty {χ : A // TernarySplit χ.1} := by
  refine ⟨fun χ => ?_⟩
  exact (ternaryNonsplitAnnihilator_mem_iff χ.1.1).mp (hA ▸ χ.1.2) χ.2

end SymmetricSubgroupAsymptotics
