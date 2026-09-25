import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Actual oriented split ternary characters

Splitting means an actual group section. Its order-three incidence and the
retained nonsplit annihilator give the exact oriented character count.
Any surviving-graph predicate is retained as an actual subtype.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

abbrev TernaryCyclic := Multiplicative (ZMod 3)

def ternaryGenerator : TernaryCyclic := Multiplicative.ofAdd 1

theorem ternaryGenerator_order : orderOf ternaryGenerator = 3 :=
  ZMod.addOrderOf_one 3

theorem ternaryGenerator_generates (z : TernaryCyclic) :
    z ∈ Subgroup.zpowers ternaryGenerator := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective z.toAdd
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  change Multiplicative.ofAdd (n • (1 : ZMod 3)) = z
  simpa only [zsmul_one] using congrArg Multiplicative.ofAdd hn

variable {G : Type*} [Group G]

abbrev ternaryCharacterHom (χ : PrimeCharacters 3 G) : G →* TernaryCyclic :=
  AddMonoidHom.toMultiplicativeRight χ

/-- Splitting is an actual section of the original character. -/
def TernarySplit (χ : PrimeCharacters 3 G) : Prop :=
  ∃ s : TernaryCyclic →* G, (ternaryCharacterHom χ).comp s = MonoidHom.id _

/-- A chosen oriented order-three element determines the actual section. -/
def ternarySectionOfWitness (x : G) (hx : orderOf x = 3) : TernaryCyclic →* G :=
  monoidHomOfForallMemZpowers ternaryGenerator_generates
    (show orderOf x ∣ orderOf ternaryGenerator by rw [hx, ternaryGenerator_order])

theorem ternarySectionOfWitness_generator (x : G) (hx : orderOf x = 3) :
    ternarySectionOfWitness x hx ternaryGenerator = x :=
  monoidHomOfForallMemZpowers_apply_gen _ _

/-- The orientation is the literal value one, rather than an unoriented
kernel or an isomorphism class of complements. -/
theorem ternarySplit_iff_witness (χ : PrimeCharacters 3 G) :
    TernarySplit χ ↔ ∃ x : G, orderOf x = 3 ∧ χ (Additive.ofMul x) = 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have hi : Function.Injective s := Function.LeftInverse.injective
      (fun z => DFunLike.congr_fun hs z)
    refine ⟨s ternaryGenerator, ?_, ?_⟩
    · rw [orderOf_injective s hi, ternaryGenerator_order]
    · exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hs ternaryGenerator)
  · rintro ⟨x,hx,hχ⟩
    refine ⟨ternarySectionOfWitness x hx, ?_⟩
    apply (MonoidHom.eq_iff_eq_on_generator ternaryGenerator_generates _ _).mpr
    change ternaryCharacterHom χ (ternarySectionOfWitness x hx ternaryGenerator) = _
    rw [ternarySectionOfWitness_generator]
    exact congrArg Multiplicative.ofAdd hχ

theorem ternarySplit_ne_zero {χ : PrimeCharacters 3 G} (hχ : TernarySplit χ) : χ ≠ 0 := by
  obtain ⟨x,_,hx⟩ := (ternarySplit_iff_witness χ).mp hχ
  intro h
  simp [h] at hx

/-- The actual nonsplit characters form the retained order-three
annihilator, including the zero character. -/
def ternaryNonsplitAnnihilator (G : Type*) [Group G] :
    Submodule (ZMod 3) (PrimeCharacters 3 G) where
  carrier := {χ | ∀ x : G, orderOf x = 3 → χ (Additive.ofMul x) = 0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by
    intro χ ψ hχ hψ x hx
    change χ (Additive.ofMul x) + ψ (Additive.ofMul x) = 0
    rw [hχ x hx,hψ x hx,zero_add]
  smul_mem' := by intro c χ hχ x hx; change c * χ (Additive.ofMul x) = 0; rw [hχ x hx,mul_zero]

theorem ternaryNonsplitAnnihilator_mem_iff (χ : PrimeCharacters 3 G) :
    χ ∈ ternaryNonsplitAnnihilator G ↔ ¬ TernarySplit χ := by
  constructor
  · intro h hs
    obtain ⟨x,hx,hχ⟩ := (ternarySplit_iff_witness χ).mp hs
    have hz := h x hx
    rw [hχ] at hz
    exact one_ne_zero hz
  · intro h x hx
    by_contra hn
    have hv : χ (Additive.ofMul x) = 1 ∨ χ (Additive.ofMul x) = 2 := by
      have hv := (χ (Additive.ofMul x)).val_lt
      interval_cases he : (χ (Additive.ofMul x)).val
      · exact (hn (Fin.ext he)).elim
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext he)
    apply h
    apply (ternarySplit_iff_witness χ).mpr
    rcases hv with hv | hv
    · exact ⟨x,hx,hv⟩
    · refine ⟨x^2, ?_, ?_⟩
      · rw [(show Nat.Coprime (orderOf x) 2 by rw [hx]; decide).orderOf_pow,hx]
      · change χ (2 • Additive.ofMul x) = 1
        rw [map_nsmul,hv]
        decide

def ternaryCharacterRank (G : Type*) [Group G] : ℕ :=
  Module.finrank (ZMod 3) (PrimeCharacters 3 G)

def ternaryNonsplitRank (G : Type*) [Group G] : ℕ :=
  Module.finrank (ZMod 3) (ternaryNonsplitAnnihilator G)

/-- Exact oriented split count; no survival exclusions have yet been made. -/
theorem ternarySplit_card [Finite G] :
    Nat.card {χ : PrimeCharacters 3 G // TernarySplit χ} =
      3^(ternaryCharacterRank G) - 3^(ternaryNonsplitRank G) := by
  letI := Fintype.ofFinite (PrimeCharacters 3 G)
  let e : {χ : PrimeCharacters 3 G // TernarySplit χ} ≃
      {χ : PrimeCharacters 3 G // ¬ χ ∈ ternaryNonsplitAnnihilator G} :=
    Equiv.subtypeEquivRight (fun χ => by rw [ternaryNonsplitAnnihilator_mem_iff,not_not])
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := PrimeCharacters 3 G),
    Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ternaryNonsplitAnnihilator G)]
  simp only [Nat.card_zmod,ternaryCharacterRank,ternaryNonsplitRank]

/-- The surviving weight counts the exact supplied predicate on original
oriented characters. It need not equal the unrestricted split count. -/
def ternarySurvivingWeight (S : PrimeCharacters 3 G → Prop) : ℕ :=
  Nat.card {χ : PrimeCharacters 3 G // TernarySplit χ ∧ S χ}

theorem ternarySurvivingWeight_le [Finite G] (S : PrimeCharacters 3 G → Prop) :
    ternarySurvivingWeight S ≤ 3^(ternaryCharacterRank G) - 3^(ternaryNonsplitRank G) := by
  rw [← ternarySplit_card]
  exact Nat.card_le_card_of_injective
    (fun χ : {χ : PrimeCharacters 3 G // TernarySplit χ ∧ S χ} =>
      (⟨χ.1,χ.2.1⟩ : {χ : PrimeCharacters 3 G // TernarySplit χ}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun χ : {χ : PrimeCharacters 3 G // TernarySplit χ} => χ.1) h))

end SymmetricSubgroupAsymptotics
