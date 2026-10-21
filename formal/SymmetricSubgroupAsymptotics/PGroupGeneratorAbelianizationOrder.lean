import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.Abelianization.Defs

/-! The full original abelianization has room for the actual ordinary
Burnside rank. This retains higher cyclic factors rather than presuming
that the original abelianization is elementary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- Ordinary generation from the actual prime quotient bounds rank. -/
theorem pGroup_genRank_le_primeCharacterRank (hG : IsPGroup p G) :
    MarkedC4.genRank G ≤ Module.finrank (ZMod p) (PrimeCharacters p G) := by
  obtain ⟨g, hg⟩ := exists_primeFrattini_generating_tuple p hG
  let S : Finset G := Finset.univ.image g
  have hset : (S : Set G) = Set.range g := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hgen : Subgroup.closure (S : Set G) = ⊤ := by rw [hset]; exact hg
  have hcard : S.card ≤ Module.finrank (ZMod p) (PrimeCharacters p G) := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin (Module.finrank (ZMod p) (PrimeCharacters p G)))).card :=
        Finset.card_image_le
      _ = Module.finrank (ZMod p) (PrimeCharacters p G) := by
        rw [Finset.card_univ, Fintype.card_fin]
  exact (MarkedC4.genRank_le hgen).trans hcard

/-- The complete elementary quotient is an actual quotient of the full
abelianization; the latter may still have higher cyclic factors. -/
theorem primeCharacterRank_pow_le_abelianization_card :
    p ^ Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Nat.card (Abelianization G) := by
  let f : Abelianization G →* Multiplicative (PrimeAbelianization p G) :=
    Abelianization.lift (primeAbelianizationGroupMap p G)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := primeAbelianizationGroupMap_surjective p G x
    exact ⟨Abelianization.of g, (Abelianization.lift_apply_of _ _).trans hg⟩
  have hc := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (PrimeAbelianization p G) ≃
    PrimeAbelianization p G)] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    Subspace.dual_finrank_eq] at hc
  exact hc

/-- A lower bound using the original ordinary generator number, with no
exponent assumption on its original full abelianization. -/
theorem pGroup_pow_genRank_le_abelianization_card (hG : IsPGroup p G) :
    p ^ MarkedC4.genRank G ≤ Nat.card (Abelianization G) :=
  (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (pGroup_genRank_le_primeCharacterRank p hG)).trans
      (primeCharacterRank_pow_le_abelianization_card p)

end SymmetricSubgroupAsymptotics
