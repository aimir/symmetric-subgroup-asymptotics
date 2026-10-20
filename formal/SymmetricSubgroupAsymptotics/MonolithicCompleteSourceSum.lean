import SymmetricSubgroupAsymptotics.MonolithicCompleteQuotientReduction
import SymmetricSubgroupAsymptotics.SocleOneEpimorphismEnvelopeTwelve

/-! Source summation after two actual monoliths. The two exceptional
faithful targets pay two ordinary one-position character envelopes; the
remaining complete quotient menu is retained without multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MonolithicCompleteSourceSum
open Non2UnipotentPrefixFiniteMenu

variable {G : Type} [Group G] [Finite G]

theorem complete_sum_le_two (hG : Nat.card G ≤ 2^12)
    (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ → Z ≤ N)
    (M : Subgroup (G ⧸ Z)) [M.Normal]
    (hM : ∀ (N : Subgroup (G ⧸ Z)) [N.Normal], N ≠ ⊥ → M ≤ N)
    (hs : SocleNormalGeneratorBound G 1)
    (hsZ : SocleNormalGeneratorBound (G ⧸ Z) 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := G) J) ≤
      (2 : ℝ)^(145 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) +
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := (G ⧸ Z) ⧸ M) J := by
  have hGZ : Nat.card (G ⧸ Z) ≤ 2^12 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z)).trans hG
  have hp (J : Subgroup (Equiv.Perm (Fin b))) :
      completeQuotientWeight (R := G) J ≤
        (2 : ℝ)^(145 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) +
          completeQuotientWeight (R := (G ⧸ Z) ⧸ M) J := by
    have hg := SocleOneEpimorphismEnvelopeTwelve.epi_card_le hG hs hZmud lit b J
    have hz := SocleOneEpimorphismEnvelopeTwelve.epi_card_le hGZ hsZ hZmud lit b J
    have h := (MonolithicCompleteQuotientReduction.complete_weight_le_two Z hZ M hM J).trans
      (add_le_add (add_le_add hg hz) le_rfl)
    convert h using 1 <;>
      (rw [show (145 : ℕ)=144+1 by decide, pow_succ]; ring)
  calc
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
        ((2 : ℝ)^(145 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) +
          completeQuotientWeight (R := (G ⧸ Z) ⧸ M) J) :=
      Finset.sum_le_sum (fun J _ => hp J)
    _ = _ := by simp [Finset.sum_add_distrib, subgroupCount, mul_comm]

end SymmetricSubgroupAsymptotics.MonolithicCompleteSourceSum
