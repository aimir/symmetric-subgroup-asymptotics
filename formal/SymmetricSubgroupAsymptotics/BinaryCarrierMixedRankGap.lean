import SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank

/-!
# Strict binary character-rank gaps for the actual carrier masters

The all-normal row theorem is applied to the original top subgroup.
Every full-menu head is at most three times its own physical scale.
Restriction to top and inflation through an actual onto map are injective,
so the resulting absolute rank gap survives quotient replacement while
retaining the degree of the original eight- or sixteen-point action.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Restriction to the literal top subgroup loses no original character. -/
theorem primeCharacterRestriction_top_injective (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] :
    Function.Injective (primeCharacterRestriction p (⊤ : Subgroup G)) := by
  intro χ ψ h
  ext x
  exact DFunLike.congr_fun (congrArg Subtype.val h)
    (Additive.ofMul (⟨x, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)))

theorem primeCharacterRank_le_relativeTop (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p (⊤ : Subgroup G)) :=
  (primeCharacterRestriction p (⊤ : Subgroup G)).finrank_le_finrank_of_injective
    (primeCharacterRestriction_top_injective p G)

namespace BinaryCarrierMixedRankGap

open BinaryCarrierWord BinaryCarrierMixedMenuWord BinaryCarrierMixedActions
  FullSubdirectGoursat

private theorem alpha_le_three_quarters (i : Fin 6) :
    BinaryCarrierCone.alpha i ≤ (3 / 4 : ℝ) := by
  fin_cases i
  · change (5 / 8 : ℝ) ≤ 3 / 4
    norm_num
  · change (3 / 4 : ℝ) ≤ 3 / 4
    exact le_rfl
  · change (0 : ℝ) ≤ 3 / 4
    norm_num
  · change (1 / 4 : ℝ) ≤ 3 / 4
    norm_num
  · change (1 / 4 : ℝ) ≤ 3 / 4
    norm_num
  · change (1 / 2 : ℝ) ≤ 3 / 4
    norm_num

/-- This is a scalar consequence of the checked full menu, retaining each
label's scale rather than assigning mass eight to all degree-eight rows. -/
theorem envelope_head_le_three_scale (i : BinaryCarrierFullMenu.Label) :
    ((BinaryCarrierFullMenu.envelope i).k : ℝ) ≤
      3 * BinaryCarrierFullMenu.physicalScale i := by
  calc
    _ ≤ BinaryCarrierFullMenuEnergy.mass i *
        BinaryCarrierCone.alpha (BinaryCarrierFullMenuEnergy.color i) :=
      BinaryCarrierFullMenuEnergy.head_le i
    _ ≤ BinaryCarrierFullMenuEnergy.mass i * (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (alpha_le_three_quarters (BinaryCarrierFullMenuEnergy.color i))
        (BinaryCarrierFullMenuEnergy.mass_nonneg i)
    _ = _ := by unfold BinaryCarrierFullMenuEnergy.mass; ring

theorem factor_relative_head_le (k : Kind) (N : NormalAxis (factor k).Carrier) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N.1) ≤ 3 * factorScaleNat k := by
  obtain ⟨i, hi, hs⟩ := factor_covered k N
  have hr : ((actualRow (A := factor k) N).k : ℝ) ≤ 3 * factorScale k := by
    calc
      _ ≤ ((BinaryCarrierFullMenu.envelope i).k : ℝ) := by exact_mod_cast hi.head
      _ ≤ 3 * BinaryCarrierFullMenu.physicalScale i := envelope_head_le_three_scale i
      _ = _ := by rw [hs]
  rw [← factorScaleNat_cast k] at hr
  have hn : (actualRow (A := factor k) N).k ≤ 3 * factorScaleNat k := by
    exact_mod_cast hr
  exact hn

/-- The bound is on the complete absolute character space of the same
literal master, not on a guessed ambient-relative surrogate. -/
theorem factor_rank_le (k : Kind) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (factor k).Carrier) ≤
      3 * factorScaleNat k :=
  (primeCharacterRank_le_relativeTop 2 (factor k).Carrier).trans
    (factor_relative_head_le k ⟨⊤, inferInstance⟩)

/-- Every original onto image inherits the bound by actual inflation.
The target is not assumed to have any particular faithful action. -/
theorem quotient_rank_le (k : Kind) {G : Type*} [Group G]
    (β : (factor k).Carrier →* G) (hβ : Function.Surjective β) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) ≤ 3 * factorScaleNat k :=
  ((primeCharacterInflation 2 β).finrank_le_finrank_of_injective
    (primeCharacterInflation_injective 2 β hβ)).trans (factor_rank_le k)

theorem factorScaleNat_pos (k : Kind) : 1 ≤ factorScaleNat k := by
  cases k <;> norm_num [factorScaleNat]

/-- The point count belongs to the specified original master action.
An actual same-degree quotient action can use this gap unchanged. -/
theorem quotient_rank_gap (k : Kind) {G : Type*} [Group G]
    (β : (factor k).Carrier →* G) (hβ : Function.Surjective β) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) + 1 ≤
      Fintype.card (points k) / 2 := by
  have h := quotient_rank_le k β hβ
  have hs := factorScaleNat_pos k
  rw [point_card]
  omega

theorem factor_rank_gap (k : Kind) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (factor k).Carrier) + 1 ≤
      Fintype.card (points k) / 2 :=
  quotient_rank_gap k (MonoidHom.id _) Function.surjective_id

/-- The additional regular C4 colour has absolute binary rank at most one.
Its proof uses one cyclic generator, not a degree-two replacement. -/
theorem cyclicFour_rank_le_one :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (Multiplicative (ZMod 4))) ≤ 1 :=
  primeCharacterRank_le_of_injective 2
    (primeSectionalRankBound_cyclic 2 (Multiplicative (ZMod 4)))
    (MonoidHom.id _) Function.injective_id

theorem cyclicFour_rank_gap :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (Multiplicative (ZMod 4))) + 1 ≤ 4 / 2 := by
  have h := cyclicFour_rank_le_one
  omega

end BinaryCarrierMixedRankGap
end SymmetricSubgroupAsymptotics
