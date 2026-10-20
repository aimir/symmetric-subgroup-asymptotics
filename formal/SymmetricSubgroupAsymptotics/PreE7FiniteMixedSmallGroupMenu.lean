import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoEightPairFiniteCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics

/-! Complete semantic mixed rows for small literal groups. A complete normal
registry and quotient socle tuples supply the character axes. The coefficient
sums are proved independently by injecting states into subsets and bounding
actual quotient automorphisms by functions. No character class enumeration
or supplied final coefficient estimate is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PreE7FiniteMixedSmallGroupMenu

variable {U : Type} [Group U] [Finite U]

theorem state_card_le (R : FiniteNormalStateRegistry U) (hcard : Nat.card U ≤ 64) :
    Nat.card R.State ≤ 2^64 := by
  letI : Fintype U := Fintype.ofFinite U
  have hsets : Nat.card R.State ≤ Nat.card (Set U) :=
    Nat.card_le_card_of_injective (fun j => (R.state j : Set U)) (by
      intro j k h
      exact R.state_injective (SetLike.coe_injective h))
  have hsetcard : Nat.card (Set U) = 2^(Nat.card U) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_set]
  rw [hsetcard] at hsets
  exact hsets.trans (Nat.pow_le_pow_right (by decide) hcard)

theorem quotient_aut_card_le (hcard : Nat.card U ≤ 64)
    (N : Subgroup U) [N.Normal] : Nat.card ((U ⧸ N) ≃* (U ⧸ N)) ≤ 64^64 := by
  have hq : Nat.card (U ⧸ N) ≤ 64 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans hcard
  exact (mulEquiv_card_le_card_pow_card (U ⧸ N)).trans
    ((Nat.pow_le_pow_left hq (Nat.card (U ⧸ N))).trans (Nat.pow_le_pow_right (by decide) hq))

theorem state_sum_le (R : FiniteNormalStateRegistry U) (hcard : Nat.card U ≤ 64)
    (f : R.State → ℝ) (hf : ∀ j, f j ≤ (64 : ℝ)^64) :
    (∑ j, f j) ≤ (2 : ℝ)^(448 : ℕ) := by
  calc
    (∑ j, f j) ≤ ∑ _j : R.State, (64 : ℝ)^64 := Finset.sum_le_sum (fun j _ => hf j)
    _ = (Nat.card R.State : ℝ) * (64 : ℝ)^64 := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ((2 : ℝ)^(64 : ℕ)) * (64 : ℝ)^64 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast state_card_le R hcard
    _ = (2 : ℝ)^(448 : ℕ) := by
      rw [show (64 : ℝ) = (2 : ℝ)^(6 : ℕ) by norm_num,← pow_mul,← pow_add]

theorem allowance (b : ℕ) :
    (2 : ℝ)^(448 : ℕ) ≤
      (2 : ℝ)^(16 * (16 : ℝ) * Real.log ((16+b+2 : ℕ) : ℝ)^2) := by
  calc
    (2 : ℝ)^(448 : ℕ) = (2 : ℝ)^(448 : ℝ) :=
      (Real.rpow_natCast (2 : ℝ) 448).symm
    _ ≤ (2 : ℝ)^(36*(16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ _ := two_rpow_thirtySix_width_le_menuMass (w := 16) (by norm_num) b

theorem general_capacity {t : ℕ} (ht : t ≤ 2)
    {Q : Type} [Group Q] [Finite Q]
    (hZmud : ZmudFaithfulCharacterTupleInput) (hgen : SocleNormalGeneratorBound Q t) :
    (hZmud.generalCertificate hgen).slope ≤ preE7CharacterWindow 16 := by
  rw [ZmudFaithfulCharacterTupleInput.generalCertificate_slope]
  have hlog := logb_two_five_div_five_lt_seven_fifteenths
  interval_cases t <;>
    norm_num [preE7CharacterWindow,preE7CharacterRho,halfDegree] <;> nlinarith

variable (i : PreE7NonPairActionClass 16)
  (R : FiniteNormalStateRegistry (preE7NonPairAction 16 i))
  {t : ℕ} (ht : t ≤ 2)
  (hgen : ∀ N : {N : Subgroup (preE7NonPairAction 16 i) // N.Normal},
    SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N.1) t)
  (hZmud : ZmudFaithfulCharacterTupleInput)

noncomputable def axes : PreE7FiniteMixedCharacterAxes 16 i where
  width_lower := by decide
  width_upper := by decide
  registry := R
  axes.state j _ :=
    ⟨hZmud.generalCertificate (hgen (R.normalAxis j)),rfl,
      general_capacity ht hZmud (hgen (R.normalAxis j))⟩

noncomputable def menu (hcard : Nat.card (preE7NonPairAction 16 i) ≤ 64) :
    PreE7FiniteMixedCharacterMenuData 16 i where
  axes := axes i R ht hgen hZmud
  main_state_total_bound b := by
    apply (state_sum_le R hcard _ ?_).trans (allowance b)
    intro j
    change (if (⊤ : Subgroup (preE7NonPairAction 16 i)) ≤ (R.normalAxis j).1
      then (1 : ℝ) else 0) ≤ (64 : ℝ)^64
    split_ifs <;> norm_num
  tail_state_total_bound b := by
    apply (state_sum_le R hcard _ ?_).trans (allowance b)
    intro j
    change (if (⊤ : Subgroup (preE7NonPairAction 16 i)) ≤ (R.normalAxis j).1
      then (0 : ℝ) else
        (Nat.card ((preE7NonPairAction 16 i ⧸ (R.normalAxis j).1) ≃*
          (preE7NonPairAction 16 i ⧸ (R.normalAxis j).1)) : ℝ)) ≤ (64 : ℝ)^64
    split_ifs
    · positivity
    · exact_mod_cast quotient_aut_card_le hcard (R.normalAxis j).1

noncomputable def importedRow (hcard : Nat.card (preE7NonPairAction 16 i) ≤ 64) :
    DegreeTwoDegreeSixteenImportedRow i :=
  .mixed (menu i R ht hgen hZmud hcard)

end PreE7FiniteMixedSmallGroupMenu
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
