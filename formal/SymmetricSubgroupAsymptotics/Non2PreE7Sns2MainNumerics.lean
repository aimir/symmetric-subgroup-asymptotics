import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalRows

/-!
# Main-row numerics for the disjoint numerical/SNS2 catalogue
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev hybridTagCount : ℕ :=
  2 * preE7NoPairNoC3EarlierOwnerCount + 1

private theorem preE7NumericalSns2Index_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7NumericalSns2Index := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  refine ⟨(hybridTagCount : ℝ) * B,
    mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hnum : Nat.card (PreE7NumericalOwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : Fin preE7NoPairNoC3EarlierOwnerCount,
          Nat.card (PreE7NonPairActionClass w) :=
        Finset.sum_le_sum (fun _ _ => Finite.card_subtype_le _)
      _ = _ := by simp
  have hsns2 : Nat.card (PreE7Sns2OwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : Fin preE7NoPairNoC3EarlierOwnerCount,
          Nat.card (PreE7NonPairActionClass w) :=
        Finset.sum_le_sum (fun _ _ => Finite.card_subtype_le _)
      _ = _ := by simp
  have hcard : Nat.card (PreE7NumericalSns2Index w) ≤
      hybridTagCount * Nat.card (PreE7NonPairActionClass w) := by
    rw [Nat.card_sum, Nat.card_sum]
    calc
      _ ≤ preE7NoPairNoC3EarlierOwnerCount *
            Nat.card (PreE7NonPairActionClass w) +
          (preE7NoPairNoC3EarlierOwnerCount *
              Nat.card (PreE7NonPairActionClass w) +
            Nat.card (PreE7NonPairActionClass w)) :=
        Nat.add_le_add hnum (Nat.add_le_add hsns2 le_rfl)
      _ = hybridTagCount * Nat.card (PreE7NonPairActionClass w) := by
        dsimp only [hybridTagCount]
        ring
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  calc
    (Nat.card (PreE7NumericalSns2Index w) : ℝ) ≤
        (hybridTagCount : ℝ) *
          (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (hybridTagCount : ℝ) *
        (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast haction)
        (Nat.cast_nonneg _)
    _ ≤ (hybridTagCount : ℝ) *
        (B * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (Nat.cast_nonneg _)
    _ = ((hybridTagCount : ℝ) * B) *
        (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2) := by ring

variable
  (Residual : ∀ w (U : PreE7NonPairActionClass w),
    PreE7NumericalSns2ResidualChoice w U)

private theorem preE7NumericalSns2Main_envelope :
    LinearLogSquaredMenuNumeratorBound 3
      (preE7NumericalSns2D Residual) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  rcases j with a | a
  · simpa only [preE7NumericalSns2D, zero_mul, zero_add, one_mul, hwb,
      Nat.cast_add, Nat.cast_ofNat] using
      (preE7NumericalOwnedPackage a).main_total_bound (n - w)
  · rcases a with a | U
    · positivity
    · simpa only [preE7NumericalSns2D, zero_mul, zero_add, one_mul, hwb,
        Nat.cast_add, Nat.cast_ofNat] using
        (Residual w U).main_total_bound (n - w)

/-- The disjoint catalogue's complete main row has subquadratic normalized
mass.  SNS2 contributes zero to this row. -/
theorem preE7NumericalSns2_mainMenu
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3 (preE7NumericalSns2D Residual)
      preE7NumericalSns2A :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (preE7NumericalSns2D_nonneg Residual)
    (fun w j => by
      change (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7NumericalSns2Action w j : Set (Equiv.Perm (Fin w))))
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NumericalSns2Action w j : Set (Equiv.Perm (Fin w))))))
    (preE7NumericalSns2Index_subquadratic hLMM)
    (preE7NumericalSns2Main_envelope Residual)

private def preE7NumericalSns2ParameterTheta (w : ℕ) :
    PreE7NumericalSns2Index w → ℝ
  | .inl a => (preE7NumericalOwnedPackage a).package.certificate.theta
  | .inr (.inl _) => 0
  | .inr (.inr _) => 0

private theorem preE7NumericalSns2_entryParameters :
    ∀ w j, PreE7CharacterEntryParameters preE7CharacterRho w
      (preE7NumericalSns2V Residual w j)
      (preE7NumericalSns2Eta Residual w j)
      (preE7NumericalSns2Delta Residual w j)
      (preE7NumericalSns2Cutoff Residual w j)
      (preE7NumericalSns2Alpha Residual w j)
      (preE7NumericalSns2ParameterTheta w j) := by
  intro w j
  rcases j with a | a
  · exact (preE7NumericalOwnedPackage a).parameters
  · rcases a with a | U
    · exact preE7EmptyCell_entryParameters
        (preE7NonPairAction_width_three_le a.2.1)
    · exact (Residual w U).parameters

/-- Uniform main-transfer parameters on the disjoint catalogue.  The SNS2
secondary slope is deliberately absent from this record. -/
theorem preE7NumericalSns2_parameterBound :
    GrowingQuotientParameterBound preE7CharacterRho
      (preE7NumericalSns2V Residual)
      (preE7NumericalSns2Eta Residual)
      (preE7NumericalSns2Delta Residual)
      (preE7NumericalSns2Cutoff Residual)
      (preE7NumericalSns2Alpha Residual) :=
  (growingQuotientParameterBound_of_entryParameters
    (preE7NumericalSns2_entryParameters Residual)).1

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
