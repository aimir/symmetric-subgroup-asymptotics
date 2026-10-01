import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalRows
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2MainNumerics

/-!
# Main-row numerics for the complete rank-tail catalogue
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

noncomputable def preE7NumericalRankTailIndexEquiv (w : ℕ) :
    PreE7NumericalRankTailIndex w ≃
      PreE7NumericalOwnedIndex w ⊕
        (PreE7B6OwnedIndex w ⊕
          (PreE7Y1OwnedIndex w ⊕
            (PreE7Sns2OwnedIndex w ⊕ PreE7NonPairActionClass w))) where
  toFun
    | .ordinary a => .inl a
    | .b6 a => .inr (.inl a)
    | .y1 a => .inr (.inr (.inl a))
    | .sns2 a => .inr (.inr (.inr (.inl a)))
    | .terminal U => .inr (.inr (.inr (.inr U)))
  invFun
    | .inl a => .ordinary a
    | .inr (.inl a) => .b6 a
    | .inr (.inr (.inl a)) => .y1 a
    | .inr (.inr (.inr (.inl a))) => .sns2 a
    | .inr (.inr (.inr (.inr U))) => .terminal U
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · rcases a with a | a
        · rfl
        · rcases a with a | a <;> rfl

private abbrev rankTailTagCount : ℕ :=
  4 * preE7NoPairNoC3EarlierOwnerCount + 1

private theorem ownerActionIndex_card_le
    (w : ℕ)
    (F : Fin preE7NoPairNoC3EarlierOwnerCount →
      PreE7NonPairActionClass w → Prop) :
    Nat.card (Σ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      {U : PreE7NonPairActionClass w // F k U}) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) := by
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _ : Fin preE7NoPairNoC3EarlierOwnerCount,
        Nat.card (PreE7NonPairActionClass w) :=
      Finset.sum_le_sum (fun _ _ => Finite.card_subtype_le _)
    _ = _ := by simp

private theorem preE7NumericalRankTailIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7NumericalRankTailIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  refine ⟨(rankTailTagCount : ℝ) * B,
    mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have hnum : Nat.card (PreE7NumericalOwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) :=
    ownerActionIndex_card_le w
      (fun k U => preE7NoPairNoC3EarlierNumericalFamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U)
  have hb6 : Nat.card (PreE7B6OwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) :=
    ownerActionIndex_card_le w
      (fun k U => preE7NoPairNoC3EarlierOwnerEquiv k = .b6 ∧
        Nonempty (PreE7B6SourceData w U))
  have hy1 : Nat.card (PreE7Y1OwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) :=
    ownerActionIndex_card_le w
      (fun k U => preE7NoPairNoC3EarlierOwnerEquiv k = .y1 ∧
        Nonempty (PreE7Y1SourceData w U))
  have hsns2 : Nat.card (PreE7Sns2OwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) :=
    ownerActionIndex_card_le w
      (fun k U => preE7NoPairNoC3EarlierOwnerEquiv k = .sns2 ∧
        Nonempty (PreE7Sns2SourceData w U))
  have heq : Nat.card (PreE7NumericalRankTailIndex w) =
      Nat.card (PreE7NumericalOwnedIndex w) +
        (Nat.card (PreE7B6OwnedIndex w) +
          (Nat.card (PreE7Y1OwnedIndex w) +
            (Nat.card (PreE7Sns2OwnedIndex w) +
              Nat.card (PreE7NonPairActionClass w)))) := by
    rw [Nat.card_congr (preE7NumericalRankTailIndexEquiv w)]
    simp only [Nat.card_sum]
  have hcard : Nat.card (PreE7NumericalRankTailIndex w) ≤
      rankTailTagCount * Nat.card (PreE7NonPairActionClass w) := by
    rw [heq]
    let M := preE7NoPairNoC3EarlierOwnerCount *
      Nat.card (PreE7NonPairActionClass w)
    calc
      _ ≤ M + (M + (M + (M + Nat.card (PreE7NonPairActionClass w)))) :=
        Nat.add_le_add hnum (Nat.add_le_add hb6
          (Nat.add_le_add hy1 (Nat.add_le_add hsns2 le_rfl)))
      _ = rankTailTagCount * Nat.card (PreE7NonPairActionClass w) := by
        dsimp only [M, rankTailTagCount]
        ring
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  calc
    (Nat.card (PreE7NumericalRankTailIndex w) : ℝ) ≤
        (rankTailTagCount : ℝ) *
          (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (rankTailTagCount : ℝ) *
        (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast haction)
        (Nat.cast_nonneg _)
    _ ≤ (rankTailTagCount : ℝ) *
        (B * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (Nat.cast_nonneg _)
    _ = ((rankTailTagCount : ℝ) * B) *
        (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2) := by ring

variable
  (Residual : ∀ w (U : PreE7NonPairActionClass w),
    PreE7NumericalRankTailResidualChoice w U)

private theorem preE7NumericalRankTailMain_envelope :
    LinearLogSquaredMenuNumeratorBound 3
      (preE7NumericalRankTailD Residual) := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  cases j with
  | ordinary a =>
      simpa only [preE7NumericalRankTailD, zero_mul, zero_add, one_mul,
        hwb, Nat.cast_add, Nat.cast_ofNat] using
        (preE7NumericalOwnedPackage a).main_total_bound (n - w)
  | b6 | y1 | sns2 => positivity
  | terminal U =>
      simpa only [preE7NumericalRankTailD, zero_mul, zero_add, one_mul,
        hwb, Nat.cast_add, Nat.cast_ofNat] using
        (Residual w U).main_total_bound (n - w)

theorem preE7NumericalRankTail_mainMenu
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3 (preE7NumericalRankTailD Residual)
      preE7NumericalRankTailA :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    (preE7NumericalRankTailD_nonneg Residual)
    (fun w j => by
      change (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7NumericalRankTailAction w j : Set (Equiv.Perm (Fin w))))
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NumericalRankTailAction w j : Set (Equiv.Perm (Fin w))))))
    (preE7NumericalRankTailIndex_subquadratic hLMM)
    (preE7NumericalRankTailMain_envelope Residual)

private def preE7NumericalRankTailParameterTheta (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .ordinary a => (preE7NumericalOwnedPackage a).package.certificate.theta
  | .b6 _ | .y1 _ | .sns2 _ => 0
  | .terminal U => (Residual w U).theta

private theorem preE7NumericalRankTail_entryParameters :
    ∀ w j, PreE7CharacterEntryParameters preE7CharacterRho w
      (preE7NumericalRankTailV Residual w j)
      (preE7NumericalRankTailEta Residual w j)
      (preE7NumericalRankTailDelta Residual w j)
      (preE7NumericalRankTailCutoff Residual w j)
      (preE7NumericalRankTailAlpha Residual w j)
      (preE7NumericalRankTailParameterTheta Residual w j) := by
  intro w j
  cases j with
  | ordinary a => exact (preE7NumericalOwnedPackage a).parameters
  | b6 a | y1 a | sns2 a =>
      exact preE7EmptyCell_entryParameters
        (preE7NonPairAction_width_three_le a.2.1)
  | terminal U => exact (Residual w U).parameters

theorem preE7NumericalRankTail_parameterBound :
    GrowingQuotientParameterBound preE7CharacterRho
      (preE7NumericalRankTailV Residual)
      (preE7NumericalRankTailEta Residual)
      (preE7NumericalRankTailDelta Residual)
      (preE7NumericalRankTailCutoff Residual)
      (preE7NumericalRankTailAlpha Residual) :=
  (growingQuotientParameterBound_of_entryParameters
    (preE7NumericalRankTail_entryParameters Residual)).1

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
