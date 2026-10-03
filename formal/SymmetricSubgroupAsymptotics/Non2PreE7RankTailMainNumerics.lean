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
            (PreE7Sns2OwnedIndex w ⊕ PreE7NumericalTerminalIndex w))) where
  toFun
    | .ordinary a => .inl a
    | .b6 a => .inr (.inl a)
    | .y1 a => .inr (.inr (.inl a))
    | .sns2 a => .inr (.inr (.inr (.inl a)))
    | .terminal t => .inr (.inr (.inr (.inr t)))
  invFun
    | .inl a => .ordinary a
    | .inr (.inl a) => .b6 a
    | .inr (.inr (.inl a)) => .y1 a
    | .inr (.inr (.inr (.inl a))) => .sns2 a
    | .inr (.inr (.inr (.inr t))) => .terminal t
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
  have hterminal : Nat.card (PreE7NumericalTerminalIndex w) ≤
      Nat.card (PreE7NonPairActionClass w) :=
    Nat.card_le_card_of_injective
      (fun t : PreE7NumericalTerminalIndex w => t.action) (by
        intro a b h
        cases a
        cases b
        simp_all only [PreE7NumericalTerminalIndex.mk.injEq])
  have heq : Nat.card (PreE7NumericalRankTailIndex w) =
      Nat.card (PreE7NumericalOwnedIndex w) +
        (Nat.card (PreE7B6OwnedIndex w) +
          (Nat.card (PreE7Y1OwnedIndex w) +
            (Nat.card (PreE7Sns2OwnedIndex w) +
              Nat.card (PreE7NumericalTerminalIndex w)))) := by
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
          (Nat.add_le_add hy1 (Nat.add_le_add hsns2
            hterminal)))
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
  (Residual : PreE7NumericalRankTailResidualData)

private theorem preE7NumericalRankTailMain_envelope :
    SubquadraticLinearLogSquaredMenuNumeratorBound 3
      (preE7NumericalRankTailD Residual) := by
  intro ε hε
  obtain ⟨K, L, C, hK, hL, hC, hentry⟩ :=
    preE7NumericalOwned_main_envelope ε hε
  obtain ⟨Kaff, hKaff1, hAff⟩ :=
    PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost_rpow_envelope hε
  let K' := max (max K Kaff) 1
  let C' := max C (max 16 (8 / Real.log 2 ^ 2))
  have hK' : 0 ≤ K' := hK.trans ((le_max_left K Kaff).trans (le_max_left _ _))
  have hKle : K ≤ K' := (le_max_left K Kaff).trans (le_max_left _ _)
  have hKaffle : Kaff ≤ K' := (le_max_right K Kaff).trans (le_max_left _ _)
  have hKone : 1 ≤ K' := le_max_right _ _
  have hC' : 0 ≤ C' := hC.trans (le_max_left _ _)
  have hCle : C ≤ C' := le_max_left _ _
  have h16le : (16 : ℝ) ≤ C' :=
    (le_max_left 16 (8 / Real.log 2 ^ 2)).trans (le_max_right _ _)
  have h8logle : 8 / Real.log 2 ^ 2 ≤ C' :=
    (le_max_right 16 (8 / Real.log 2 ^ 2)).trans (le_max_right _ _)
  refine ⟨K', L, C', hK', hL, hC', ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
  have hexpMono :
      ε * (w : ℝ) ^ 2 + L * w + C * w * Real.log ((n : ℝ) + 2) ^ 2 ≤
        ε * (w : ℝ) ^ 2 + L * w + C' * w * Real.log ((n : ℝ) + 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hCle (mul_nonneg hw0 hlog0)]
  cases j with
  | ordinary a =>
      have hold := hentry n w hw a
      calc
        _ ≤ K * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 + L * w +
              C * w * Real.log ((n : ℝ) + 2) ^ 2) := hold
        _ ≤ K' * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 + L * w +
              C' * w * Real.log ((n : ℝ) + 2) ^ 2) := by
          calc
            _ ≤ K' * (2 : ℝ) ^
                (ε * (w : ℝ) ^ 2 + L * w +
                  C * w * Real.log ((n : ℝ) + 2) ^ 2) :=
              mul_le_mul_of_nonneg_right hKle (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpMono) hK'
  | b6 | y1 | sns2 =>
      simp only [preE7NumericalRankTailD]
      exact mul_nonneg hK'
        (Real.rpow_nonneg (by norm_num) _)
  | terminal t =>
      rcases (Residual w t).main_total_growth with hmain | haffine
      · have hold := hmain (n - w)
        have hold' : (Residual w t).D (n - w) ≤ (2 : ℝ) ^
            (16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2) := by
          simpa only [hwb, Nat.cast_add, Nat.cast_ofNat] using hold
        have hexp : 16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
            ε * (w : ℝ) ^ 2 + L * w +
              C' * w * Real.log ((n : ℝ) + 2) ^ 2 := by
          nlinarith [mul_nonneg hε.le (sq_nonneg (w : ℝ)),
            mul_nonneg hL hw0,
            mul_le_mul_of_nonneg_right h16le (mul_nonneg hw0 hlog0)]
        have hpow : (2 : ℝ) ^
              (16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2) ≤
            (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 + L * w +
                C' * w * Real.log ((n : ℝ) + 2) ^ 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        simpa only [preE7NumericalRankTailD] using
          hold'.trans (hpow.trans (by
            nth_rewrite 1 [← one_mul ((2 : ℝ) ^ _)]
            exact mul_le_mul_of_nonneg_right hKone (by positivity)))
      · have hold := haffine (n - w)
        have hw1 : 1 ≤ w := by
          have := (Finset.mem_Ico.mp hw).1
          omega
        have hcost := hAff w hw1
        have hsource := affineSourceLog_le_widthLogSquared n w hw
        have hCsrc : (8 / Real.log 2 ^ 2) * w *
              Real.log ((n : ℝ) + 2) ^ 2 ≤
            C' * w * Real.log ((n : ℝ) + 2) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right h8logle
            (mul_nonneg hw0 hlog0)]
        have htarget : 0 ≤ K' := hK'
        have hLw : 0 ≤ L * (w : ℝ) := mul_nonneg hL hw0
        calc
          _ ≤ (2 : ℝ) ^
              (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
                8 * (w : ℝ) * Real.logb 2 ((n - w + 1 : ℕ) : ℝ)) := by
            simpa only [preE7NumericalRankTailD, Nat.cast_add, Nat.cast_one] using hold
          _ = (2 : ℝ) ^
              PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w *
              (2 : ℝ) ^ (8 * (w : ℝ) *
                Real.logb 2 ((n - w + 1 : ℕ) : ℝ)) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          _ ≤ (Kaff * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) *
              (2 : ℝ) ^ ((8 / Real.log 2 ^ 2) * w *
                Real.log ((n : ℝ) + 2) ^ 2) :=
            mul_le_mul hcost
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsource)
              (by positivity) (by positivity)
          _ ≤ (K' * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) *
              (2 : ℝ) ^ (C' * w * Real.log ((n : ℝ) + 2) ^ 2) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_right hKaffle (by positivity))
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hCsrc)
              (by positivity) (by positivity)
          _ = K' * (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 +
                C' * w * Real.log ((n : ℝ) + 2) ^ 2) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            ring
          _ ≤ K' * (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 + L * w +
                C' * w * Real.log ((n : ℝ) + 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ htarget
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            nlinarith

theorem preE7NumericalRankTail_mainMenu
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3 (preE7NumericalRankTailD Residual)
      preE7NumericalRankTailA :=
  growingMenuMassBound_of_subquadraticLinearLogSquared (by omega) _ _
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
  | .terminal t => (Residual w t).theta

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
  | terminal t => exact (Residual w t).parameters

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
