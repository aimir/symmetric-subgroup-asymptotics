import SymmetricSubgroupAsymptotics.Non2PreE7RankTailMainNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2SecondaryNumerics

/-!
# Secondary numerics for the complete rank-tail catalogue

The enlarged secondary row is reindexed exactly as the disjoint sum of the
already-closed ordinary-plus-SNS2 menu and the fixed-width B6 and Y1 menus.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

noncomputable def preE7B6OwnedMenuEquiv (w : ℕ) :
    PreE7B6OwnedIndex w ≃ PreE7B6MenuIndex w where
  toFun := preE7B6OwnedMenuIndex
  invFun := fun i => ⟨preE7B6OwnerIndex, i.1,
    preE7B6OwnerIndex_family, i.2⟩
  left_inv := by
    rintro ⟨k, ⟨U, hk, hsource⟩⟩
    have hko : k = preE7B6OwnerIndex := by
      apply preE7NoPairNoC3EarlierOwnerEquiv.injective
      simpa only [preE7B6OwnerIndex_family] using hk
    subst k
    rfl
  right_inv := by intro i; apply Subtype.ext; rfl

noncomputable def preE7Y1OwnedMenuEquiv (w : ℕ) :
    PreE7Y1OwnedIndex w ≃ PreE7Y1MenuIndex w where
  toFun := preE7Y1OwnedMenuIndex
  invFun := fun i => ⟨preE7Y1OwnerIndex, i.1,
    preE7Y1OwnerIndex_family, i.2⟩
  left_inv := by
    rintro ⟨k, ⟨U, hk, hsource⟩⟩
    have hko : k = preE7Y1OwnerIndex := by
      apply preE7NoPairNoC3EarlierOwnerEquiv.injective
      simpa only [preE7Y1OwnerIndex_family] using hk
    subst k
    rfl
  right_inv := by intro i; apply Subtype.ext; rfl

/-- Forget the presentation tags while retaining each literal action once. -/
private abbrev PreE7RankTailSecondaryBaseIndex (w : ℕ) :=
  PreE7NumericalOwnedIndex w ⊕
    (PreE7Sns2OwnedIndex w ⊕ PreE7NumericalTerminalIndex w)

noncomputable def preE7RankTailSecondaryIndexEquiv (w : ℕ) :
    PreE7NumericalRankTailIndex w ≃
      PreE7RankTailSecondaryBaseIndex w ⊕
        (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w) where
  toFun
    | .ordinary a => .inl (.inl a)
    | .b6 a => .inr (.inl (preE7B6OwnedMenuIndex a))
    | .y1 a => .inr (.inr (preE7Y1OwnedMenuIndex a))
    | .sns2 a => .inl (.inr (.inl a))
    | .terminal t => .inl (.inr (.inr t))
  invFun
    | .inl (.inl a) => .ordinary a
    | .inl (.inr (.inl a)) => .sns2 a
    | .inl (.inr (.inr t)) => .terminal t
    | .inr (.inl a) => .b6 ((preE7B6OwnedMenuEquiv w).symm a)
    | .inr (.inr a) => .y1 ((preE7Y1OwnedMenuEquiv w).symm a)
  left_inv := by
    intro x
    cases x with
    | ordinary | sns2 | terminal => rfl
    | b6 a =>
        change PreE7NumericalRankTailIndex.b6
          ((preE7B6OwnedMenuEquiv w).symm
            (preE7B6OwnedMenuEquiv w a)) =
          PreE7NumericalRankTailIndex.b6 a
        rw [Equiv.symm_apply_apply]
    | y1 a =>
        change PreE7NumericalRankTailIndex.y1
          ((preE7Y1OwnedMenuEquiv w).symm
            (preE7Y1OwnedMenuEquiv w a)) =
          PreE7NumericalRankTailIndex.y1 a
        rw [Equiv.symm_apply_apply]
  right_inv := by
    intro x
    rcases x with a | a
    · rcases a with a | a
      · rfl
      · rcases a with a | U <;> rfl
    · rcases a with a | a
      · change Sum.inr (Sum.inl (preE7B6OwnedMenuEquiv w
          ((preE7B6OwnedMenuEquiv w).symm a))) = Sum.inr (Sum.inl a)
        rw [Equiv.apply_symm_apply]
      · change Sum.inr (Sum.inr (preE7Y1OwnedMenuEquiv w
          ((preE7Y1OwnedMenuEquiv w).symm a))) = Sum.inr (Sum.inr a)
        rw [Equiv.apply_symm_apply]

@[simp] private theorem preE7RankTailSecondaryIndexEquiv_ordinary
    (w : ℕ) (a : PreE7NumericalOwnedIndex w) :
    preE7RankTailSecondaryIndexEquiv w (.ordinary a) = .inl (.inl a) := rfl

@[simp] private theorem preE7RankTailSecondaryIndexEquiv_b6
    (w : ℕ) (a : PreE7B6OwnedIndex w) :
    preE7RankTailSecondaryIndexEquiv w (.b6 a) =
      .inr (.inl (preE7B6OwnedMenuIndex a)) := rfl

@[simp] private theorem preE7RankTailSecondaryIndexEquiv_y1
    (w : ℕ) (a : PreE7Y1OwnedIndex w) :
    preE7RankTailSecondaryIndexEquiv w (.y1 a) =
      .inr (.inr (preE7Y1OwnedMenuIndex a)) := rfl

@[simp] private theorem preE7RankTailSecondaryIndexEquiv_sns2
    (w : ℕ) (a : PreE7Sns2OwnedIndex w) :
    preE7RankTailSecondaryIndexEquiv w (.sns2 a) =
      .inl (.inr (.inl a)) := rfl

@[simp] private theorem preE7RankTailSecondaryIndexEquiv_terminal
    (w : ℕ) (t : PreE7NumericalTerminalIndex w) :
    preE7RankTailSecondaryIndexEquiv w (.terminal t) =
      .inl (.inr (.inr t)) := rfl

@[simp] private theorem preE7NumericalRankTailA_terminal
    (w : ℕ) (t : PreE7NumericalTerminalIndex w) :
    preE7NumericalRankTailA w (.terminal t) =
      Nat.card (Subgroup.normalizer
        (preE7NonPairAction w t.action : Set (Equiv.Perm (Fin w)))) := rfl

variable (lit : PreE7CharacterLiterature)
  (Residual : PreE7NumericalRankTailResidualData)

/-- The new additive tail carried only by terminal residual rows. -/
private def rankTailTerminalT (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℕ → ℝ
  | .terminal t => (Residual w t).T
  | _ => 0

/-- Its slope; nonterminal entries are zero rows. -/
private def rankTailTerminalTheta (w : ℕ) :
    PreE7NumericalRankTailIndex w → ℝ
  | .terminal t => (Residual w t).theta
  | _ => 0

private def rankTailTargetT (w : ℕ) :
    (PreE7RankTailSecondaryBaseIndex w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℕ → ℝ
  | .inl (.inl a) => preE7NumericalSns2T w (.inl a)
  | .inl (.inr (.inl a)) => preE7NumericalSns2T w (.inr (.inl a))
  | .inl (.inr (.inr t)) => (Residual w t).T
  | .inr (.inl a) => preE7B6MenuCoefficient lit a
  | .inr (.inr a) => preE7Y1MenuCoefficient lit a

private def rankTailTargetX (w : ℕ) :
    (PreE7RankTailSecondaryBaseIndex w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℕ → ℝ
  | .inl (.inl a) => preE7NumericalSns2X w (.inl a)
  | .inl (.inr (.inl a)) => preE7NumericalSns2X w (.inr (.inl a))
  | .inl (.inr (.inr t)) => (Residual w t).X
  | .inr (.inl a) => preE7B6MenuExceptional lit a
  | .inr (.inr a) => preE7Y1MenuExceptional lit a

private def rankTailTargetA (w : ℕ) :
    (PreE7RankTailSecondaryBaseIndex w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℝ
  | .inl (.inl a) => preE7NumericalSns2A w (.inl a)
  | .inl (.inr (.inl a)) => preE7NumericalSns2A w (.inr (.inl a))
  | .inl (.inr (.inr t)) =>
      Nat.card (Subgroup.normalizer
        (preE7NonPairAction w t.action : Set (Equiv.Perm (Fin w))))
  | .inr (.inl a) => preE7B6MenuNormalizer a
  | .inr (.inr a) => preE7Y1MenuNormalizer a

private def rankTailTargetTheta (w : ℕ) :
    (PreE7RankTailSecondaryBaseIndex w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℝ
  | .inl (.inl a) => preE7NumericalSns2Theta w (.inl a)
  | .inl (.inr (.inl a)) => preE7NumericalSns2Theta w (.inr (.inl a))
  | .inl (.inr (.inr t)) => (Residual w t).theta
  | .inr (.inl _) => 4 / 3
  | .inr (.inr _) => 153 / 200

/-- Expand the terminal-only row before it is combined with the other four
menus.  Keeping this as an explicit finite-sum identity avoids asking the
ring normalizer to recognize the terminal summand through the custom
five-constructor index. -/
private theorem rankTailTerminal_coldWidthSum_expand (b w : ℕ) :
    growingQuotientColdWidthSum b w (rankTailTerminalT Residual w)
        (preE7NumericalRankTailA w)
        (rankTailTerminalTheta Residual w) =
      ∑ t : PreE7NumericalTerminalIndex w,
        fusionWidthColdKernel b w ((Residual w t).T b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w t.action : Set (Equiv.Perm (Fin w)))))
          (Residual w t).theta := by
  unfold growingQuotientColdWidthSum
  let e := preE7RankTailSecondaryIndexEquiv w
  calc
    _ = ∑ z : PreE7RankTailSecondaryBaseIndex w ⊕
          (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w),
        match z with
        | .inl (.inr (.inr t)) =>
            fusionWidthColdKernel b w ((Residual w t).T b)
              (Nat.card (Subgroup.normalizer
                (preE7NonPairAction w t.action : Set (Equiv.Perm (Fin w)))))
              (Residual w t).theta
        | _ => 0 := by
          exact Fintype.sum_equiv e _ _ (fun i => by
            cases i <;>
              simp [e, rankTailTerminalT, rankTailTerminalTheta,
                fusionWidthColdKernel])
    _ = _ := by
      simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add,
        add_zero]

private theorem preE7RankTail_coldWidthSum_split (b w : ℕ) :
    growingQuotientColdWidthSum b w
        (preE7NumericalRankTailT lit Residual w) (preE7NumericalRankTailA w)
        (preE7NumericalRankTailTheta Residual w) =
      growingQuotientColdWidthSum b w (preE7NumericalSns2T w)
          (preE7NumericalSns2A w) (preE7NumericalSns2Theta w) +
        growingQuotientColdWidthSum b w
          (fun i : PreE7B6MenuIndex w => preE7B6MenuCoefficient lit i)
          (fun i => preE7B6MenuNormalizer i) (fun _ => 4 / 3) +
        growingQuotientColdWidthSum b w
          (fun i : PreE7Y1MenuIndex w => preE7Y1MenuCoefficient lit i)
          (fun i => preE7Y1MenuNormalizer i) (fun _ => 153 / 200) +
        growingQuotientColdWidthSum b w (rankTailTerminalT Residual w)
          (preE7NumericalRankTailA w)
          (rankTailTerminalTheta Residual w) := by
  rw [rankTailTerminal_coldWidthSum_expand Residual b w]
  unfold growingQuotientColdWidthSum
  let e := preE7RankTailSecondaryIndexEquiv w
  calc
    (∑ i : PreE7NumericalRankTailIndex w,
        fusionWidthColdKernel b w (preE7NumericalRankTailT lit Residual w i b)
          (preE7NumericalRankTailA w i)
          (preE7NumericalRankTailTheta Residual w i)) =
      ∑ z, fusionWidthColdKernel b w (rankTailTargetT lit Residual w z b)
        (rankTailTargetA w z) (rankTailTargetTheta Residual w z) := by
          exact Fintype.sum_equiv e _ _ (fun i => by
            cases i <;> rfl)
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      simp only [rankTailTargetT, rankTailTargetA, rankTailTargetTheta,
        preE7NumericalSns2T, preE7NumericalSns2Theta,
        fusionWidthColdKernel, zero_div, mul_zero, zero_mul,
        Finset.sum_const_zero, mul_comm]
      ring

private theorem preE7RankTail_exceptionalWidthSum_split (b w : ℕ) :
    (∑ i : PreE7NumericalRankTailIndex w,
        preE7NumericalRankTailX lit Residual w i b) =
      (∑ i : PreE7NumericalSns2Index w, preE7NumericalSns2X w i b) +
        (∑ i : PreE7B6MenuIndex w, preE7B6MenuExceptional lit i b) +
        (∑ i : PreE7Y1MenuIndex w, preE7Y1MenuExceptional lit i b) +
        ∑ t : PreE7NumericalTerminalIndex w, (Residual w t).X b := by
  let e := preE7RankTailSecondaryIndexEquiv w
  calc
    _ = ∑ z, rankTailTargetX lit Residual w z b := by
      exact Fintype.sum_equiv e _ _ (fun i => by
        cases i <;> rfl)
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      simp only [rankTailTargetX, preE7NumericalSns2X,
        Finset.sum_const_zero]
      ring

private theorem preE7RankTail_coldRow_split (n b : ℕ) :
    growingQuotientColdRow 3 (preE7NumericalRankTailT lit Residual)
        preE7NumericalRankTailA (preE7NumericalRankTailTheta Residual) n b =
      growingQuotientColdRow 3 preE7NumericalSns2T
          preE7NumericalSns2A preE7NumericalSns2Theta n b +
        growingQuotientColdRow 3
          (fun w i => preE7B6MenuCoefficient lit (w := w) i)
          (fun w i => preE7B6MenuNormalizer (w := w) i)
          (fun _ _ => 4 / 3) n b +
        growingQuotientColdRow 3
          (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
          (fun w i => preE7Y1MenuNormalizer (w := w) i)
          (fun _ _ => 153 / 200) n b +
        growingQuotientColdRow 3 (rankTailTerminalT Residual)
          preE7NumericalRankTailA (rankTailTerminalTheta Residual) n b := by
  unfold growingQuotientColdRow
  calc
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
        (if b + w = n then
          growingQuotientColdWidthSum b w (preE7NumericalSns2T w)
              (preE7NumericalSns2A w) (preE7NumericalSns2Theta w) +
            growingQuotientColdWidthSum b w
              (fun i : PreE7B6MenuIndex w => preE7B6MenuCoefficient lit i)
              (fun i => preE7B6MenuNormalizer i) (fun _ => 4 / 3) +
            growingQuotientColdWidthSum b w
              (fun i : PreE7Y1MenuIndex w => preE7Y1MenuCoefficient lit i)
              (fun i => preE7Y1MenuNormalizer i) (fun _ => 153 / 200) +
            growingQuotientColdWidthSum b w (rankTailTerminalT Residual w)
              (preE7NumericalRankTailA w)
              (rankTailTerminalTheta Residual w)
         else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs
      · exact preE7RankTail_coldWidthSum_split lit Residual b w
      · rfl
    _ = _ := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> ring

private theorem preE7RankTail_exceptionalTotal_split (n : ℕ) :
    growingQuotientExceptionalTotal 3
        (preE7NumericalRankTailX lit Residual) n =
      growingQuotientExceptionalTotal 3 preE7NumericalSns2X n +
        growingQuotientExceptionalTotal 3
          (fun w i => preE7B6MenuExceptional lit (w := w) i) n +
        growingQuotientExceptionalTotal 3
          (fun w i => preE7Y1MenuExceptional lit (w := w) i) n +
        growingQuotientExceptionalTotal 3
          (fun w t => (Residual w t).X) n := by
  unfold growingQuotientExceptionalTotal
  calc
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
        ((∑ i : PreE7NumericalSns2Index w,
            preE7NumericalSns2X w i (n - w)) +
          (∑ i : PreE7B6MenuIndex w,
            preE7B6MenuExceptional lit i (n - w)) +
          (∑ i : PreE7Y1MenuIndex w,
            preE7Y1MenuExceptional lit i (n - w)) +
          ∑ t : PreE7NumericalTerminalIndex w,
            (Residual w t).X (n - w)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact preE7RankTail_exceptionalWidthSum_split lit Residual (n - w) w
    _ = _ := by simp only [Finset.sum_add_distrib]

private theorem preE7RankTail_secondary_split (n : ℕ) :
    growingQuotientSecondaryError 3 (preE7NumericalRankTailT lit Residual)
        (preE7NumericalRankTailX lit Residual) preE7NumericalRankTailA
        (preE7NumericalRankTailTheta Residual) n =
      growingQuotientSecondaryError 3 preE7NumericalSns2T
          preE7NumericalSns2X preE7NumericalSns2A
          preE7NumericalSns2Theta n +
        growingQuotientSecondaryError 3
          (fun w i => preE7B6MenuCoefficient lit (w := w) i)
          (fun w i => preE7B6MenuExceptional lit (w := w) i)
          (fun w i => preE7B6MenuNormalizer (w := w) i)
          (fun _ _ => 4 / 3) n +
        growingQuotientSecondaryError 3
          (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
          (fun w i => preE7Y1MenuExceptional lit (w := w) i)
          (fun w i => preE7Y1MenuNormalizer (w := w) i)
          (fun _ _ => 153 / 200) n +
        (∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 (rankTailTerminalT Residual)
            preE7NumericalRankTailA (rankTailTerminalTheta Residual) n b *
              ordinarySubgroupRatio b) +
        growingQuotientExceptionalTotal 3
          (fun w t => (Residual w t).X) n := by
  unfold growingQuotientSecondaryError
  rw [preE7RankTail_exceptionalTotal_split lit Residual]
  have hcold :
      (∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 (preE7NumericalRankTailT lit Residual)
              preE7NumericalRankTailA (preE7NumericalRankTailTheta Residual) n b *
            ordinarySubgroupRatio b) =
        (∑ b ∈ Finset.range n,
          (growingQuotientColdRow 3 preE7NumericalSns2T
              preE7NumericalSns2A preE7NumericalSns2Theta n b +
            growingQuotientColdRow 3
              (fun w i => preE7B6MenuCoefficient lit (w := w) i)
              (fun w i => preE7B6MenuNormalizer (w := w) i)
              (fun _ _ => 4 / 3) n b +
            growingQuotientColdRow 3
              (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
              (fun w i => preE7Y1MenuNormalizer (w := w) i)
              (fun _ _ => 153 / 200) n b +
            growingQuotientColdRow 3 (rankTailTerminalT Residual)
              preE7NumericalRankTailA (rankTailTerminalTheta Residual) n b) *
                ordinarySubgroupRatio b) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [preE7RankTail_coldRow_split lit Residual n b]
  rw [hcold]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- The terminal-only additive coefficient is pointwise dominated by the
main coefficient whose menu mass is already controlled. -/
private theorem rankTailTerminalT_le_D :
    ∀ w (j : PreE7NumericalRankTailIndex w) b,
      rankTailTerminalT Residual w j b ≤
        preE7NumericalRankTailD Residual w j b := by
  intro w j b
  cases j with
  | ordinary a =>
      exact (preE7NumericalOwnedPackage a).package.certificate.D_nonneg b
  | b6 | y1 | sns2 => exact le_rfl
  | terminal t => exact (Residual w t).T_le_D b

private theorem rankTailTerminalT_nonneg :
    ∀ w (j : PreE7NumericalRankTailIndex w) b,
      0 ≤ rankTailTerminalT Residual w j b := by
  intro w j b
  cases j with
  | terminal t => exact (Residual w t).T_nonneg b
  | ordinary | b6 | y1 | sns2 => exact le_rfl

/-- A pointwise smaller coefficient inherits a growing menu-mass bound. -/
private theorem growingMenuMassBound_mono
    {ι : ℕ → Type*} [∀ w, Fintype (ι w)]
    {w0 : ℕ} {D T : ∀ w, ι w → ℕ → ℝ} {A : ∀ w, ι w → ℝ}
    (hT : ∀ w i b, T w i b ≤ D w i b)
    (hA : ∀ w i, 0 < A w i)
    (hD : GrowingMenuMassBound w0 D A) :
    GrowingMenuMassBound w0 T A := by
  intro gamma hgamma
  filter_upwards [hD gamma hgamma] with n hn
  intro w hw
  exact (Finset.sum_le_sum (fun i _ =>
    div_le_div_of_nonneg_right (hT w i (n - w)) (hA w i).le)).trans
      (hn w hw)

private theorem rankTailTerminal_menu
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3 (rankTailTerminalT Residual)
      preE7NumericalRankTailA :=
  growingMenuMassBound_mono (rankTailTerminalT_le_D Residual)
    preE7NumericalRankTailA_pos
    (preE7NumericalRankTail_mainMenu Residual hLMM)

private theorem rankTailTerminal_gap :
    ∀ w (j : PreE7NumericalRankTailIndex w),
      rankTailTerminalTheta Residual w j ≤
        (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  intro w j
  have hzero := (preE7EmptyCell_entryParameters
    (preE7NonPairAction_width_three_le
      (preE7NumericalRankTailActionClass j))).tail_gap
  cases j with
  | terminal t => exact (Residual w t).parameters.tail_gap
  | ordinary | b6 | y1 | sns2 =>
      simpa only [rankTailTerminalTheta] using hzero

/-- The complete ordinary/B6/Y1/SNS2 secondary contribution, together with
the additive tail of every terminal residual row, is exponentially
contractive. -/
noncomputable def preE7NumericalRankTail_secondary
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3
        (preE7NumericalRankTailT lit Residual) (preE7NumericalRankTailX lit Residual)
        preE7NumericalRankTailA (preE7NumericalRankTailTheta Residual)) := by
  let Ebase := preE7NumericalSns2_secondary hLMM hcoarse hFS hOuter
  let Eb6 := preE7B6Secondary_exponentialForwardEstimate lit hcoarse
  let Ey1 := preE7Y1Secondary_exponentialForwardEstimate lit hcoarse
  let terminalColdError : ℕ → ℝ := fun n =>
    ∑ b ∈ Finset.range n,
      growingQuotientColdRow 3 (rankTailTerminalT Residual)
        preE7NumericalRankTailA (rankTailTerminalTheta Residual) n b *
          ordinarySubgroupRatio b
  let EterminalCold := growingColdOnly_exponentialForwardEstimate
    terminalColdError 3 (rankTailTerminalT Residual)
      preE7NumericalRankTailA (rankTailTerminalTheta Residual)
      (by norm_num [preE7CharacterRho])
      (by norm_num [preE7CharacterRho]) (by omega)
      (rankTailTerminalT_nonneg Residual) preE7NumericalRankTailA_pos
      (rankTailTerminal_gap Residual) (rankTailTerminal_menu Residual hLMM)
      (Filter.Eventually.of_forall (fun _ => le_rfl))
  let Eterminal :=
    (exponentialScalarBound_growingQuotientExceptionalTotal 3 12288
      (fun w t => (Residual w t).X)
      (fun w t => (Residual w t).exceptional hcoarse)
      (fun w t hw => by
        rcases (Residual w t).exceptional_support with hzero | hsmall
        · exact hzero
        · omega)).toForwardEstimate
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
      (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
        (OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ebase Eb6) Ey1)
        EterminalCold)
    Eterminal
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by
      simpa only [terminalColdError] using
        le_of_eq (preE7RankTail_secondary_split lit Residual n))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
