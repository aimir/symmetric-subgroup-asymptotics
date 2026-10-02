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

variable (lit : PreE7CharacterLiterature)
  (Residual : PreE7NumericalRankTailResidualData)

private def rankTailTargetT (w : ℕ) :
    (PreE7RankTailSecondaryBaseIndex w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℕ → ℝ
  | .inl (.inl a) => preE7NumericalSns2T w (.inl a)
  | .inl (.inr (.inl a)) => preE7NumericalSns2T w (.inr (.inl a))
  | .inl (.inr (.inr _)) => 0
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
  | .inl (.inr (.inr _)) => 0
  | .inr (.inl _) => 4 / 3
  | .inr (.inr _) => 153 / 200

private theorem preE7RankTail_coldWidthSum_split (b w : ℕ) :
    growingQuotientColdWidthSum b w
        (preE7NumericalRankTailT lit w) (preE7NumericalRankTailA w)
        (preE7NumericalRankTailTheta w) =
      growingQuotientColdWidthSum b w (preE7NumericalSns2T w)
          (preE7NumericalSns2A w) (preE7NumericalSns2Theta w) +
        growingQuotientColdWidthSum b w
          (fun i : PreE7B6MenuIndex w => preE7B6MenuCoefficient lit i)
          (fun i => preE7B6MenuNormalizer i) (fun _ => 4 / 3) +
        growingQuotientColdWidthSum b w
          (fun i : PreE7Y1MenuIndex w => preE7Y1MenuCoefficient lit i)
          (fun i => preE7Y1MenuNormalizer i) (fun _ => 153 / 200) := by
  unfold growingQuotientColdWidthSum
  let e := preE7RankTailSecondaryIndexEquiv w
  calc
    (∑ i : PreE7NumericalRankTailIndex w,
        fusionWidthColdKernel b w (preE7NumericalRankTailT lit w i b)
          (preE7NumericalRankTailA w i)
          (preE7NumericalRankTailTheta w i)) =
      ∑ z, fusionWidthColdKernel b w (rankTailTargetT lit w z b)
        (rankTailTargetA w z) (rankTailTargetTheta w z) := by
          exact Fintype.sum_equiv e _ _ (fun i => by
            cases i <;> rfl)
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      simp only [rankTailTargetT, rankTailTargetA, rankTailTargetTheta,
        preE7NumericalSns2T, preE7NumericalSns2Theta,
        fusionWidthColdKernel, zero_div, mul_zero, zero_mul,
        Pi.zero_apply, Finset.sum_const_zero, mul_comm]
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
    growingQuotientColdRow 3 (preE7NumericalRankTailT lit)
        preE7NumericalRankTailA preE7NumericalRankTailTheta n b =
      growingQuotientColdRow 3 preE7NumericalSns2T
          preE7NumericalSns2A preE7NumericalSns2Theta n b +
        growingQuotientColdRow 3
          (fun w i => preE7B6MenuCoefficient lit (w := w) i)
          (fun w i => preE7B6MenuNormalizer (w := w) i)
          (fun _ _ => 4 / 3) n b +
        growingQuotientColdRow 3
          (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
          (fun w i => preE7Y1MenuNormalizer (w := w) i)
          (fun _ _ => 153 / 200) n b := by
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
              (fun i => preE7Y1MenuNormalizer i) (fun _ => 153 / 200)
         else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs
      · exact preE7RankTail_coldWidthSum_split lit b w
      · rfl
    _ = _ := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
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
    growingQuotientSecondaryError 3 (preE7NumericalRankTailT lit)
        (preE7NumericalRankTailX lit Residual) preE7NumericalRankTailA
        preE7NumericalRankTailTheta n =
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
        growingQuotientExceptionalTotal 3
          (fun w t => (Residual w t).X) n := by
  unfold growingQuotientSecondaryError
  rw [preE7RankTail_exceptionalTotal_split lit Residual]
  have hcold :
      (∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 (preE7NumericalRankTailT lit)
              preE7NumericalRankTailA preE7NumericalRankTailTheta n b *
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
              (fun _ _ => 153 / 200) n b) * ordinarySubgroupRatio b) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [preE7RankTail_coldRow_split]
  rw [hcold]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- The complete ordinary/B6/Y1/SNS2 secondary contribution is
exponentially contractive. -/
noncomputable def preE7NumericalRankTail_secondary
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3
        (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit Residual)
        preE7NumericalRankTailA preE7NumericalRankTailTheta) := by
  let Ebase := preE7NumericalSns2_secondary hLMM hcoarse hFS hOuter
  let Eb6 := preE7B6Secondary_exponentialForwardEstimate lit hcoarse
  let Ey1 := preE7Y1Secondary_exponentialForwardEstimate lit hcoarse
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
      (OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ebase Eb6) Ey1)
    Eterminal
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => le_of_eq (preE7RankTail_secondary_split lit Residual n))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
