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
noncomputable def preE7RankTailSecondaryIndexEquiv (w : ℕ) :
    PreE7NumericalRankTailIndex w ≃
      PreE7NumericalSns2Index w ⊕
        (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w) where
  toFun
    | .ordinary a => .inl (.inl a)
    | .b6 a => .inr (.inl (preE7B6OwnedMenuIndex a))
    | .y1 a => .inr (.inr (preE7Y1OwnedMenuIndex a))
    | .sns2 a => .inl (.inr (.inl a))
    | .terminal U => .inl (.inr (.inr U))
  invFun
    | .inl (.inl a) => .ordinary a
    | .inl (.inr (.inl a)) => .sns2 a
    | .inl (.inr (.inr U)) => .terminal U
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

private def rankTailTargetT (w : ℕ) :
    (PreE7NumericalSns2Index w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℕ → ℝ
  | .inl a => preE7NumericalSns2T w a
  | .inr (.inl a) => preE7B6MenuCoefficient lit a
  | .inr (.inr a) => preE7Y1MenuCoefficient lit a

private def rankTailTargetX (w : ℕ) :
    (PreE7NumericalSns2Index w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℕ → ℝ
  | .inl a => preE7NumericalSns2X w a
  | .inr (.inl a) => preE7B6MenuExceptional lit a
  | .inr (.inr a) => preE7Y1MenuExceptional lit a

private def rankTailTargetA (w : ℕ) :
    (PreE7NumericalSns2Index w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℝ
  | .inl a => preE7NumericalSns2A w a
  | .inr (.inl a) => preE7B6MenuNormalizer a
  | .inr (.inr a) => preE7Y1MenuNormalizer a

private def rankTailTargetTheta (w : ℕ) :
    (PreE7NumericalSns2Index w ⊕
      (PreE7B6MenuIndex w ⊕ PreE7Y1MenuIndex w)) → ℝ
  | .inl a => preE7NumericalSns2Theta w a
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
      simp only [rankTailTargetT, rankTailTargetA, rankTailTargetTheta]
      ring

private theorem preE7RankTail_exceptionalWidthSum_split (b w : ℕ) :
    (∑ i : PreE7NumericalRankTailIndex w,
        preE7NumericalRankTailX lit w i b) =
      (∑ i : PreE7NumericalSns2Index w, preE7NumericalSns2X w i b) +
        (∑ i : PreE7B6MenuIndex w, preE7B6MenuExceptional lit i b) +
        ∑ i : PreE7Y1MenuIndex w, preE7Y1MenuExceptional lit i b := by
  let e := preE7RankTailSecondaryIndexEquiv w
  calc
    _ = ∑ z, rankTailTargetX lit w z b := by
      exact Fintype.sum_equiv e _ _ (fun i => by
        cases i <;> rfl)
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      simp only [rankTailTargetX]
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
    growingQuotientExceptionalTotal 3 (preE7NumericalRankTailX lit) n =
      growingQuotientExceptionalTotal 3 preE7NumericalSns2X n +
        growingQuotientExceptionalTotal 3
          (fun w i => preE7B6MenuExceptional lit (w := w) i) n +
        growingQuotientExceptionalTotal 3
          (fun w i => preE7Y1MenuExceptional lit (w := w) i) n := by
  unfold growingQuotientExceptionalTotal
  calc
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
        ((∑ i : PreE7NumericalSns2Index w,
            preE7NumericalSns2X w i (n - w)) +
          (∑ i : PreE7B6MenuIndex w,
            preE7B6MenuExceptional lit i (n - w)) +
          ∑ i : PreE7Y1MenuIndex w,
            preE7Y1MenuExceptional lit i (n - w)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact preE7RankTail_exceptionalWidthSum_split lit (n - w) w
    _ = _ := by simp only [Finset.sum_add_distrib]

private theorem preE7RankTail_secondary_split (n : ℕ) :
    growingQuotientSecondaryError 3 (preE7NumericalRankTailT lit)
        (preE7NumericalRankTailX lit) preE7NumericalRankTailA
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
          (fun _ _ => 153 / 200) n := by
  unfold growingQuotientSecondaryError
  rw [preE7RankTail_exceptionalTotal_split]
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
        (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit)
        preE7NumericalRankTailA preE7NumericalRankTailTheta) := by
  let Ebase := preE7NumericalSns2_secondary hLMM hcoarse hFS hOuter
  let Eb6 := preE7B6Secondary_exponentialForwardEstimate lit hcoarse
  let Ey1 := preE7Y1Secondary_exponentialForwardEstimate lit hcoarse
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ebase Eb6) Ey1
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => le_of_eq (preE7RankTail_secondary_split lit n))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
