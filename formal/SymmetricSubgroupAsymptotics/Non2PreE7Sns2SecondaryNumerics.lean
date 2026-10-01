import SymmetricSubgroupAsymptotics.Non2PreE7Sns2MainNumerics

/-!
# Global secondary numerics for the disjoint numerical/SNS2 catalogue

The ordinary numerical owners are summed by the additive-tail interface.
The SNS2 owners are reindexed onto the literal all-width SNS2 menu, where the
cold row and correlated hot scalar are estimated together.  The terminal
row contributes no secondary term.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The retained owner label of an SNS2 action is unique, so forgetting it is
an equivalence onto the literal SNS2 action menu. -/
noncomputable def preE7Sns2OwnedMenuEquiv (w : ℕ) :
    PreE7Sns2OwnedIndex w ≃ PreE7Sns2MenuIndex w where
  toFun := preE7Sns2OwnedMenuIndex
  invFun := fun i =>
    ⟨preE7Sns2OwnerIndex, i.1, preE7Sns2OwnerIndex_family, i.2⟩
  left_inv := by
    rintro ⟨k, ⟨U, hk, hsource⟩⟩
    have hko : k = preE7Sns2OwnerIndex := by
      apply preE7NoPairNoC3EarlierOwnerEquiv.injective
      simpa only [preE7Sns2OwnerIndex_family] using hk
    subst k
    rfl
  right_inv := by
    intro i
    apply Subtype.ext
    rfl

private theorem preE7Sns2MenuIndex_empty_below_five
    {w : ℕ} (hw : w < 5) (i : PreE7Sns2MenuIndex w) : False := by
  have hwidth := (preE7Sns2MenuSource i).width_lower
  omega

private theorem preE7Sns2_coldWidthSum_zero_below_five
    {w b : ℕ} (hw : w < 5) :
    growingQuotientColdWidthSum b w
        (fun i : PreE7Sns2MenuIndex w => preE7Sns2MenuCoefficient i)
        (fun i => preE7Sns2MenuNormalizer i)
        (fun i => preE7Sns2MenuSlope i) = 0 := by
  unfold growingQuotientColdWidthSum
  apply Finset.sum_eq_zero
  intro i _
  exact False.elim (preE7Sns2MenuIndex_empty_below_five hw i)

private theorem preE7Sns2_exceptionalWidthSum_zero_below_five
    {w b : ℕ} (hw : w < 5) :
    (∑ i : PreE7Sns2MenuIndex w, preE7Sns2MenuExceptional i b) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact False.elim (preE7Sns2MenuIndex_empty_below_five hw i)

private theorem preE7Sns2_coldRow_three_eq_five (n b : ℕ) :
    growingQuotientColdRow 3
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n b =
      growingQuotientColdRow 5
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n b := by
  unfold growingQuotientColdRow
  symm
  apply Finset.sum_subset
  · intro w hw
    simp only [Finset.mem_Ico] at hw ⊢
    omega
  · intro w hw3 hw5
    have hwlt : w < 5 := by
      simp only [Finset.mem_Ico] at hw3 hw5
      omega
    rw [preE7Sns2_coldWidthSum_zero_below_five hwlt]
    split_ifs <;> rfl

private theorem preE7Sns2_exceptionalTotal_three_eq_five (n : ℕ) :
    growingQuotientExceptionalTotal 3
        (fun w i => preE7Sns2MenuExceptional (w := w) i) n =
      growingQuotientExceptionalTotal 5
        (fun w i => preE7Sns2MenuExceptional (w := w) i) n := by
  unfold growingQuotientExceptionalTotal
  symm
  apply Finset.sum_subset
  · intro w hw
    simp only [Finset.mem_Ico] at hw ⊢
    omega
  · intro w hw3 hw5
    have hwlt : w < 5 := by
      simp only [Finset.mem_Ico] at hw3 hw5
      omega
    exact preE7Sns2_exceptionalWidthSum_zero_below_five hwlt

private theorem preE7Sns2_secondary_three_eq_five (n : ℕ) :
    growingQuotientSecondaryError 3
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuExceptional (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n =
      growingQuotientSecondaryError 5
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuExceptional (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n := by
  unfold growingQuotientSecondaryError
  rw [preE7Sns2_exceptionalTotal_three_eq_five]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [preE7Sns2_coldRow_three_eq_five]

private def preE7NumericalOwnedT (w : ℕ)
    (j : PreE7NumericalOwnedIndex w) (b : ℕ) : ℝ :=
  (preE7NumericalOwnedPackage j).package.certificate.T b

private def preE7NumericalOwnedX (w : ℕ)
    (j : PreE7NumericalOwnedIndex w) (b : ℕ) : ℝ :=
  (preE7NumericalOwnedPackage j).package.certificate.X b

private def preE7NumericalOwnedA (w : ℕ)
    (j : PreE7NumericalOwnedIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairAction w j.2.1 : Set (Equiv.Perm (Fin w))))

private def preE7NumericalOwnedTheta (w : ℕ)
    (j : PreE7NumericalOwnedIndex w) : ℝ :=
  (preE7NumericalOwnedPackage j).package.certificate.theta

private theorem preE7NumericalOwnedT_nonneg :
    ∀ w j b, 0 ≤ preE7NumericalOwnedT w j b := by
  intro w j b
  exact (preE7NumericalOwnedPackage j).package.certificate.T_nonneg b

private theorem preE7NumericalOwnedA_pos :
    ∀ w j, 0 < preE7NumericalOwnedA w j := by
  intro w j
  unfold preE7NumericalOwnedA
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (preE7NonPairAction w j.2.1 : Set (Equiv.Perm (Fin w)))))

private theorem preE7NumericalOwnedIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    SubquadraticMenuIndexCount PreE7NumericalOwnedIndex := by
  intro epsilon hepsilon
  obtain ⟨B, hB, hcount⟩ := hLMM epsilon hepsilon
  refine ⟨(preE7NoPairNoC3EarlierOwnerCount : ℝ) * B,
    mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro w
  have howned : Nat.card (PreE7NumericalOwnedIndex w) ≤
      preE7NoPairNoC3EarlierOwnerCount *
        Nat.card (PreE7NonPairActionClass w) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : Fin preE7NoPairNoC3EarlierOwnerCount,
          Nat.card (PreE7NonPairActionClass w) :=
        Finset.sum_le_sum (fun _ _ => Finite.card_subtype_le _)
      _ = _ := by simp
  have haction := (preE7NonPairActionClass_card_le_preE7 w).trans
    (preE7ActionClass_card_le_labelled w)
  calc
    (Nat.card (PreE7NumericalOwnedIndex w) : ℝ) ≤
        (preE7NoPairNoC3EarlierOwnerCount : ℝ) *
          (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
      exact_mod_cast howned
    _ ≤ (preE7NoPairNoC3EarlierOwnerCount : ℝ) *
        (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast haction)
        (Nat.cast_nonneg _)
    _ ≤ (preE7NoPairNoC3EarlierOwnerCount : ℝ) *
        (B * (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (Nat.cast_nonneg _)
    _ = ((preE7NoPairNoC3EarlierOwnerCount : ℝ) * B) *
        (2 : ℝ) ^ (epsilon * (w : ℝ) ^ 2) := by ring

private theorem preE7NumericalOwnedTail_envelope :
    LinearLogSquaredMenuNumeratorBound 3 preE7NumericalOwnedT := by
  refine ⟨1, 0, 16, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n w hw j
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  simpa only [preE7NumericalOwnedT, zero_mul, zero_add, one_mul, hwb,
      Nat.cast_add, Nat.cast_ofNat] using
    (preE7NumericalOwnedPackage j).tail_total_bound (n - w)

private theorem preE7NumericalOwned_tailGap :
    ∀ w j, preE7NumericalOwnedTheta w j ≤
      (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4 := by
  exact (growingQuotientParameterBound_of_entryParameters
    (fun w j => (preE7NumericalOwnedPackage j).parameters)).2

private theorem preE7NumericalOwned_tailMenu
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    GrowingMenuMassBound 3 preE7NumericalOwnedT preE7NumericalOwnedA :=
  growingMenuMassBound_of_linearLogSquared (by omega) _ _
    preE7NumericalOwnedT_nonneg
    (fun w j => by
      have h := preE7NumericalOwnedA_pos w j
      unfold preE7NumericalOwnedA at h ⊢
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairAction w j.2.1 : Set (Equiv.Perm (Fin w))))))
    (preE7NumericalOwnedIndex_subquadratic hLMM)
    preE7NumericalOwnedTail_envelope

private noncomputable def preE7NumericalOwned_exceptional
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ExponentialScalarBound
      (growingQuotientExceptionalTotal 3 preE7NumericalOwnedX) := by
  apply exponentialScalarBound_growingQuotientExceptionalTotal 3 12288
  · intro w j
    exact (preE7NumericalOwnedPackage j).package.exceptional hcoarse
  · intro w j hw
    change (preE7NumericalOwnedPackage j).package.certificate.X = 0
    rcases (preE7NumericalOwnedPackage j).package.exceptional_support with
      hzero | hwidth
    · exact hzero
    · omega

private noncomputable def preE7NumericalOwned_secondary
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3 preE7NumericalOwnedT
        preE7NumericalOwnedX preE7NumericalOwnedA
        preE7NumericalOwnedTheta) := by
  let tailError : ℕ → ℝ := fun n =>
    ∑ b ∈ Finset.range n,
      growingQuotientColdRow 3 preE7NumericalOwnedT
          preE7NumericalOwnedA preE7NumericalOwnedTheta n b *
        ordinarySubgroupRatio b
  have htailPhysical : GrowingColdOnlyPhysicalBound tailError 3
      preE7NumericalOwnedT preE7NumericalOwnedA
        preE7NumericalOwnedTheta :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  let Ecold := growingColdOnly_exponentialForwardEstimate tailError
    3 preE7NumericalOwnedT preE7NumericalOwnedA preE7NumericalOwnedTheta
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho]) (by omega)
    preE7NumericalOwnedT_nonneg preE7NumericalOwnedA_pos
    preE7NumericalOwned_tailGap
    (preE7NumericalOwned_tailMenu hLMM) htailPhysical
  let Eexceptional := (preE7NumericalOwned_exceptional hcoarse).toForwardEstimate
  simpa only [growingQuotientSecondaryError, tailError] using
    OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ecold Eexceptional

private def preE7Sns2OwnedT (w : ℕ)
    (j : PreE7Sns2OwnedIndex w) (b : ℕ) : ℝ :=
  preE7Sns2MenuCoefficient (preE7Sns2OwnedMenuIndex j) b

private def preE7Sns2OwnedX (w : ℕ)
    (j : PreE7Sns2OwnedIndex w) (b : ℕ) : ℝ :=
  preE7Sns2MenuExceptional (preE7Sns2OwnedMenuIndex j) b

private def preE7Sns2OwnedA (w : ℕ)
    (j : PreE7Sns2OwnedIndex w) : ℝ :=
  Nat.card (Subgroup.normalizer
    (preE7NonPairAction w j.2.1 : Set (Equiv.Perm (Fin w))))

private def preE7Sns2OwnedTheta (w : ℕ)
    (j : PreE7Sns2OwnedIndex w) : ℝ :=
  preE7Sns2MenuSlope (preE7Sns2OwnedMenuIndex j)

private theorem preE7Sns2Owned_coldWidthSum_eq_menu (b w : ℕ) :
    growingQuotientColdWidthSum b w (preE7Sns2OwnedT w)
        (preE7Sns2OwnedA w) (preE7Sns2OwnedTheta w) =
      growingQuotientColdWidthSum b w
        (fun i : PreE7Sns2MenuIndex w => preE7Sns2MenuCoefficient i)
        (fun i => preE7Sns2MenuNormalizer i)
        (fun i => preE7Sns2MenuSlope i) := by
  unfold growingQuotientColdWidthSum
  exact Fintype.sum_equiv (preE7Sns2OwnedMenuEquiv w)
    (fun i => fusionWidthColdKernel b w
      (preE7Sns2OwnedT w i b) (preE7Sns2OwnedA w i)
      (preE7Sns2OwnedTheta w i))
    (fun i => fusionWidthColdKernel b w
      (preE7Sns2MenuCoefficient i b) (preE7Sns2MenuNormalizer i)
      (preE7Sns2MenuSlope i)) (fun _ => rfl)

private theorem preE7Sns2Owned_exceptionalWidthSum_eq_menu (b w : ℕ) :
    (∑ i : PreE7Sns2OwnedIndex w, preE7Sns2OwnedX w i b) =
      ∑ i : PreE7Sns2MenuIndex w, preE7Sns2MenuExceptional i b := by
  exact Fintype.sum_equiv (preE7Sns2OwnedMenuEquiv w)
    (fun i => preE7Sns2OwnedX w i b)
    (fun i => preE7Sns2MenuExceptional i b) (fun _ => rfl)

private theorem preE7Sns2Owned_secondary_eq_menu_three (n : ℕ) :
    growingQuotientSecondaryError 3 preE7Sns2OwnedT preE7Sns2OwnedX
        preE7Sns2OwnedA preE7Sns2OwnedTheta n =
      growingQuotientSecondaryError 3
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuExceptional (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n := by
  unfold growingQuotientSecondaryError growingQuotientExceptionalTotal
    growingQuotientColdRow
  congr 1
  · apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    split_ifs
    · exact preE7Sns2Owned_coldWidthSum_eq_menu b w
    · rfl
  · apply Finset.sum_congr rfl
    intro w _
    exact preE7Sns2Owned_exceptionalWidthSum_eq_menu (n - w) w

private noncomputable def preE7Sns2Owned_secondary
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3 preE7Sns2OwnedT preE7Sns2OwnedX
        preE7Sns2OwnedA preE7Sns2OwnedTheta) := by
  let E₅ := preE7Sns2Secondary_exponentialForwardEstimate_of_inputs
    hcoarse hFS hOuter hLMM
  let E₃ := OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E₅ 0
    (fun n _ => le_of_eq (preE7Sns2_secondary_three_eq_five n))
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E₃ 0
    (fun n _ => le_of_eq (preE7Sns2Owned_secondary_eq_menu_three n))

private theorem preE7NumericalSns2_coldWidthSum_split (b w : ℕ) :
    growingQuotientColdWidthSum b w
        (preE7NumericalSns2T w) (preE7NumericalSns2A w)
        (preE7NumericalSns2Theta w) =
      growingQuotientColdWidthSum b w (preE7NumericalOwnedT w)
          (preE7NumericalOwnedA w) (preE7NumericalOwnedTheta w) +
        growingQuotientColdWidthSum b w (preE7Sns2OwnedT w)
          (preE7Sns2OwnedA w) (preE7Sns2OwnedTheta w) := by
  unfold growingQuotientColdWidthSum
  simp only [PreE7NumericalSns2Index, Fintype.sum_sum_type]
  simp [preE7NumericalSns2T, preE7NumericalSns2A,
    preE7NumericalSns2Theta, preE7NumericalSns2Action,
    preE7NumericalSns2ActionClass, preE7NumericalOwnedT,
    preE7NumericalOwnedA, preE7NumericalOwnedTheta, preE7Sns2OwnedT,
    preE7Sns2OwnedA, preE7Sns2OwnedTheta, fusionWidthColdKernel]

private theorem preE7NumericalSns2_exceptionalWidthSum_split (b w : ℕ) :
    (∑ j : PreE7NumericalSns2Index w,
        preE7NumericalSns2X w j b) =
      (∑ j : PreE7NumericalOwnedIndex w, preE7NumericalOwnedX w j b) +
        ∑ j : PreE7Sns2OwnedIndex w, preE7Sns2OwnedX w j b := by
  simp only [PreE7NumericalSns2Index, Fintype.sum_sum_type]
  simp [preE7NumericalSns2X, preE7NumericalOwnedX, preE7Sns2OwnedX]

private theorem preE7NumericalSns2_coldRow_split (n b : ℕ) :
    growingQuotientColdRow 3 preE7NumericalSns2T preE7NumericalSns2A
        preE7NumericalSns2Theta n b =
      growingQuotientColdRow 3 preE7NumericalOwnedT preE7NumericalOwnedA
          preE7NumericalOwnedTheta n b +
        growingQuotientColdRow 3 preE7Sns2OwnedT preE7Sns2OwnedA
          preE7Sns2OwnedTheta n b := by
  unfold growingQuotientColdRow
  calc
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
        (if b + w = n then
          growingQuotientColdWidthSum b w (preE7NumericalOwnedT w)
              (preE7NumericalOwnedA w) (preE7NumericalOwnedTheta w) +
            growingQuotientColdWidthSum b w (preE7Sns2OwnedT w)
              (preE7Sns2OwnedA w) (preE7Sns2OwnedTheta w)
         else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs
      · exact preE7NumericalSns2_coldWidthSum_split b w
      · rfl
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
          ((if b + w = n then
              growingQuotientColdWidthSum b w (preE7NumericalOwnedT w)
                (preE7NumericalOwnedA w) (preE7NumericalOwnedTheta w)
            else 0) +
           (if b + w = n then
              growingQuotientColdWidthSum b w (preE7Sns2OwnedT w)
                (preE7Sns2OwnedA w) (preE7Sns2OwnedTheta w)
            else 0)) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> ring
    _ = _ := by simp only [Finset.sum_add_distrib]

private theorem preE7NumericalSns2_exceptionalTotal_split (n : ℕ) :
    growingQuotientExceptionalTotal 3 preE7NumericalSns2X n =
      growingQuotientExceptionalTotal 3 preE7NumericalOwnedX n +
        growingQuotientExceptionalTotal 3 preE7Sns2OwnedX n := by
  unfold growingQuotientExceptionalTotal
  calc
    _ = ∑ w ∈ Finset.Ico 3 (n + 1),
        ((∑ j : PreE7NumericalOwnedIndex w,
            preE7NumericalOwnedX w j (n - w)) +
          ∑ j : PreE7Sns2OwnedIndex w,
            preE7Sns2OwnedX w j (n - w)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact preE7NumericalSns2_exceptionalWidthSum_split (n - w) w
    _ = _ := by simp only [Finset.sum_add_distrib]

private theorem preE7NumericalSns2_secondary_split (n : ℕ) :
    growingQuotientSecondaryError 3 preE7NumericalSns2T
        preE7NumericalSns2X preE7NumericalSns2A
        preE7NumericalSns2Theta n =
      growingQuotientSecondaryError 3 preE7NumericalOwnedT
          preE7NumericalOwnedX preE7NumericalOwnedA
          preE7NumericalOwnedTheta n +
        growingQuotientSecondaryError 3 preE7Sns2OwnedT
          preE7Sns2OwnedX preE7Sns2OwnedA preE7Sns2OwnedTheta n := by
  unfold growingQuotientSecondaryError
  rw [preE7NumericalSns2_exceptionalTotal_split]
  have hcold :
      (∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 preE7NumericalSns2T
              preE7NumericalSns2A preE7NumericalSns2Theta n b *
            ordinarySubgroupRatio b) =
        (∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 preE7NumericalOwnedT
              preE7NumericalOwnedA preE7NumericalOwnedTheta n b *
            ordinarySubgroupRatio b) +
        ∑ b ∈ Finset.range n,
          growingQuotientColdRow 3 preE7Sns2OwnedT
              preE7Sns2OwnedA preE7Sns2OwnedTheta n b *
            ordinarySubgroupRatio b := by
    calc
      _ = ∑ b ∈ Finset.range n,
          (growingQuotientColdRow 3 preE7NumericalOwnedT
                preE7NumericalOwnedA preE7NumericalOwnedTheta n b +
            growingQuotientColdRow 3 preE7Sns2OwnedT
                preE7Sns2OwnedA preE7Sns2OwnedTheta n b) *
              ordinarySubgroupRatio b := by
          apply Finset.sum_congr rfl
          intro b _
          rw [preE7NumericalSns2_coldRow_split]
      _ = _ := by
        simp only [add_mul, Finset.sum_add_distrib]
  rw [hcold]
  ring

/-- The complete secondary contribution of the disjoint catalogue is
exponentially contractive.  This is the point where the ordinary pointwise
owners and the globally correlated SNS2 rank-tail owner are combined. -/
noncomputable def preE7NumericalSns2_secondary
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3 preE7NumericalSns2T
        preE7NumericalSns2X preE7NumericalSns2A
        preE7NumericalSns2Theta) := by
  let Eordinary := preE7NumericalOwned_secondary hLMM hcoarse
  let Esns2 := preE7Sns2Owned_secondary hcoarse hFS hOuter hLMM
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    Eordinary Esns2
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => le_of_eq (preE7NumericalSns2_secondary_split n))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
