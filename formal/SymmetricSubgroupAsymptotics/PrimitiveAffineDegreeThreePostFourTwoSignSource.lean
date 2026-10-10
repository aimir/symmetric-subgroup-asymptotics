import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourTwoSignComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourOneSignSource

/-!
# Complete source for the post-four two-sign branch

The two-sign pair kernel contributes two central binary factors.  The
literal comparator is the actual block top with two disjoint regular
binary orbits, of degree `s+4`.  This file bounds the recursive comparison
coefficient and prepends the canonical ternary translation capacity at
the two low-sign cells where this branch occurs: twelve and eighteen
blocks.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev C2 := Multiplicative (ZMod 2)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- In the two-sign branch the literal signed quotient has order at most
four times the order of the full block symmetric group. -/
theorem degreeThreePostFourTwoSignSignedQuotient_card_le
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 2) :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤
      4 * (Nat.card block.Points).factorial := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  have htrans : MulAction.IsPretransitive (quotientAction block P).range
      (Fin (quotientDegree block)) :=
    degreeThreeSignedQuotientRange_pretransitive block P hr hcomponent
  have hkernel : Nat.card F.top.ker = 4 :=
    BinaryPairFrame.top_ker_card_eq_four_of_sign_count_two F htrans htwo
  have htop : Nat.card F.top.range ≤
      (Nat.card block.Points).factorial :=
    degreeThreePostFourOneSignTop_card_le_factorial block P hr
  have hcard := F.top.ker.card_mul_index
  rw [Subgroup.index_ker] at hcard
  calc
    Nat.card (preE7NonPairAction w U ⧸ E block P) =
        Nat.card (quotientAction block P).range :=
      Nat.card_congr (degreeThreeSignedQuotientRangeEquiv block P).toEquiv
    _ = Nat.card F.top.ker * Nat.card F.top.range := hcard.symm
    _ ≤ 4 * (Nat.card block.Points).factorial := by
      rw [hkernel]
      exact Nat.mul_le_mul_left 4 htop

/-- Exact all-normal comparison, transported to the literal faithful
`s+4` point comparator. -/
noncomputable def degreeThreePostFourTwoSignQuotientEnvelope
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 2) :
    RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P) := by
  let D := degreeThreePostFourTwoSignComparison
    block P hr hcomponent htwo
  let Q := DegreeThreePostFourTwoSignComparator block P hr
  let e := degreeThreePostFourTwoSignComparatorEquiv block P hr
  exact
    { R := Q
      groupR := inferInstance
      finiteR := inferInstance
      v := (Nat.card block.Points + 2) + 2
      action := Q.subtype
      action_injective := Subtype.val_injective
      coefficient := fun _ ↦ D.coefficient
      eta := 0
      coefficient_nonneg := fun _ ↦ Nat.cast_nonneg _
      bound := by
        intro b J
        have h := D.completeQuotientWeight_le J
        rw [Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr e J]
          at h
        simpa only [zero_mul, Real.rpow_zero, mul_one] using h }

private theorem two_rpow_oneHundredSeventy_width_le_menuMass
    {w : ℕ} (hw : 36 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (170 * (w : ℝ)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have harg : (32 : ℝ) ≤ ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 32 ≤ w + b + 2 by omega)
  have hmono : Real.log (32 : ℝ) ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at hmono
  have hlogtwo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : (10 : ℝ) / 3 ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) := by
    have hstrict : (10 : ℝ) / 3 < 5 * Real.log 2 := by
      nlinarith
    exact le_trans (le_of_lt hstrict) (by
      simpa only [Nat.cast_ofNat] using hmono)
  have hw0 : (0 : ℝ) ≤ w := by positivity
  nlinarith [sq_nonneg
    (Real.log ((w + b + 2 : ℕ) : ℝ) - 10 / 3)]

/-- The double-central coefficient and the canonical ternary coefficient
fit the common menu in the twelve- and eighteen-block two-sign cells. -/
theorem degreeThreePostFourTwoSign_coefficient_menu
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 12 ∨ Nat.card block.Points = 18)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 2)
    (b : ℕ) :
    let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hr
    let D := degreeThreePostFourTwoSignComparison
      block P hr hcomponent htwo
    H.coefficient * (D.coefficient : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  let pi := degreeThreePostFourOneSignProjectiveMap block P hr
  let S := degreeThreePostFourTwoSignProjectiveCentralSeries
    block P hr hcomponent htwo
  let X := (preE7NonPairAction w U ⧸ E block P) ⧸ S.C
  let A := DegreeThreePostFourTwoSignTop block P hr
  let D0 := DoubleCentralBinaryRecursiveComparison.firstCentralComparison
    A pi (degreeThreePostFourOneSignProjectiveMap_surjective block P hr)
      S (by rw [degreeThreePostFourTwoSignProjectiveKernel_card
        block P hr hcomponent htwo])
  let Dprod :=
    DoubleCentralBinaryRecursiveComparison.firstCentralProductComparison
      A pi (degreeThreePostFourOneSignProjectiveMap_surjective block P hr)
        S (by rw [degreeThreePostFourTwoSignProjectiveKernel_card
          block P hr hcomponent htwo])
  let D := degreeThreePostFourTwoSignComparison
    block P hr hcomponent htwo
  have hHcases := degreeThreePostFour_translationCoefficient_le_two_rpow
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr
      (hs.elim (fun h ↦ Or.inr (Or.inl h)) (fun h ↦ Or.inr (Or.inr h)))
  have hR := degreeThreePostFourTwoSignSignedQuotient_card_le
    block P hr hcomponent htwo
  have hA := degreeThreePostFourOneSignTop_card_le_factorial block P hr
  have hXle : Nat.card X ≤ Nat.card
      (preE7NonPairAction w U ⧸ E block P) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' S.C)
      (QuotientGroup.mk'_surjective S.C)
  rcases hHcases with ⟨hs6, _hH⟩ | ⟨hs12, hH⟩ | ⟨hs18, hH⟩
  · rcases hs with hs | hs <;> omega
  · have hw : w = 36 := by simpa only [hr, hs12] using width_eq block
    have hRpow : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤
        2 ^ 31 := by
      rw [hs12] at hR
      exact hR.trans (by norm_num)
    have hXpow : Nat.card X ≤ 2 ^ 31 := hXle.trans hRpow
    have hApow : Nat.card A ≤ 2 ^ 29 := by
      rw [hs12] at hA
      exact hA.trans (by norm_num)
    have hXprod : Nat.card (X × C2) ≤ 2 ^ 32 := by
      calc
        Nat.card (X × C2) = Nat.card X * 2 := by
          rw [Nat.card_prod]
          norm_num [C2, Nat.card_zmod]
        _ ≤ (2 ^ 31) * 2 := Nat.mul_le_mul_right 2 hXpow
        _ = 2 ^ 32 := by norm_num
    have hAprod : Nat.card (A × C2) ≤ 2 ^ 30 := by
      calc
        Nat.card (A × C2) = Nat.card A * 2 := by
          rw [Nat.card_prod]
          norm_num [C2, Nat.card_zmod]
        _ ≤ (2 ^ 29) * 2 := Nat.mul_le_mul_right 2 hApow
        _ = 2 ^ 30 := by norm_num
    have hD0 : D0.coefficient ≤ 2 ^ 991 := by
      apply D0.coefficient_le_two_pow_of_card_le_pow
        31 29 0 hXpow hApow
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hDprod : Dprod.coefficient ≤ 2 ^ 1055 := by
      apply Dprod.coefficient_le_two_pow_of_card_le_pow
        32 30 0 hXprod hAprod
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hDnat : D.coefficient ≤ 2 ^ 2048 := by
      apply D.coefficient_le_two_pow_of_card_le_pow
        31 31 1055 hRpow hXpow
      · change D0.coefficient ≤ 2 ^ 1055
        exact hD0.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      · change Dprod.coefficient ≤ 2 ^ 1055
        exact hDprod
    have hDreal : (D.coefficient : ℝ) ≤ (2 : ℝ) ^ (2048 : ℝ) := by
      calc
        (D.coefficient : ℝ) ≤ ((2 ^ 2048 : ℕ) : ℝ) := by
          exact_mod_cast hDnat
        _ = (2 : ℝ) ^ (2048 : ℝ) := by
          calc
            ((2 ^ 2048 : ℕ) : ℝ) = (2 : ℝ) ^ (2048 : ℕ) :=
              Nat.cast_pow 2 2048
            _ = (2 : ℝ) ^ (2048 : ℝ) :=
              (Real.rpow_natCast 2 2048).symm
    calc
      H.coefficient * (D.coefficient : ℝ) ≤
          (2 : ℝ) ^ (2560 : ℝ) * (2 : ℝ) ^ (2048 : ℝ) :=
        mul_le_mul hH hDreal (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (4608 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (170 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_oneHundredSeventy_width_le_menuMass
        (hw.symm ▸ (by norm_num : 36 ≤ 36)) b
  · have hw : w = 54 := by simpa only [hr, hs18] using width_eq block
    have hRpow : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤
        2 ^ 55 := by
      rw [hs18] at hR
      exact hR.trans (by norm_num)
    have hXpow : Nat.card X ≤ 2 ^ 55 := hXle.trans hRpow
    have hApow : Nat.card A ≤ 2 ^ 53 := by
      rw [hs18] at hA
      exact hA.trans (by norm_num)
    have hXprod : Nat.card (X × C2) ≤ 2 ^ 56 := by
      calc
        Nat.card (X × C2) = Nat.card X * 2 := by
          rw [Nat.card_prod]
          norm_num [C2, Nat.card_zmod]
        _ ≤ (2 ^ 55) * 2 := Nat.mul_le_mul_right 2 hXpow
        _ = 2 ^ 56 := by norm_num
    have hAprod : Nat.card (A × C2) ≤ 2 ^ 54 := by
      calc
        Nat.card (A × C2) = Nat.card A * 2 := by
          rw [Nat.card_prod]
          norm_num [C2, Nat.card_zmod]
        _ ≤ (2 ^ 53) * 2 := Nat.mul_le_mul_right 2 hApow
        _ = 2 ^ 54 := by norm_num
    have hD0 : D0.coefficient ≤ 2 ^ 3079 := by
      apply D0.coefficient_le_two_pow_of_card_le_pow
        55 53 0 hXpow hApow
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hDprod : Dprod.coefficient ≤ 2 ^ 3191 := by
      apply Dprod.coefficient_le_two_pow_of_card_le_pow
        56 54 0 hXprod hAprod
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hDnat : D.coefficient ≤ 2 ^ 6272 := by
      apply D.coefficient_le_two_pow_of_card_le_pow
        55 55 3191 hRpow hXpow
      · change D0.coefficient ≤ 2 ^ 3191
        exact hD0.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      · change Dprod.coefficient ≤ 2 ^ 3191
        exact hDprod
    have hDreal : (D.coefficient : ℝ) ≤ (2 : ℝ) ^ (6272 : ℝ) := by
      calc
        (D.coefficient : ℝ) ≤ ((2 ^ 6272 : ℕ) : ℝ) := by
          exact_mod_cast hDnat
        _ = (2 : ℝ) ^ (6272 : ℝ) := by
          calc
            ((2 ^ 6272 : ℕ) : ℝ) = (2 : ℝ) ^ (6272 : ℕ) :=
              Nat.cast_pow 2 6272
            _ = (2 : ℝ) ^ (6272 : ℝ) :=
              (Real.rpow_natCast 2 6272).symm
    calc
      H.coefficient * (D.coefficient : ℝ) ≤
          (2 : ℝ) ^ (2880 : ℝ) * (2 : ℝ) ^ (6272 : ℝ) :=
        mul_le_mul hH hDreal (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (9152 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (170 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_oneHundredSeventy_width_le_menuMass
        (hw.symm ▸ (by norm_num : 36 ≤ 54)) b

/-- Numerical margin for the `s+4` comparator and canonical ternary width
at twelve and eighteen blocks. -/
theorem degreeThreePostFourTwoSign_margin
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
          (((Nat.card block.Points + 2) + 2 : ℕ) : ℝ)) / 8 -
        Real.logb 2 3 / 3 *
          ternaryWidthCore (Nat.card block.Points)
            ((Nat.card block.Points).factorization 3) := by
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hlog : Real.logb 2 3 ≤ 8 / 5 := by
    have hp : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
      simpa only [mul_comm] using le_of_lt h)
  have hf12 : (12 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf18 : (18 : ℕ).factorization 3 = 2 := by decide +kernel
  rcases hs with hs | hs
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf12,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf18,
      preE7CharacterRho] at hlog ⊢
    linarith

/-- Complete post-four source when the literal pair kernel has exactly two
realized coordinate signs. -/
noncomputable def degreeThreePostFourTwoSignSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 12 ∨ Nat.card block.Points = 18)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 2) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  let D := degreeThreePostFourTwoSignComparison
    block P hr hcomponent htwo
  let Q := degreeThreePostFourTwoSignQuotientEnvelope
    block P hr hcomponent htwo
  let T := translationLayerEnvelopeOver block P H Q
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart, localTranslationChart] using hpd.1
  have hcap : H.capacity = ternaryWidthCore (Nat.card block.Points)
      ((Nat.card block.Points).factorization 3) :=
    degreeThreeTernaryWidthJointCapacity_capacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hr
  let S : PreE7S3ExceptionalSource w U :=
    { sourceDegree := (Nat.card block.Points + 2) + 2
      sourceDegree_two := by omega
      Q := DegreeThreePostFourTwoSignComparator block P hr
      B := H.coefficient * (D.coefficient : ℝ)
      C := 0
      eta := Real.logb 2 3 / 3 * H.capacity
      theta := 0
      B_nonneg := mul_nonneg H.coefficient_nonneg (Nat.cast_nonneg _)
      C_nonneg := le_rfl
      eta_nonneg := mul_nonneg
        (div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
          (by norm_num)) H.capacity_nonneg
      exponent_margin := by
        have hm := degreeThreePostFourTwoSign_margin block hr hs
        simpa only [hcap] using hm
      tail_window := by
        rcases hs with hs | hs
        · have hw36 : w = 36 := by simpa only [hr, hs] using width_eq block
          rw [hw36]
          norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
        · have hw54 : w = 54 := by simpa only [hr, hs] using width_eq block
          rw [hw54]
          norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      complete_bound := by
        intro b J
        have h := T.bound b J
        simpa only [T, Q, translationLayerEnvelopeOver_v,
          translationLayerEnvelopeOver_eta,
          translationLayerEnvelopeOver_coefficient,
          degreeThreePostFourTwoSignQuotientEnvelope, hp, zero_add,
          zero_mul, Real.rpow_zero, mul_one, add_zero] using h
      main_menu := by
        intro b
        exact degreeThreePostFourTwoSign_coefficient_menu block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hs hcomponent htwo b
      tail_menu := by intro b; positivity }
  exact .inl S.toRankTailOwnerSource

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
