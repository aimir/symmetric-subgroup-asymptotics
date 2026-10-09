import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourOneSignComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeTopKernelZeroSource
import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalSmallRankTailBridge

/-!
# Complete source for the post-four one-sign branch

The one-sign signed quotient is a central binary extension of its actual
block top.  Its `top × C₂` comparator uses only `s+2` points.  Prepending
the canonical ternary-width capacity then leaves a strict margin at each
of the surviving block counts six, twelve, and eighteen.

The finite coefficient estimates below use only the literal kernel/top
orders and the published Tracey coefficient.  They are intentionally
uniform and avoid a normal-subgroup or action census.
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

private theorem ceil_div_sqrt_logb_le_self
    (n s : ℕ) (hs : 2 ≤ s) :
    ⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ ≤ n := by
  have hlog : (1 : ℝ) ≤ Real.logb 2 s := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hs : (2 : ℝ) ≤ s)
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (Real.logb 2 s) :=
    Real.one_le_sqrt.mpr hlog
  have hsqrt0 : 0 < Real.sqrt (Real.logb 2 s) :=
    lt_of_lt_of_le (by norm_num) hsqrt
  have hdiv : (n : ℝ) / Real.sqrt (Real.logb 2 s) ≤ n := by
    apply (div_le_iff₀ hsqrt0).2
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hnonneg : 0 ≤ (n : ℝ) / Real.sqrt (Real.logb 2 s) := by
    positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hlt :
      (⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ : ℝ) < n + 1 := by
    nlinarith
  have hltNat :
      ⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ < n + 1 := by
    exact_mod_cast hlt
  omega

private theorem ceil_div_sqrt_logb_le_half
    (n s k : ℕ) (hs : 16 ≤ s) (hn : n ≤ 2 * k) :
    ⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ ≤ k := by
  have hlog16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hlog : (4 : ℝ) ≤ Real.logb 2 s := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 16)
      (by exact_mod_cast hs : (16 : ℝ) ≤ s)
    simpa only [hlog16] using h
  have hlog0 : 0 ≤ Real.logb 2 s := le_trans (by norm_num) hlog
  have hsqrt0 : 0 ≤ Real.sqrt (Real.logb 2 s) := Real.sqrt_nonneg _
  have hsqrtSq := Real.sq_sqrt hlog0
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (Real.logb 2 s) := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (Real.logb 2 s) :=
    lt_of_lt_of_le (by norm_num) hsqrt
  have hnReal : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn
  have hdiv : (n : ℝ) / Real.sqrt (Real.logb 2 s) ≤ k := by
    apply (div_le_iff₀ hsqrtPos).2
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hnonneg : 0 ≤ (n : ℝ) / Real.sqrt (Real.logb 2 s) := by
    positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hlt :
      (⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ : ℝ) < k + 1 := by
    nlinarith
  have hltNat :
      ⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ < k + 1 := by
    exact_mod_cast hlt
  omega

private theorem postFour_inducedCeiling_six_le :
    traceyInducedGeneratorCeiling 1 6 ≤ 24 := by
  convert ceil_div_sqrt_logb_le_self 24 6 (by norm_num) using 1 <;>
    norm_num [traceyInducedGeneratorCeiling]

private theorem postFour_permutationCeiling_eighteen_le :
    traceyPermutationGeneratorCeiling 18 ≤ 18 := by
  simpa [traceyPermutationGeneratorCeiling] using
    (ceil_div_sqrt_logb_le_self 18 18 (by norm_num))

private theorem postFour_traceyExponent_six_le :
    traceyAffineCoefficientExponent 1 6
      (traceyInducedGeneratorCeiling 1 6)
      (traceyPermutationGeneratorCeiling 18) 18 3 ≤ 405 := by
  have hi := postFour_inducedCeiling_six_le
  have hg := postFour_permutationCeiling_eighteen_le
  unfold traceyAffineCoefficientExponent
  omega

private theorem postFour_inducedCeiling_twelve_le :
    traceyInducedGeneratorCeiling 1 12 ≤ 48 := by
  convert ceil_div_sqrt_logb_le_self 48 12 (by norm_num) using 1 <;>
    norm_num [traceyInducedGeneratorCeiling]

private theorem postFour_permutationCeiling_thirtySix_le :
    traceyPermutationGeneratorCeiling 36 ≤ 36 := by
  simpa [traceyPermutationGeneratorCeiling] using
    (ceil_div_sqrt_logb_le_self 36 36 (by norm_num))

private theorem postFour_traceyExponent_twelve_le :
    traceyAffineCoefficientExponent 1 12
      (traceyInducedGeneratorCeiling 1 12)
      (traceyPermutationGeneratorCeiling 36) 36 3 ≤ 1600 := by
  have hi := postFour_inducedCeiling_twelve_le
  have hg := postFour_permutationCeiling_thirtySix_le
  unfold traceyAffineCoefficientExponent
  omega

private theorem postFour_inducedCeiling_eighteen_le :
    traceyInducedGeneratorCeiling 1 18 ≤ 36 := by
  convert ceil_div_sqrt_logb_le_half 72 18 36 (by norm_num) (by norm_num)
    using 1 <;> norm_num [traceyInducedGeneratorCeiling]

private theorem postFour_permutationCeiling_fiftyFour_le :
    traceyPermutationGeneratorCeiling 54 ≤ 27 := by
  simpa [traceyPermutationGeneratorCeiling] using
    (ceil_div_sqrt_logb_le_half 54 54 27 (by norm_num) (by norm_num))

private theorem postFour_traceyExponent_eighteen_le :
    traceyAffineCoefficientExponent 1 18
      (traceyInducedGeneratorCeiling 1 18)
      (traceyPermutationGeneratorCeiling 54) 54 3 ≤ 1800 := by
  have hi := postFour_inducedCeiling_eighteen_le
  have hg := postFour_permutationCeiling_fiftyFour_le
  unfold traceyAffineCoefficientExponent
  omega

private theorem three_pow_le_two_pow_of_exponent_le_five_mul
    (A k : ℕ) (hA : A ≤ 5 * k) :
    (3 : ℝ) ^ A ≤ (2 : ℝ) ^ (8 * k) := by
  calc
    (3 : ℝ) ^ A ≤ (3 : ℝ) ^ (5 * k) :=
      pow_le_pow_right₀ (by norm_num) hA
    _ = ((3 : ℝ) ^ 5) ^ k := by rw [pow_mul]
    _ ≤ ((2 : ℝ) ^ 8) ^ k :=
      pow_le_pow_left₀ (by positivity) (by norm_num) k
    _ = (2 : ℝ) ^ (8 * k) := by rw [pow_mul]

/-- The published ternary incidence coefficient has an absolute bound in
each of the three post-four cells. -/
theorem degreeThreePostFour_translationCoefficient_le_two_rpow
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) :
    let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hr
    (Nat.card block.Points = 6 ∧ H.coefficient ≤ (2 : ℝ) ^ (648 : ℝ)) ∨
    (Nat.card block.Points = 12 ∧ H.coefficient ≤ (2 : ℝ) ^ (2560 : ℝ)) ∨
    (Nat.card block.Points = 18 ∧ H.coefficient ≤ (2 : ℝ) ^ (2880 : ℝ)) := by
  let H₀ := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hraw := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hcoeffEq : H.coefficient = H₀.coefficient := by
    exact degreeThreeTernaryWidthJointCapacity_coefficient block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr
  rcases hs with hs | hs | hs
  · have hw : w = 18 := by simpa only [hr, hs] using width_eq block
    have hcoeff : H.coefficient ≤ (3 : ℝ) ^
        traceyAffineCoefficientExponent 1 6
          (traceyInducedGeneratorCeiling 1 6)
          (traceyPermutationGeneratorCeiling 18) 18 3 := by
      rw [hcoeffEq]
      simpa only [H₀, hpd.1, hpd.2, hp, hs, hw,
        Fintype.card_eq_nat_card] using hraw
    refine Or.inl ⟨hs, ?_⟩
    calc
      H.coefficient ≤ (3 : ℝ) ^
          traceyAffineCoefficientExponent 1 6
            (traceyInducedGeneratorCeiling 1 6)
            (traceyPermutationGeneratorCeiling 18) 18 3 := hcoeff
      _ ≤ (2 : ℝ) ^ (8 * 81 : ℕ) :=
        three_pow_le_two_pow_of_exponent_le_five_mul _ 81
          postFour_traceyExponent_six_le
      _ = (2 : ℝ) ^ (648 : ℝ) := by
        norm_num [Real.rpow_natCast]
  · have hw : w = 36 := by simpa only [hr, hs] using width_eq block
    have hcoeff : H.coefficient ≤ (3 : ℝ) ^
        traceyAffineCoefficientExponent 1 12
          (traceyInducedGeneratorCeiling 1 12)
          (traceyPermutationGeneratorCeiling 36) 36 3 := by
      rw [hcoeffEq]
      simpa only [H₀, hpd.1, hpd.2, hp, hs, hw,
        Fintype.card_eq_nat_card] using hraw
    refine Or.inr (Or.inl ⟨hs, ?_⟩)
    calc
      H.coefficient ≤ (3 : ℝ) ^
          traceyAffineCoefficientExponent 1 12
            (traceyInducedGeneratorCeiling 1 12)
            (traceyPermutationGeneratorCeiling 36) 36 3 := hcoeff
      _ ≤ (2 : ℝ) ^ (8 * 320 : ℕ) :=
        three_pow_le_two_pow_of_exponent_le_five_mul _ 320
          postFour_traceyExponent_twelve_le
      _ = (2 : ℝ) ^ (2560 : ℝ) := by
        norm_num [Real.rpow_natCast]
  · have hw : w = 54 := by simpa only [hr, hs] using width_eq block
    have hcoeff : H.coefficient ≤ (3 : ℝ) ^
        traceyAffineCoefficientExponent 1 18
          (traceyInducedGeneratorCeiling 1 18)
          (traceyPermutationGeneratorCeiling 54) 54 3 := by
      rw [hcoeffEq]
      simpa only [H₀, hpd.1, hpd.2, hp, hs, hw,
        Fintype.card_eq_nat_card] using hraw
    refine Or.inr (Or.inr ⟨hs, ?_⟩)
    calc
      H.coefficient ≤ (3 : ℝ) ^
          traceyAffineCoefficientExponent 1 18
            (traceyInducedGeneratorCeiling 1 18)
            (traceyPermutationGeneratorCeiling 54) 54 3 := hcoeff
      _ ≤ (2 : ℝ) ^ (8 * 360 : ℕ) :=
        three_pow_le_two_pow_of_exponent_le_five_mul _ 360
          postFour_traceyExponent_eighteen_le
      _ = (2 : ℝ) ^ (2880 : ℝ) := by
        norm_num [Real.rpow_natCast]

/-- The literal block top has order at most the factorial of the block
count. -/
theorem degreeThreePostFourOneSignTop_card_le_factorial
    (hr : Nat.card block.Fibre = 3) :
    Nat.card (DegreeThreePostFourOneSignTop block P hr) ≤
      (Nat.card block.Points).factorial := by
  calc
    Nat.card (DegreeThreePostFourOneSignTop block P hr) ≤
        Nat.card (Equiv.Perm block.Points) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = (Nat.card block.Points).factorial := by rw [Nat.card_perm]

/-- In the one-sign branch the signed quotient has order at most twice the
order of the full block symmetric group. -/
theorem degreeThreePostFourOneSignSignedQuotient_card_le
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 1) :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤
      2 * (Nat.card block.Points).factorial := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  have hkernel : Nat.card F.top.ker ≤ 2 :=
    BinaryPairFrame.top_ker_card_le_two_of_sign_count_one F hone
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
    _ ≤ 2 * (Nat.card block.Points).factorial :=
      Nat.mul_le_mul hkernel htop

/-- The exact all-normal comparison, transported to the literal faithful
`s+2` point comparator. -/
noncomputable def degreeThreePostFourOneSignQuotientEnvelope
    (hr : Nat.card block.Fibre = 3)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 1) :
    RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P) := by
  let D := degreeThreePostFourOneSignComparison block P hr hone
  let Q := DegreeThreePostFourOneSignComparator block P hr
  let e := degreeThreePostFourOneSignComparatorEquiv block P hr
  exact
    { R := Q
      groupR := inferInstance
      finiteR := inferInstance
      v := Nat.card block.Points + 2
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

private theorem two_rpow_oneHundredTwelve_width_le_menuMass
    {w : ℕ} (hw : 18 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (112 * (w : ℝ)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have harg : (16 : ℝ) ≤ ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 16 ≤ w + b + 2 by omega)
  have hmono : Real.log (16 : ℝ) ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hmono
  have hlogtwo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : (8 : ℝ) / 3 ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) := by
    norm_num at hmono
    linarith
  have hw0 : (0 : ℝ) ≤ w := by positivity
  nlinarith [sq_nonneg
    (Real.log ((w + b + 2 : ℕ) : ℝ) - 8 / 3)]

/-- The one-sign central-product coefficient and the canonical ternary
coefficient fit the common menu in all three post-four cells. -/
theorem degreeThreePostFourOneSign_coefficient_menu
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 1)
    (b : ℕ) :
    let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hr
    let D := degreeThreePostFourOneSignComparison block P hr hone
    H.coefficient * (D.coefficient : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  let D := degreeThreePostFourOneSignComparison block P hr hone
  have hHcases := degreeThreePostFour_translationCoefficient_le_two_rpow
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hR := degreeThreePostFourOneSignSignedQuotient_card_le
    block P hr hone
  have hA := degreeThreePostFourOneSignTop_card_le_factorial block P hr
  rcases hHcases with ⟨hs, hH⟩ | ⟨hs, hH⟩ | ⟨hs, hH⟩
  · have hw : w = 18 := by simpa only [hr, hs] using width_eq block
    have hRpow : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2 ^ 11 := by
      rw [hs] at hR
      exact hR.trans (by norm_num)
    have hApow : Nat.card (DegreeThreePostFourOneSignTop block P hr) ≤
        2 ^ 10 := by
      rw [hs] at hA
      exact hA.trans (by norm_num)
    have hDnat : D.coefficient ≤ 2 ^ 132 := by
      apply D.coefficient_le_two_pow_of_card_le_pow 11 10 0 hRpow hApow
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hD : (D.coefficient : ℝ) ≤ (2 : ℝ) ^ (132 : ℝ) := by
      calc
        (D.coefficient : ℝ) ≤ ((2 ^ 132 : ℕ) : ℝ) := by
          exact_mod_cast hDnat
        _ = (2 : ℝ) ^ (132 : ℝ) := by norm_num [Real.rpow_natCast]
    calc
      H.coefficient * (D.coefficient : ℝ) ≤
          (2 : ℝ) ^ (648 : ℝ) * (2 : ℝ) ^ (132 : ℝ) :=
        mul_le_mul hH hD (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (780 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (112 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_oneHundredTwelve_width_le_menuMass
        (hw.symm ▸ (by norm_num : 18 ≤ 18)) b
  · have hw : w = 36 := by simpa only [hr, hs] using width_eq block
    have hRpow : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2 ^ 30 := by
      rw [hs] at hR
      exact hR.trans (by norm_num)
    have hApow : Nat.card (DegreeThreePostFourOneSignTop block P hr) ≤
        2 ^ 29 := by
      rw [hs] at hA
      exact hA.trans (by norm_num)
    have hDnat : D.coefficient ≤ 2 ^ 930 := by
      apply D.coefficient_le_two_pow_of_card_le_pow 30 29 0 hRpow hApow
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hD : (D.coefficient : ℝ) ≤ (2 : ℝ) ^ (930 : ℝ) := by
      calc
        (D.coefficient : ℝ) ≤ ((2 ^ 930 : ℕ) : ℝ) := by
          exact_mod_cast hDnat
        _ = (2 : ℝ) ^ (930 : ℝ) := by norm_num [Real.rpow_natCast]
    calc
      H.coefficient * (D.coefficient : ℝ) ≤
          (2 : ℝ) ^ (2560 : ℝ) * (2 : ℝ) ^ (930 : ℝ) :=
        mul_le_mul hH hD (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (3490 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (112 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_oneHundredTwelve_width_le_menuMass
        (hw.symm ▸ (by norm_num : 18 ≤ 36)) b
  · have hw : w = 54 := by simpa only [hr, hs] using width_eq block
    have hRpow : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2 ^ 54 := by
      rw [hs] at hR
      exact hR.trans (by norm_num)
    have hApow : Nat.card (DegreeThreePostFourOneSignTop block P hr) ≤
        2 ^ 53 := by
      rw [hs] at hA
      exact hA.trans (by norm_num)
    have hDnat : D.coefficient ≤ 2 ^ 2970 := by
      apply D.coefficient_le_two_pow_of_card_le_pow 54 53 0 hRpow hApow
      · change 1 ≤ 2 ^ 0
        norm_num
      · change 1 ≤ 2 ^ 0
        norm_num
    have hD : (D.coefficient : ℝ) ≤ (2 : ℝ) ^ (2970 : ℝ) := by
      calc
        (D.coefficient : ℝ) ≤ ((2 ^ 2970 : ℕ) : ℝ) := by
          exact_mod_cast hDnat
        _ = (2 : ℝ) ^ (2970 : ℝ) := by norm_num [Real.rpow_natCast]
    calc
      H.coefficient * (D.coefficient : ℝ) ≤
          (2 : ℝ) ^ (2880 : ℝ) * (2 : ℝ) ^ (2970 : ℝ) :=
        mul_le_mul hH hD (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (5850 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (112 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hw]
        norm_num
      _ ≤ _ := two_rpow_oneHundredTwelve_width_le_menuMass
        (hw.symm ▸ (by norm_num : 18 ≤ 54)) b

/-- Numerical margin for the `s+2` point comparator and canonical ternary
width at six, twelve, and eighteen blocks. -/
theorem degreeThreePostFourOneSign_margin
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (Nat.card block.Points + 2)) / 8 -
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
  have hf6 : (6 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf12 : (12 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf18 : (18 : ℕ).factorization 3 = 2 := by decide +kernel
  rcases hs with hs | hs | hs
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf6,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf12,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf18,
      preE7CharacterRho] at hlog ⊢
    linarith

/-- Complete post-four source when the literal pair kernel has one realized
coordinate sign. -/
noncomputable def degreeThreePostFourOneSignSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18)
    (hone : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 1) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  let D := degreeThreePostFourOneSignComparison block P hr hone
  let Q := degreeThreePostFourOneSignQuotientEnvelope block P hr hone
  let T := translationLayerEnvelopeOver block P H Q
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart, localTranslationChart] using hpd.1
  have hcap : H.capacity = ternaryWidthCore (Nat.card block.Points)
      ((Nat.card block.Points).factorization 3) :=
    degreeThreeTernaryWidthJointCapacity_capacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hr
  let S : PreE7S3ExceptionalSource w U :=
    { sourceDegree := Nat.card block.Points + 2
      sourceDegree_two := by omega
      Q := DegreeThreePostFourOneSignComparator block P hr
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
        have hm := degreeThreePostFourOneSign_margin block hr hs
        simpa only [hcap] using hm
      tail_window := by
        rcases hs with hs | hs | hs
        · have hw18 : w = 18 := by simpa only [hr, hs] using width_eq block
          rw [hw18]
          norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
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
          degreeThreePostFourOneSignQuotientEnvelope, hp, zero_add,
          zero_mul, Real.rpow_zero, mul_one, add_zero] using h
      main_menu := by
        intro b
        exact degreeThreePostFourOneSign_coefficient_menu block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hs hone b
      tail_menu := by intro b; positivity }
  exact .inl S.toRankTailOwnerSource

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
