import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPairPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePairNumericalLift
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalOwnedPolynomialEnvelope

/-!
# Close the nonbinary four-block signed quotient

The actual ternary translation layer has capacity at most one at four
blocks.  The published nonbinary four-pair correspondence retains a
comparator of degree at most six, an additive slope at most `7/9`, and
uniform finite coefficients.  This file checks those two rows together at
the ambient width twelve and installs the resulting correlated source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private theorem ceil_div_sqrt_logb_le
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
  have hnonneg : 0 ≤ (n : ℝ) / Real.sqrt (Real.logb 2 s) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hlt : (⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ : ℝ) < n + 1 := by
    nlinarith
  have hltNat : ⌈(n : ℝ) / Real.sqrt (Real.logb 2 s)⌉₊ < n + 1 := by
    exact_mod_cast hlt
  omega

private theorem degreeThreeFourBlock_inducedCeiling_le_sixteen :
    traceyInducedGeneratorCeiling 1 4 ≤ 16 := by
  convert ceil_div_sqrt_logb_le 16 4 (by norm_num) using 1;
    norm_num [traceyInducedGeneratorCeiling]

private theorem degreeThreeFourBlock_permutationCeiling_le_twelve :
    traceyPermutationGeneratorCeiling 12 ≤ 12 := by
  simpa [traceyPermutationGeneratorCeiling] using
    (ceil_div_sqrt_logb_le 12 12 (by norm_num))

private theorem degreeThreeFourBlock_traceyExponent_le :
    traceyAffineCoefficientExponent 1 4
      (traceyInducedGeneratorCeiling 1 4)
      (traceyPermutationGeneratorCeiling 12) 12 3 ≤ 180 := by
  have hi := degreeThreeFourBlock_inducedCeiling_le_sixteen
  have hg := degreeThreeFourBlock_permutationCeiling_le_twelve
  unfold traceyAffineCoefficientExponent
  omega

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The literal ternary incidence coefficient is an absolute constant in
the four-block slice. -/
theorem degreeThreeFourBlock_translationCoefficient_le_two_rpow
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).coefficient ≤
        (2 : ℝ) ^ (384 : ℝ) := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  have hw : w = 12 := by
    simpa only [hr, hs] using width_eq block
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hraw := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hcoeff : H.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 4
        (traceyInducedGeneratorCeiling 1 4)
        (traceyPermutationGeneratorCeiling 12) 12 3 := by
    simpa only [H, hpd.1, hpd.2, hp, hs, hw,
      Fintype.card_eq_nat_card] using hraw
  let A : ℕ := traceyAffineCoefficientExponent 1 4
    (traceyInducedGeneratorCeiling 1 4)
    (traceyPermutationGeneratorCeiling 12) 12 3
  have hA : A ≤ 180 := by
    simpa only [A] using degreeThreeFourBlock_traceyExponent_le
  calc
    H.coefficient ≤ (3 : ℝ) ^ A := by simpa only [A] using hcoeff
    _ ≤ (4 : ℝ) ^ A := pow_le_pow_left₀ (by norm_num) (by norm_num) A
    _ ≤ (4 : ℝ) ^ (180 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) hA
    _ = (2 : ℝ) ^ (360 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    _ ≤ (2 : ℝ) ^ (384 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = (2 : ℝ) ^ (384 : ℝ) :=
      (Real.rpow_natCast (2 : ℝ) 384).symm

private theorem fourBlock_pairCoefficient_total_growth (b : ℕ) :
    (2 : ℝ) ^ (704 : ℝ) * (1 + b) ≤
      (2 : ℝ) ^
        (16 * (12 : ℝ) * Real.log (((b + 12 + 2 : ℕ) : ℝ)) ^ 2) := by
  have hmem : 12 ∈ Finset.Ico 3 (b + 12 + 1) := by
    simp only [Finset.mem_Ico]
    omega
  have hshift := shiftedNatPow_le_widthLogSquared 1 (b + 12) 12 hmem
  have hbsub : b + 12 - 12 = b := by omega
  have hpoly : (1 : ℝ) + b ≤
      (2 : ℝ) ^ (12 * Real.log (((b + 12 + 2 : ℕ) : ℝ)) ^ 2) := by
    simpa only [hbsub, pow_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      one_mul] using hshift
  let L : ℝ := Real.log (((b + 12 + 2 : ℕ) : ℝ))
  have hexpTwo : Real.exp (2 : ℝ) < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  have harg : (9 : ℝ) < ((b + 12 + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 9 < b + 12 + 2 by omega)
  have hlog : (2 : ℝ) ≤ L := by
    dsimp [L]
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2
      (hexpTwo.trans harg)).le
  have hexponent : (704 : ℝ) + 12 * L ^ 2 ≤ 16 * 12 * L ^ 2 := by
    nlinarith [sq_nonneg (L - 2)]
  calc
    (2 : ℝ) ^ (704 : ℝ) * (1 + b) ≤
        (2 : ℝ) ^ (704 : ℝ) * (2 : ℝ) ^ (12 * L ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [L] using hpoly) (by positivity)
    _ = (2 : ℝ) ^ ((704 : ℝ) + 12 * L ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (16 * 12 * L ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = (2 : ℝ) ^
        (16 * (12 : ℝ) * Real.log (((b + 12 + 2 : ℕ) : ℝ)) ^ 2) := by
      rfl

private theorem logb_two_three_le_eight_fifths :
    Real.logb 2 3 ≤ (8 : ℝ) / 5 := by
  have hp : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
    simpa only [mul_comm] using le_of_lt h)

/-- The common additive numerical record for every nonbinary four-pair
row after the actual ternary layer is prepended. -/
noncomputable def degreeThreeFourBlockNonbinaryAdditiveNumerics
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hnonbinary : ¬ IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm
    let G := degreeThreeFourBlockNonbinaryGrowthPackage block P hZmud lit
      published hr hs hcomponent hnonbinary
    DegreeThreeSignedQuotientAdditiveNumerics block P H G := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let G := degreeThreeFourBlockNonbinaryGrowthPackage block P hZmud lit
    published hr hs hcomponent hnonbinary
  let N := degreeThreeFourBlockNonbinaryGrowthNumerics block P hgen hZmud lit
    published hr hs hcomponent hnonbinary
  let tau : ℝ := Real.logb 2 (elementaryChart block P).p /
    (elementaryChart block P).p * H.capacity
  let eta : ℝ := 0
  let theta : ℝ := 7 / 9
  let delta : ℝ := paddedComparatorDelta preE7CharacterRho tau G.package.v w
  let cutoff : ℝ :=
    (paddedComparatorDegree preE7CharacterRho G.package.v w : ℝ) / 8 +
      delta / 2
  let alpha : ℝ := tau + cutoff
  have hpd := degreeThree_translation_prime_dim block P hr
  have hep : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart, localTranslationChart] using hpd.1
  have hcap := degreeThree_translation_capacity_fourBlocks block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hrate0 : 0 ≤ Real.logb 2 3 / 3 := by
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have htau0 : 0 ≤ tau := by
    dsimp [tau]
    exact mul_nonneg
      (div_nonneg (Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (elementaryChart block P).p_prime.one_le))
        (by positivity)) H.capacity_nonneg
  have htau : tau ≤ (8 : ℝ) / 15 := by
    have hcost : Real.logb 2 3 / 3 * H.capacity ≤
        Real.logb 2 3 / 3 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcap hrate0
    have hepR : ((elementaryChart block P).p : ℝ) = 3 := by
      exact_mod_cast hep
    dsimp [tau]
    rw [hepR]
    exact hcost.trans (by
      have h := logb_two_three_le_eight_fifths
      linarith)
  have hw12 : w = 12 := by
    simpa only [hr, hs] using width_eq block
  have hwR : (w : ℝ) = 12 := by exact_mod_cast hw12
  have heven : evenWidth w = 12 := by
    rw [hw12]
    norm_num [evenWidth, halfDegree]
  have hpad : paddedComparatorDegree preE7CharacterRho G.package.v w =
      G.package.v := by
    unfold paddedComparatorDegree
    apply max_eq_left
    rw [heven]
    norm_num [preE7CharacterRho]
  have hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - G.package.v) / 8 - tau := by
    have hv : (G.package.v : ℝ) ≤ 6 := by
      exact_mod_cast N.degree_le_six
    rw [hwR, heven]
    norm_num [preE7CharacterRho]
    linarith
  have htail : tau + theta ≤ preE7CharacterWindow w := by
    have hhalf : halfDegree w = 6 := by
      rw [hw12]
      norm_num [halfDegree]
    rw [preE7CharacterWindow, hhalf, hwR]
    dsimp [theta]
    norm_num [preE7CharacterRho]
    linarith
  have hparams := preE7Padded_entryParameters_withTail
    (w := w) (v0 := G.package.v) (eta := tau) (theta := tau + theta)
    htau0 N.degree_two_le hmargin htail
  have hHcoeff := degreeThreeFourBlock_translationCoefficient_le_two_rpow
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  refine
    { D := fun b => (2 : ℝ) ^ (704 : ℝ) * (1 + b)
      T := fun b => (2 : ℝ) ^ (704 : ℝ) * (1 + b)
      eta := eta
      theta := theta
      delta := delta
      cutoff := cutoff
      alpha := alpha
      alpha_eq := by simp [alpha, eta, tau, H]
      D_nonneg := fun b => by positivity
      T_nonneg := fun b => by positivity
      T_le_D := fun _ => le_rfl
      eta_le := by simpa only [eta, N.eta_eq_zero] using (show (0 : ℝ) ≤ 0 by norm_num)
      theta_le := N.theta_le
      mainCoefficient_le := ?_
      coldCoefficient_le := ?_
      width_upper := by omega
      parameters := ?_
      total_growth := ?_ }
  · intro b
    calc
      H.coefficient * G.package.envelope.mainCoefficient ≤
          (2 : ℝ) ^ (384 : ℝ) *
            ((2 : ℝ) ^ (320 : ℝ) * (1 + b)) :=
        mul_le_mul hHcoeff (N.main_le b)
          G.package.envelope.mainCoefficient_nonneg (by positivity)
      _ = ((2 : ℝ) ^ (384 : ℝ) * (2 : ℝ) ^ (320 : ℝ)) *
          (1 + b) := by ring
      _ = (2 : ℝ) ^ (704 : ℝ) * (1 + b) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
  · intro b
    calc
      H.coefficient * G.package.envelope.coldCoefficient b ≤
          (2 : ℝ) ^ (384 : ℝ) *
            ((2 : ℝ) ^ (320 : ℝ) * (1 + b)) :=
        mul_le_mul hHcoeff (N.cold_le b)
          (G.package.envelope.coldCoefficient_nonneg b) (by positivity)
      _ = ((2 : ℝ) ^ (384 : ℝ) * (2 : ℝ) ^ (320 : ℝ)) *
          (1 + b) := by ring
      _ = (2 : ℝ) ^ (704 : ℝ) * (1 + b) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
  · simpa only [delta, cutoff, alpha, eta, theta, tau, H, G, hpad,
      add_zero] using hparams
  · intro b
    have h := fourBlock_pairCoefficient_total_growth b
    simpa only [hw12, Nat.add_comm b 12] using h

/-- Final source for the nonbinary four-block exact-local-S3 cell. -/
noncomputable def degreeThreeFourBlockNonbinarySource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hnonbinary : ¬ IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let G := degreeThreeFourBlockNonbinaryGrowthPackage block P hZmud lit
    published hr hs hcomponent hnonbinary
  exact DegreeThreeSignedQuotientAdditiveNumerics.source block P
    (degreeThreeFourBlockNonbinaryAdditiveNumerics block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hgen hZmud lit published
      hr hs hcomponent hnonbinary)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
