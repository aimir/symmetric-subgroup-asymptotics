import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeHighSignRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourIdentitySource

/-!
# Post-four identity source in the high-sign branch

The cyclic signed-coordinate theorem sharpens the actual joint capacity to
one while retaining its published fixed-top coefficient.  We use that new
capacity record directly in the ternary prepend; no minimality claim about
the separately chosen Tracey record is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The capacity-one joint record supplied by the literal high-sign
ternary module. -/
noncomputable def degreeThreeHighSignJointCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 18 ∧
        6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let huniform := degreeThreeActualAmbient_dual_uniform_high_sign
    block P hTraceyPerm hr hcomponent hsize
  simpa only [S, C, H, initialState, localTranslationChart,
    elementaryChart, ActualWreathAffineCapacity.E,
    PermutationalWreathProduct.Compression.kernelElementaryChart] using
      ActualWreathAffineCapacity.jointCapacitySharpenToOne_of_ambientDual_uniform
        S (localMap block P) C H huniform

@[simp] theorem degreeThreeHighSignJointCapacity_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 18 ∧
        6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    (degreeThreeHighSignJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hcomponent hsize).capacity = 1 := by
  simp [degreeThreeHighSignJointCapacity]

theorem degreeThreeHighSignJointCapacity_coefficient_eq
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 18 ∧
        6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    (degreeThreeHighSignJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hcomponent hsize).coefficient =
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).coefficient := by
  simp [degreeThreeHighSignJointCapacity]

/-- The high-sign post-four branch closes on the faithful literal signed
quotient action of degree twice the block count. -/
noncomputable def degreeThreeSixOrTwelveHighSignIdentitySource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 18 ∧
        6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := degreeThreeHighSignJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hcomponent hsize
  let Q := RelativeCompleteSourceEnvelope.identity
    (preE7NonPairAction w U ⧸ E block P) (quotientDegree block)
    (quotientAction block P) (quotientAction_injective block P)
  let T := translationLayerEnvelopeOver block P H Q
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hs : Nat.card block.Points = 6 ∨ Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18 := by
    rcases hsize with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  have hs2 : 2 ≤ Nat.card block.Points := by
    rcases hs with h | h | h <;> omega
  have hv2 : 2 ≤ quotientDegree block := by
    rw [degreeThree_quotientDegree_eq_twice_blocks block hr]
    omega
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hcoeff0 := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hcoeff : H.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 (Nat.card block.Points)
        (traceyInducedGeneratorCeiling 1 (Nat.card block.Points))
        (traceyPermutationGeneratorCeiling w) w 3 := by
    rw [degreeThreeHighSignJointCapacity_coefficient_eq]
    simpa only [hpd.1, hpd.2, hp, Fintype.card_eq_nat_card] using hcoeff0
  have hD := degreeThreeTranslationCoefficient_bound
    (Nat.card block.Points) w hs2 hw H.coefficient hcoeff
  have hM : RelativeCompleteSourceEnvelope.PreE7Margin T := by
    refine
    { eta_nonneg := ?_
      seedDegree_two_le := ?_
      margin := ?_
      coefficient_bound := ?_ }
    · change 0 ≤ Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity + 0
      have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
        Real.logb_nonneg (by norm_num)
          (by exact_mod_cast (elementaryChart block P).p_prime.one_le)
      exact add_nonneg
        (mul_nonneg (div_nonneg hlog (by positivity)) H.capacity_nonneg)
        le_rfl
    · simpa only [T, translationLayerEnvelopeOver_v, Q,
        RelativeCompleteSourceEnvelope.identity] using hv2
    · have hep : (elementaryChart block P).p = 3 := by
        simpa only [elementaryChart] using hp
      have hcap : H.capacity = 1 := by
        exact degreeThreeHighSignJointCapacity_capacity block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr hcomponent hsize
      have hlog : Real.logb 2 3 ≤ 8 / 5 := by
        have hpow : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
        have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
          (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hpow
        simp only [Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
          simpa only [mul_comm] using le_of_lt h)
      have hcost : Real.logb 2 3 / 3 * H.capacity ≤ 8 / 15 := by
        rw [hcap]
        simpa only [mul_one] using
          (show Real.logb 2 3 / 3 ≤ 8 / 15 by linarith)
      have hq := degreeThree_quotientDegree_eq_twice_blocks block hr
      have hraw : preE7CharacterRho * w ≤
          ((evenWidth w : ℝ) - quotientDegree block) / 8 -
            Real.logb 2 3 / 3 * H.capacity := by
        rcases hs with hs | hs | hs
        · have hw18 : w = 18 := by simpa only [hs] using hw
          have hq12 : quotientDegree block = 12 := by simpa only [hs] using hq
          have hw18R : (w : ℝ) = 18 := by exact_mod_cast hw18
          have heven18R : (evenWidth w : ℝ) = 18 := by
            rw [hw18]
            norm_num [evenWidth, halfDegree]
          have hq12R : (quotientDegree block : ℝ) = 12 := by
            exact_mod_cast hq12
          rw [hw18R, heven18R, hq12R]
          norm_num [preE7CharacterRho]
          linarith
        · have hw36 : w = 36 := by simpa only [hs] using hw
          have hq24 : quotientDegree block = 24 := by simpa only [hs] using hq
          have hw36R : (w : ℝ) = 36 := by exact_mod_cast hw36
          have heven36R : (evenWidth w : ℝ) = 36 := by
            rw [hw36]
            norm_num [evenWidth, halfDegree]
          have hq24R : (quotientDegree block : ℝ) = 24 := by
            exact_mod_cast hq24
          rw [hw36R, heven36R, hq24R]
          norm_num [preE7CharacterRho]
          linarith
        · have hw54 : w = 54 := by simpa only [hs] using hw
          have hq36 : quotientDegree block = 36 := by simpa only [hs] using hq
          have hw54R : (w : ℝ) = 54 := by exact_mod_cast hw54
          have heven54R : (evenWidth w : ℝ) = 54 := by
            rw [hw54]
            norm_num [evenWidth, halfDegree]
          have hq36R : (quotientDegree block : ℝ) = 36 := by
            exact_mod_cast hq36
          rw [hw54R, heven54R, hq36R]
          norm_num [preE7CharacterRho]
          linarith
      simpa only [T, translationLayerEnvelopeOver_v,
        translationLayerEnvelopeOver_eta, Q,
        RelativeCompleteSourceEnvelope.identity, hep, add_zero] using hraw
    · intro b
      simpa only [T, translationLayerEnvelopeOver_coefficient, Q,
        RelativeCompleteSourceEnvelope.identity, mul_one] using hD b
  let D : DegreeThreeSignedQuotientSourceData block P H :=
    { quotientEnvelope := Q
      ambientMargin := by simpa only [T] using hM }
  exact DegreeThreeSignedQuotientSourceData.source block P D

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
