import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeThreeSignCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourIdentitySource

/-!
# Identity source in the eighteen-block, three-sign cell

The capacity-three theorem leaves sufficient margin for the faithful
thirty-six-point signed quotient action.  Its coefficient is unchanged
from the published ternary translation-layer estimate.
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

/-- The three-sign eighteen-block branch closes on the literal faithful
signed quotient action of degree thirty-six. -/
noncomputable def degreeThreeEighteenThreeSignIdentitySource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := degreeThreeThreeSignJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hcomponent heighteen hthree
  let Q := RelativeCompleteSourceEnvelope.identity
    (preE7NonPairAction w U ⧸ E block P) (quotientDegree block)
    (quotientAction block P) (quotientAction_injective block P)
  let T := translationLayerEnvelopeOver block P H Q
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hs2 : 2 ≤ Nat.card block.Points := by omega
  have hv2 : 2 ≤ quotientDegree block := by
    rw [degreeThree_quotientDegree_eq_twice_blocks block hr]
    omega
  have hw : w = 54 := by
    simpa only [hr, heighteen] using width_eq block
  have hcoeff0 := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hcoeff : H.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 (Nat.card block.Points)
        (traceyInducedGeneratorCeiling 1 (Nat.card block.Points))
        (traceyPermutationGeneratorCeiling w) w 3 := by
    rw [degreeThreeThreeSignJointCapacity_coefficient_eq]
    simpa only [hpd.1, hpd.2, hp, Fintype.card_eq_nat_card] using hcoeff0
  have hD := degreeThreeTranslationCoefficient_bound
    (Nat.card block.Points) w hs2
      (by rw [heighteen, hw]; norm_num)
      H.coefficient hcoeff
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
      have hcap : H.capacity = 3 :=
        degreeThreeThreeSignJointCapacity_capacity block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
          hr hcomponent heighteen hthree
      have hq36 : quotientDegree block = 36 := by
        rw [degreeThree_quotientDegree_eq_twice_blocks block hr, heighteen]
      have hlog : Real.logb 2 3 ≤ 8 / 5 := by
        have hpow : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
        have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
          (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hpow
        simp only [Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
          simpa only [mul_comm] using le_of_lt h)
      have hraw : preE7CharacterRho * w ≤
          ((evenWidth w : ℝ) - quotientDegree block) / 8 -
            Real.logb 2 3 / 3 * H.capacity := by
        rw [hw, hq36, hcap]
        norm_num [preE7CharacterRho, evenWidth, halfDegree]
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
