import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeCoefficient

/-!
# Numerical endpoint for a ternary layer over a signed pair quotient

The structural prepend theorem produces a raw source-summed row.  This file
packages the remaining faithful comparator action and numerical margin, and
installs the result in the final source-or-Yoneda-top sum.  Small pair
catalogue files can therefore export one object without duplicating either
the literal ternary incidence calculation or the terminal residual plumbing.
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

/-! ## Pointwise comparator endpoints -/

/-- Close a signed quotient which already has a faithful smaller action.
The only case-specific obligation is the displayed linear margin.  The
literal ternary coefficient is paid uniformly by
`degreeThreeTranslationCoefficient_bound`. -/
noncomputable def degreeThreeIdentitySignedQuotientSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (v : ℕ)
    (action : (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin v))
    (action_injective : Function.Injective action)
    (hv : 2 ≤ v)
    (hmargin :
      let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm
      preE7CharacterRho * w ≤
        ((evenWidth w : ℝ) - v) / 8 -
          Real.logb 2 3 / 3 * H.capacity) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let Q := RelativeCompleteSourceEnvelope.identity
    (preE7NonPairAction w U ⧸ E block P) v action action_injective
  let T := translationLayerEnvelopeOver block P H Q
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hs2 : 2 ≤ Nat.card block.Points := block.degrees_ge_two.2
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hcoeff0 := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hcoeff : H.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 (Nat.card block.Points)
        (traceyInducedGeneratorCeiling 1 (Nat.card block.Points))
        (traceyPermutationGeneratorCeiling w) w 3 := by
    simpa only [H, hpd.1, hpd.2, hp, Fintype.card_eq_nat_card] using hcoeff0
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
        RelativeCompleteSourceEnvelope.identity] using hv
    · have hep : (elementaryChart block P).p = 3 := by
        simpa only [elementaryChart] using hp
      simpa only [T, translationLayerEnvelopeOver_v,
        translationLayerEnvelopeOver_eta, Q,
        RelativeCompleteSourceEnvelope.identity, H, hep, add_zero] using
        hmargin
    · intro b
      simpa only [T, translationLayerEnvelopeOver_coefficient, Q,
        RelativeCompleteSourceEnvelope.identity, mul_one] using hD b
  let D : DegreeThreeSignedQuotientSourceData block P H :=
    { quotientEnvelope := Q
      ambientMargin := by simpa only [T] using hM }
  exact DegreeThreeSignedQuotientSourceData.source block P D

/-- At three blocks a faithful signed-quotient comparator of degree at most
three leaves a uniform margin.  The odd ambient width is essential here:
`evenWidth 9 = 8`, so the same statement is false for comparator degree four
or five at the generic capacity-one bound. -/
noncomputable def degreeThreeThreeBlocksIdentitySource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (v : ℕ)
    (action : (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin v))
    (action_injective : Function.Injective action)
    (hv2 : 2 ≤ v) (hv3 : v ≤ 3) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeThreeIdentitySignedQuotientSource block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr v action action_injective hv2
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have hcap := degreeThree_translation_capacity_threeBlocks block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hrate0 : 0 ≤ Real.logb 2 3 / 3 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have heta : Real.logb 2 3 / 3 * H.capacity ≤
      fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hcap hrate0
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hw9 : w = 9 := by
    simpa only [hr, hs] using width_eq block
  have hwR : (w : ℝ) = 9 := by exact_mod_cast hw9
  have heven : evenWidth w = 8 := by
    rw [hw9]
    norm_num [evenWidth, halfDegree]
  have hvR : (v : ℝ) ≤ 3 := by exact_mod_cast hv3
  rw [hwR, heven]
  norm_num [preE7CharacterRho]
  linarith

/-- All data after the actual signed quotient has been assigned its raw
pair-action estimate.  The numerical margin is stated on the already
prepended source, so the original physical width and the ternary exponent
are tested together. -/
structure DegreeThreeSignedQuotientSummedEndpoint
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart) : Type 1 where
  quotient : PreE7DegreeTwoPairQuotientSummedEnvelope
    (preE7NonPairAction w U ⧸ E block P)
  v : ℕ
  action : quotient.R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  margin :
    let source := prependSignedQuotientSummedSource block P H quotient
      v action action_injective
    source.NumericalMargin

namespace DegreeThreeSignedQuotientSummedEndpoint

variable
  {H : ElementaryLayerJointCapacityBound
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart}

/-- The completed correlated row, retaining the exceptional scalar only
once after the source sum. -/
noncomputable def source
    (D : DegreeThreeSignedQuotientSummedEndpoint block P H) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S := prependSignedQuotientSummedSource block P H D.quotient
    D.v D.action D.action_injective
  exact .inr (.inr (S.toResidualChoice D.margin))

end DegreeThreeSignedQuotientSummedEndpoint

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
