import SymmetricSubgroupAsymptotics.DegreeNineCentralProductComparator
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockNonbinaryClosure
import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalSmallRankTailBridge

/-!
# The one-sign four-block source

In the diagonal sign branch the signed quotient has one central binary
layer over its four-point top.  A `DegreeNineCentralProductModel` records
the complete, all-normal comparison with the faithful degree-six product
comparator.  This file prepends the literal ternary translation incidence
and checks the degree-twelve numerical window.

The result is packaged as an `S3EXC` complete source.  This is slightly more
general than assigning the historical `S3CENT` label: it uses exactly the
same complete comparator inequality, but avoids rebuilding it as one
abelian-Yoneda tower on each normal axis.
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

/-- Finite structural certificate needed by the diagonal numerical source.
The order bound is the exact consequence of a central binary layer over a
four-point top; the model retains every literal normal quotient. -/
structure DegreeThreeFourBlockDiagonalComparison : Type 2 where
  model : DegreeNineCentralProductModel
    (preE7NonPairAction w U ⧸ E block P)
  signedOrder_le :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 48

/-- The complete central-product comparison, regarded as a relative source
envelope on the literal signed quotient. -/
noncomputable def degreeThreeFourBlockDiagonalQuotientEnvelope
    (M : DegreeNineCentralProductModel
      (preE7NonPairAction w U ⧸ E block P)) :
    RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P) where
  R := M.Q
  groupR := inferInstance
  finiteR := inferInstance
  v := 6
  action := M.Q.subtype
  action_injective := Subtype.val_injective
  coefficient := fun _ ↦ M.coefficient
  eta := 0
  coefficient_nonneg := fun _ ↦ Nat.cast_nonneg _
  bound := by
    intro b J
    simpa only [zero_mul, Real.rpow_zero, mul_one] using
      (M.toComparator.complete_bound J)

/-- The diagonal central-product coefficient and the literal ternary
incidence coefficient fit in the common fixed-width menu. -/
theorem degreeThreeFourBlock_diagonalCoefficient_menu
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (M : DegreeNineCentralProductModel
      (preE7NonPairAction w U ⧸ E block P))
    (horder :
      Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 48)
    (b : ℕ) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).coefficient *
        (M.coefficient : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have hw : w = 12 := by
    simpa only [hr, hs] using width_eq block
  have hH := degreeThreeFourBlock_translationCoefficient_le_two_rpow
    block P hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hMnat : M.coefficient ≤ 2 ^ 72 := M.coefficient_le horder
  have hMreal : (M.coefficient : ℝ) ≤ (2 : ℝ) ^ (72 : ℝ) := by
    calc
      (M.coefficient : ℝ) ≤ ((2 ^ 72 : ℕ) : ℝ) := by
        exact_mod_cast hMnat
      _ = (2 : ℝ) ^ (72 : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (72 : ℝ) :=
        (Real.rpow_natCast (2 : ℝ) 72).symm
  calc
    H.coefficient * (M.coefficient : ℝ) ≤
        (2 : ℝ) ^ (384 : ℝ) * (2 : ℝ) ^ (72 : ℝ) :=
      mul_le_mul hH hMreal (Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (456 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hw]
      norm_num
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass
      (hw.symm ▸ (by norm_num : 8 ≤ 12)) b

/-- Concrete complete source for the one-sign branch.  The ternary layer
has capacity at most one, so its slope is at most `log₂(3)/3`; the degree-six
comparator leaves a strict degree-twelve margin. -/
noncomputable def degreeThreeFourBlock_diagonalExceptionalSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (M : DegreeNineCentralProductModel
      (preE7NonPairAction w U ⧸ E block P))
    (horder :
      Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 48) :
    PreE7S3ExceptionalSource w U := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let Q := degreeThreeFourBlockDiagonalQuotientEnvelope block P M
  let T := translationLayerEnvelopeOver block P H Q
  have hw : w = 12 := by
    simpa only [hr, hs] using width_eq block
  have hpd := degreeThree_translation_prime_dim block P hr
  have hp : (elementaryChart block P).p = 3 := by
    simpa only [elementaryChart, localTranslationChart] using hpd.1
  have hcap := degreeThree_translation_capacity_fourBlocks block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hgamma0 : 0 ≤ Real.logb 2 3 / 3 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  refine
    { sourceDegree := 6
      sourceDegree_two := by norm_num
      Q := M.Q
      B := H.coefficient * (M.coefficient : ℝ)
      C := 0
      eta := Real.logb 2 3 / 3 * H.capacity
      theta := 0
      B_nonneg := mul_nonneg H.coefficient_nonneg (Nat.cast_nonneg _)
      C_nonneg := le_rfl
      eta_nonneg := mul_nonneg hgamma0 H.capacity_nonneg
      exponent_margin := ?_
      tail_window := by
        rw [hw]
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      complete_bound := ?_
      main_menu := ?_
      tail_menu := ?_ }
  · have hgamma :=
      fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
    have heta :
        Real.logb 2 3 / 3 * H.capacity ≤ 17 / 32 := by
      calc
        Real.logb 2 3 / 3 * H.capacity ≤
            Real.logb 2 3 / 3 * 1 :=
          mul_le_mul_of_nonneg_left hcap hgamma0
        _ = fixedTargetCompositionGamma := by
          simp [fixedTargetCompositionGamma]
        _ ≤ 17 / 32 := hgamma
    have hwreal : (w : ℝ) = 12 := by exact_mod_cast hw
    have heven : evenWidth w = 12 := by
      norm_num [evenWidth, halfDegree, hw]
    rw [hwreal, heven]
    norm_num [preE7CharacterRho]
    linarith
  · intro b J
    have h := T.bound b J
    simpa only [T, Q, translationLayerEnvelopeOver_v,
      translationLayerEnvelopeOver_eta,
      translationLayerEnvelopeOver_coefficient,
      degreeThreeFourBlockDiagonalQuotientEnvelope, hp, zero_add, zero_mul,
      Real.rpow_zero, mul_one, add_zero] using h
  · intro b
    exact degreeThreeFourBlock_diagonalCoefficient_menu block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hs M horder b
  · intro b
    exact le_trans le_rfl (by positivity)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
