import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenSocleGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource

/-!
# Character-interval sources for affine degrees eight and sixteen

The structural files prove the sharp whole-socle normal-generator budgets
for the five soluble exceptional cells.  This file performs only the common
Zmud character conversion, the fixed-width arithmetic, and the dispatch
from the numerical affine exception.  The literal translation intersection,
block action, and every quotient below it remain unchanged.
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

private theorem logb_two_five_lt_seven_thirds_816 :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

theorem degreeEight_quotientDegree_eq_seven_mul
    (hr : Nat.card block.Fibre = 8) :
    quotientDegree block = 7 * Nat.card block.Points := by
  rw [quotientDegree_eq, hr]

theorem degreeSixteen_quotientDegree_eq_fifteen_mul
    (hr : Nat.card block.Fibre = 16) :
    quotientDegree block = 15 * Nat.card block.Points := by
  rw [quotientDegree_eq, hr]

theorem degreeEight_comparator_margin_of_width
    (s : ℕ) (hs : 2 ≤ s) :
    preE7CharacterRho * ((8 * s : ℕ) : ℝ) ≤
      ((evenWidth (8 * s) : ℝ) - (max 2 (7 * s) : ℕ)) / 8 := by
  have hhalf : halfDegree (8 * s) = 4 * s := by
    unfold halfDegree
    omega
  have heven : evenWidth (8 * s) = 8 * s := by
    unfold evenWidth
    rw [hhalf]
    omega
  have hmax : max 2 (7 * s) = 7 * s := max_eq_right (by omega)
  rw [heven, hmax]
  unfold preE7CharacterRho
  push_cast
  nlinarith

theorem degreeSixteen_comparator_margin_of_width
    (s : ℕ) (hs : 2 ≤ s) :
    preE7CharacterRho * ((16 * s : ℕ) : ℝ) ≤
      ((evenWidth (16 * s) : ℝ) - (max 2 (15 * s) : ℕ)) / 8 := by
  have hhalf : halfDegree (16 * s) = 8 * s := by
    unfold halfDegree
    omega
  have heven : evenWidth (16 * s) = 16 * s := by
    unfold evenWidth
    rw [hhalf]
    omega
  have hmax : max 2 (15 * s) = 15 * s := max_eq_right (by omega)
  rw [heven, hmax]
  unfold preE7CharacterRho
  push_cast
  nlinarith

theorem degreeEight_theta_window_of_width
    (s : ℕ) :
    (s : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow (8 * s) := by
  have hcoefficient : Real.logb 2 5 / 3 ≤ (7 : ℝ) / 9 := by
    linarith [logb_two_five_lt_seven_thirds_816]
  have hmul := mul_le_mul_of_nonneg_left hcoefficient
    (Nat.cast_nonneg s)
  have hhalf : halfDegree (8 * s) = 4 * s := by
    unfold halfDegree
    omega
  apply hmul.trans
  rw [preE7CharacterWindow, hhalf]
  unfold preE7CharacterRho
  push_cast
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  nlinarith [hs0]

theorem degreeSixteen_theta_window_of_width
    (s : ℕ) :
    ((2 * s : ℕ) : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow (16 * s) := by
  have hcoefficient : Real.logb 2 5 / 3 ≤ (7 : ℝ) / 9 := by
    linarith [logb_two_five_lt_seven_thirds_816]
  have hmul := mul_le_mul_of_nonneg_left hcoefficient
    (show (0 : ℝ) ≤ ((2 * s : ℕ) : ℝ) by positivity)
  have hhalf : halfDegree (16 * s) = 8 * s := by
    unfold halfDegree
    omega
  apply hmul.trans
  rw [preE7CharacterWindow, hhalf]
  unfold preE7CharacterRho
  push_cast
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  nlinarith [hs0]

/-- The literal interval below the actual translation intersection in all
five soluble degree-eight/sixteen exceptional cells. -/
noncomputable def binaryAffineExceptionalSocleGeneratorInterval
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := binaryAffineExceptionalSlots
    (Nat.card block.Fibre) (Nat.card block.Points)
  quotientSocleGenerators := fun N hretained =>
    binaryAffineExceptional_socleNormalGeneratorBound block P hgen hClifford
      hTraceyPerm published shape hsoluble block.base N hretained

/-- Install the published Zmud faithful-character theorem after the proved
whole-socle bound. -/
noncomputable def binaryAffineExceptionalCompleteCharacterInterval
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    CompleteCharacterIntervalData (preE7NonPairAction w U) :=
  (binaryAffineExceptionalSocleGeneratorInterval block P hgen hClifford
    hTraceyPerm published shape hsoluble).toCompleteCharacterIntervalData hZmud

/-- Counting-ready source for a soluble degree-eight or degree-sixteen
exceptional affine component.  Its finite coefficient is paid by the shared
bounded-width envelope. -/
noncomputable def binaryAffineExceptionalCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let D := binaryAffineExceptionalCompleteCharacterInterval block P hZmud hgen
    hClifford hTraceyPerm published shape hsoluble
  apply boundedCompleteCharacterSource D lit .acomp
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    have hs : 2 ≤ Nat.card block.Points := block.degrees_ge_two.2
    cases shape with
    | degreeEight hr hcounts =>
        have hw : w = 8 * Nat.card block.Points := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
            _ = 8 * Nat.card block.Points := by rw [hr]
        have hq := degreeEight_quotientDegree_eq_seven_mul block hr
        simpa only [hw, hq] using
          degreeEight_comparator_margin_of_width
            (Nat.card block.Points) hs
    | degreeSixteen hr hcounts =>
        have hw : w = 16 * Nat.card block.Points := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
            _ = 16 * Nat.card block.Points := by rw [hr]
        have hq := degreeSixteen_quotientDegree_eq_fifteen_mul block hr
        simpa only [hw, hq] using
          degreeSixteen_comparator_margin_of_width
            (Nat.card block.Points) hs
  · change
      (binaryAffineExceptionalSlots
        (Nat.card block.Fibre) (Nat.card block.Points) : ℝ) *
          (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    cases shape with
    | degreeEight hr hcounts =>
        have hw : w = 8 * Nat.card block.Points := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
            _ = 8 * Nat.card block.Points := by rw [hr]
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeEight
          (.degreeEight hr hcounts) hr]
        have hwindow : preE7CharacterWindow w =
            preE7CharacterWindow (8 * Nat.card block.Points) :=
          congrArg preE7CharacterWindow hw
        exact (degreeEight_theta_window_of_width
          (Nat.card block.Points)).trans_eq hwindow.symm
    | degreeSixteen hr hcounts =>
        have hw : w = 16 * Nat.card block.Points := by
          calc
            w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
            _ = 16 * Nat.card block.Points := by rw [hr]
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeSixteen
          (.degreeSixteen hr hcounts) hr]
        have hwindow : preE7CharacterWindow w =
            preE7CharacterWindow (16 * Nat.card block.Points) :=
          congrArg preE7CharacterWindow hw
        exact (degreeSixteen_theta_window_of_width
          (Nat.card block.Points)).trans_eq hwindow.symm
  ·
    cases shape with
    | degreeEight hr hcounts =>
        rcases hcounts with hs | hs | hs
        all_goals rw [width_eq block, hr, hs] <;> norm_num
    | degreeSixteen hr hcounts =>
        rcases hcounts with hs | hs
        all_goals rw [width_eq block, hr, hs] <;> norm_num

/-- Dispatch a numerical affine exception known to have binary local degree
to the preceding literal soluble source. -/
noncomputable def binaryAffineExceptionalCharacterIntervalSource_of_capacityException
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (hexception : ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hbinary : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16)
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  binaryAffineExceptionalCharacterIntervalSource block P hZmud lit hgen
    hClifford hTraceyPerm published
      (BinaryAffineExceptionalShape.ofCapacityException_of_binaryDegree
        hexception hbinary) hsoluble

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
