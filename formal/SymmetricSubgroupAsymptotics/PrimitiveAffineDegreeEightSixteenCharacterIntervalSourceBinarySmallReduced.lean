import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenCharacterIntervalSource
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenSocleGeneratorsBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

noncomputable def binaryAffineExceptionalSocleGeneratorInterval
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
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
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineExceptional_socleNormalGeneratorBound block P hgen hClifford
      hTraceyPerm published shape hsoluble block.base N hretained

noncomputable def binaryAffineExceptionalCompleteCharacterInterval
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    CompleteCharacterIntervalData (preE7NonPairAction w U) :=
  (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineExceptionalSocleGeneratorInterval block P hgen hClifford
    hTraceyPerm published shape hsoluble).toCompleteCharacterIntervalData hZmud

noncomputable def binaryAffineExceptionalCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let D := _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineExceptionalCompleteCharacterInterval block P hZmud hgen
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

noncomputable def binaryAffineExceptionalCharacterIntervalSource_of_capacityException
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (hexception : ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hbinary : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16)
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineExceptionalCharacterIntervalSource block P hZmud lit hgen
    hClifford hTraceyPerm published
      (BinaryAffineExceptionalShape.ofCapacityException_of_binaryDegree
        hexception hbinary) hsoluble

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

