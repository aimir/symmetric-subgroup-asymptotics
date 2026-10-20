import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalKnownDegreeSources
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssemblyBinarySmallReduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenCharacterIntervalSourceBinarySmallReduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveNonsolubleExceptionalSourceBinarySmallReduced

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

noncomputable def degreeEightOrSixteenResidualSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : BinaryAffineSmallCatalogueData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hexception : ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hbinary : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  by_cases hsoluble : IsSolvable (P.complement (origin block))
  · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineExceptionalCharacterIntervalSource_of_capacityException
      block P hZmud lit hgen hClifford hTraceyPerm published
      hexception hbinary hsoluble
  · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.degreeEightOrSixteenNonsolubleSource published hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen block P
      hbinary hsoluble

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

