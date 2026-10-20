import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveNonsolubleExceptionalSource
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacityBinarySmallReduced

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

noncomputable def degreeEightOrSixteenNonsolubleSource
    (D : BinaryAffineSmallCatalogueData)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : FiniteSimpleTwoGeneratorBound)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hdegree : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16)
    (hnonsolvable : ¬ IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P := by
    by_cases h8 : Nat.card block.Fibre = 8
    · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeEight_nonsoluble hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P D h8 hnonsolvable
    · have h16 : Nat.card block.Fibre = 16 := hdegree.resolve_left h8
      exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_nonsoluble hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P D h16 hnonsolvable
  exact imprimitiveAffineComponentTransfer hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hgen block P S

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

