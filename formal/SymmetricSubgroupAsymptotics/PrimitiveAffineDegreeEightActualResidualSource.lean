import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightActualComponentCapacity
import SymmetricSubgroupAsymptotics.BinaryAffineExceptionalActualSource

/-! The actual degree8 residual consumer keeps its original block tower in
the nonsoluble case and its correlated same-type source in the soluble case. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}

def degreeEightActualResidualSource
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hexception : ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8) : PreE7RankTailSourceOrYonedaTopData w U := by
  letI degreeEightActualResidualSource_nontrivial : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  by_cases hsoluble : IsSolvable (P.complement (origin block))
  · exact binaryAffineExceptionalActualSource_of_capacityException block P
      hZmud lit hgen hClifford hTraceyPerm hexception (Or.inl hr) hsoluble
  · exact imprimitiveAffineComponentTransfer hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hSimpleGen block P
      (DegreeEightActual.ComponentSource.of_degreeEight_nonsoluble
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hr hsoluble)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
