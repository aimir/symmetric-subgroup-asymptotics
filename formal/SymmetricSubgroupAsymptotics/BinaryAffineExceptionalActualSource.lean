import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightActualCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTranslationColdSource

/-! The five actual binary-affine exceptional cells have complete original
sources. Degree8 uses the proved degree8 facts and the original same-type
socle sharing. Degree16 uses the actual elementary-kernel cold moment.
No bundled8/16 catalogue data or published16 locator is a parameter. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

def binaryAffineExceptionalActualSource
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (shape : BinaryAffineExceptionalShape (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply Classical.choice
  cases shape with
  | degreeEight hr hs =>
      exact ⟨DegreeEightActual.binaryAffineExceptionalCharacterIntervalSource
        block P hZmud lit hgen hClifford hTraceyPerm hr (.degreeEight hr hs) hsoluble⟩
  | degreeSixteen hr hs =>
      exact ⟨sixteenExceptionalTranslationColdSource block P hTraceyPerm hr hs⟩

def binaryAffineExceptionalActualSource_of_capacityException
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hexception : ImprimitiveAffineCapacityException (Nat.card block.Fibre) (Nat.card block.Points))
    (hbinary : Nat.card block.Fibre=8 ∨ Nat.card block.Fibre=16)
    (hsoluble : IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  binaryAffineExceptionalActualSource block P hZmud lit hgen hClifford hTraceyPerm
    (BinaryAffineExceptionalShape.ofCapacityException_of_binaryDegree hexception hbinary) hsoluble

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
