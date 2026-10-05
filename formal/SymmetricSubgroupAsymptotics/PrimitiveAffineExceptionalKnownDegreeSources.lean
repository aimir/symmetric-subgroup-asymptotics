import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveNonsolubleExceptionalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineWholeCoreSource

/-!
# Sources for the completed affine exceptional degrees

This file collects the already proved degree-five, degree-eight,
degree-nine, and degree-sixteen constructions behind one uniform interface.
It leaves the still separate degree-two, degree-three, and degree-four lanes
out of the dispatcher, so those lanes can be checked and integrated without
changing the completed cases below.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}

/-- The two genuinely residual degree-five cells use the checked whole-socle
character interval.  The four-block cell was already consumed by the direct
translation source before this helper is called. -/
noncomputable def degreeFiveResidualCharacterSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 5)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  letI : Nontrivial block.Points :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.2
  exact degreeFiveCharacterIntervalSource block P hZmud lit .acomp
    hTraceyHalf hTraceyPerm hr hs
      (Classical.choice (inferInstance : Nonempty block.Points))

/-- Every residual degree-nine cell is handled by the kernel-checked
whole-linear-core split, including both the zero and nonzero core. -/
noncomputable def degreeNineResidualCharacterSource
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  letI : Nontrivial block.Points :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.2
  exact degreeNineWholeCoreCharacterIntervalSource block P hClifford
    hTraceyHalf hTraceyPerm hgen hZmud lit .acomp hr hs
      (Classical.choice (inferInstance : Nonempty block.Points))

/-- The binary local degrees split on the literal complement.  Soluble
complements use the checked character interval; nonsoluble complements use
the published finite affine catalogue followed by the actual-wreath
component transfer. -/
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
    (published : PublishedPrimitiveAffineSmallCatalogueData)
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
  · exact binaryAffineExceptionalCharacterIntervalSource_of_capacityException
      block P hZmud lit hgen hClifford hTraceyPerm published
      hexception hbinary hsoluble
  · exact degreeEightOrSixteenNonsolubleSource published hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen block P
      hbinary hsoluble

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
