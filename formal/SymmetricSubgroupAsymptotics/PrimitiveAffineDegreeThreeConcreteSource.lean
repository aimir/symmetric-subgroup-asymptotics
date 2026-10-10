import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFinalAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourSignSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourOneSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourTwoSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeThreeSignIdentitySource

/-!
# Concrete degree-three affine residual source

The post-four sign partition is now exhaustive.  High sign count uses the
uniformly cyclic signed module, one and two signs use their central binary
comparators, and the sole remaining three-sign cell is the eighteen-block
capacity-three identity source.  Together with the literal four-block
two-sign comparison this removes both project-owned endpoint parameters
from the final degree-three assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Concrete post-four source in every six-, twelve-, or eighteen-block
cell with nonzero signed kernel. -/
noncomputable def degreeThreeNonzeroSignedKernelPostFourSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeThreeNonzeroSignedKernelPostFourResidualSource := by
  intro w U _hw basePoint block P _hres hr hs hcomponent _hK
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  have hsplit := degreeThreePostFour_highSign_or_lowSign
    block P hr hcomponent hs
  by_cases hhigh :
      (Nat.card block.Points = 6 ∧
          2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr))) ∨
        (Nat.card block.Points = 12 ∧
          3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr))) ∨
        (Nat.card block.Points = 18 ∧
          6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)))
  · exact degreeThreeSixOrTwelveHighSignIdentitySource block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hcomponent hhigh
  · have hlow := hsplit.resolve_left hhigh
    by_cases hs6 : Nat.card block.Points = 6
    · have hone : Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)) = 1 := by
        rcases hlow with h6 | h12 | h18
        · exact h6.2
        · omega
        · omega
      exact degreeThreePostFourOneSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inl hs6) hone
    · by_cases hs12 : Nat.card block.Points = 12
      · have h12 : Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 1 ∨
            Nat.card (BinaryPairFrame.CoordinateSign
              (degreeThreeSignedQuotientPairFrame block P hr)) = 2 := by
          rcases hlow with h6 | h12' | h18
          · omega
          · exact h12'.2
          · omega
        by_cases hone : Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 1
        · exact degreeThreePostFourOneSignSource block P
            hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr (Or.inr (Or.inl hs12)) hone
        · have htwo := h12.resolve_left hone
          exact degreeThreePostFourTwoSignSource block P
            hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr (Or.inl hs12) hcomponent htwo
      · have hs18 : Nat.card block.Points = 18 := by
          rcases hs with hs6' | hs12' | hs18'
          · exact (hs6 hs6').elim
          · exact (hs12 hs12').elim
          · exact hs18'
        have h18 : Nat.card (BinaryPairFrame.CoordinateSign
              (degreeThreeSignedQuotientPairFrame block P hr)) = 1 ∨
            Nat.card (BinaryPairFrame.CoordinateSign
              (degreeThreeSignedQuotientPairFrame block P hr)) = 2 ∨
            Nat.card (BinaryPairFrame.CoordinateSign
              (degreeThreeSignedQuotientPairFrame block P hr)) = 3 := by
          rcases hlow with h6 | h12 | h18'
          · omega
          · omega
          · exact h18'.2
        by_cases hone : Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 1
        · exact degreeThreePostFourOneSignSource block P
            hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
            hr (Or.inr (Or.inr hs18)) hone
        · have h23 := h18.resolve_left hone
          by_cases htwo : Nat.card (BinaryPairFrame.CoordinateSign
              (degreeThreeSignedQuotientPairFrame block P hr)) = 2
          · exact degreeThreePostFourTwoSignSource block P
              hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
              hr (Or.inr hs18) hcomponent htwo
          · have hthree := h23.resolve_left htwo
            exact degreeThreeEighteenThreeSignIdentitySource block P
              hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
              hr hcomponent hs18 hthree

/-- Fully concrete degree-three residual source, depending only on the
published inputs already exposed by the surrounding affine theorem. -/
noncomputable def degreeThreeResidualSource
    (hKP : KovacsPraegerAbelianizationBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (publishedPairs : PublishedDegreeTwoFourPairClassification) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_twoSignAndPostFour
    hKP publishedSix hZmud lit hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hgen publishedPairs
      degreeThreeFourBlockTwoSignComparisonSource
      (degreeThreeNonzeroSignedKernelPostFourSource
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
