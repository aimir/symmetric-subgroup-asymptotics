import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeRegularSixClosure
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeTopKernelZeroSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockKernelZero

/-!
# Split assembly for the degree-three affine residual

The exact local `S3` lane has one intrinsic split: the kernel of the signed
quotient on the actual blocks is either zero or nonzero.  The zero-kernel
half is now completely closed.  At four blocks it uses the original refined
capacity-one row; at the other four residual block counts it uses the
Sylow-three width row.  The nonzero half is deliberately exposed as a
construction function so that the literal degree-two pair packages can be
threaded in without a catalogue or owner-order assumption.

This file is assembly only.  In particular `DegreeThreeNonzeroSignedKernelResidualSource`
is not a mathematical assumption intended to survive the final theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Temporary construction boundary for the genuinely correlated half of
the exact local-`S3` lane.  It retains the literal nonzero block kernel and
the exact five-count residual list. -/
abbrev DegreeThreeNonzeroSignedKernelResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    (Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
      Nat.card block.Points = 6 ∨ Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18) →
    Nat.card block.Component = 6 →
    degreeNineLinearBlockKernel block P ≠ ⊥ →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Close the exact-`S3` endpoint once only its nonzero signed-kernel half
has been constructed.  All zero-kernel branches are discharged here from
the literal block system. -/
noncomputable def degreeThreeExactS3ResidualSource_of_kernelSplit
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (nonzero : DegreeThreeNonzeroSignedKernelResidualSource) :
    DegreeThreeExactS3ResidualSource := by
  intro w U hw basePoint block P hres hr hs hcomponent
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  by_cases hK : degreeNineLinearBlockKernel block P = ⊥
  · by_cases hs3 : Nat.card block.Points = 3
    · exact degreeThreeKernelZeroTopSource block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hr (Or.inl hs3) hK
    by_cases hs4 : Nat.card block.Points = 4
    · exact degreeThreeFourBlockKernelZeroSource block P hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm hr hs4 hK
    by_cases hs6 : Nat.card block.Points = 6
    · exact degreeThreeKernelZeroTopSource block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hr (Or.inr (Or.inl hs6)) hK
    by_cases hs12 : Nat.card block.Points = 12
    · exact degreeThreeKernelZeroTopSource block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hr
          (Or.inr (Or.inr (Or.inl hs12))) hK
    have hs18 : Nat.card block.Points = 18 := by
      rcases hs with h | h | h | h | h
      · exact False.elim (hs3 h)
      · exact False.elim (hs4 h)
      · exact False.elim (hs6 h)
      · exact False.elim (hs12 h)
      · exact h
    exact degreeThreeKernelZeroTopSource block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr
        (Or.inr (Or.inr (Or.inr hs18))) hK
  · exact nonzero U hw basePoint block P hres hr hs hcomponent hK

/-- Full degree-three residual source after the nonzero signed-kernel
constructor has been supplied.  The regular-`C3`, six-block endpoint is the
checked literal Schur-capacity theorem. -/
noncomputable def degreeThreeResidualSource_of_kernelSplit
    (hKP : KovacsPraegerAbelianizationBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (nonzero : DegreeThreeNonzeroSignedKernelResidualSource) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_endpoints hKP publishedSix
    (degreeThreeRegularSixResidualSource hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)
    (degreeThreeExactS3ResidualSource_of_kernelSplit hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm nonzero)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
