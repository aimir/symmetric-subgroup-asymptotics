import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeResidualSplitAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeThreeBlockCorrelatedSource

/-!
# Remove the three-block cell from the nonzero signed-kernel residual

The literal correlated three-block source leaves only the four, six,
twelve, and eighteen block counts in the nonzero signed-kernel lane.  This
file performs that assembly without forgetting the original block system or
turning an owner label into a source theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Construction boundary after the intrinsic three-block correlated row
has been discharged.  This is an intermediate source type, not a premise of
the final theorem. -/
abbrev DegreeThreeNonzeroSignedKernelLaterResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    (Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) →
    Nat.card block.Component = 6 →
    degreeNineLinearBlockKernel block P ≠ ⊥ →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Insert the checked correlated three-block construction and expose only
the four later block counts. -/
noncomputable def degreeThreeNonzeroSignedKernelSource_of_later
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (later : DegreeThreeNonzeroSignedKernelLaterResidualSource) :
    DegreeThreeNonzeroSignedKernelResidualSource := by
  intro w U hw basePoint block P hres hr hs hcomponent hK
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  by_cases hs3 : Nat.card block.Points = 3
  · letI : Nontrivial block.Points :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hs3]; norm_num)
    exact degreeThreeThreeBlockNonzeroCorrelatedSource block P hZmud lit
      hClifford hTraceyPerm hr hs3
        (Classical.choice (inferInstance : Nonempty block.Points)) hK
  by_cases hs4 : Nat.card block.Points = 4
  · exact later U hw basePoint block P hres hr (Or.inl hs4) hcomponent hK
  by_cases hs6 : Nat.card block.Points = 6
  · exact later U hw basePoint block P hres hr
      (Or.inr (Or.inl hs6)) hcomponent hK
  by_cases hs12 : Nat.card block.Points = 12
  · exact later U hw basePoint block P hres hr
      (Or.inr (Or.inr (Or.inl hs12))) hcomponent hK
  have hs18 : Nat.card block.Points = 18 := by
    rcases hs with h | h | h | h | h
    · exact False.elim (hs3 h)
    · exact False.elim (hs4 h)
    · exact False.elim (hs6 h)
    · exact False.elim (hs12 h)
    · exact h
  exact later U hw basePoint block P hres hr
    (Or.inr (Or.inr (Or.inr hs18))) hcomponent hK

/-- Full degree-three residual source with only the four later nonzero-kernel
block counts left as an intermediate construction input. -/
noncomputable def degreeThreeResidualSource_of_nonzeroLater
    (hKP : KovacsPraegerAbelianizationBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (later : DegreeThreeNonzeroSignedKernelLaterResidualSource) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_kernelSplit hKP publishedSix hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm
      (degreeThreeNonzeroSignedKernelSource_of_later hZmud lit hClifford
        hTraceyPerm later)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
