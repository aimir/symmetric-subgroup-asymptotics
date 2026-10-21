import SymmetricSubgroupAsymptotics.C3ResidualClosure
import SymmetricSubgroupAsymptotics.C3HighSemisimpleOwnerRelabel
import SymmetricSubgroupAsymptotics.C3PhysicalOwnerBranchesWithoutCatalogue

/-! After both old structural owners and the new actual semisimple owner
are removed on the complete physical subgroup, the high term is empty.
The same direct and low original-complement rows therefore remain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

def C3ActualFinalResidualPredicate (b : ℕ)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b))) : Prop :=
  C3FinalResidualPredicate b H ∧
    ¬C3PhysicalHighSemisimpleOwner (3+b)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (H.map (fusionOrbitAction ternaryRegularAction)))

theorem c3ActualFinalResidualPredicate_natural (b : ℕ) :
    FusionOrbitNatural ternaryRegularAction (C3ActualFinalResidualPredicate b) := by
  apply fusionOrbitNatural_of_relabel_invariant ternaryRegularAction
    (c3ResidualPointEquiv b)
    (fun G => (¬IsCriticalSubgroup (3+b) G ∧
      FirstOwned (ownerOrResidualEligible c3PhysicalStructuralBranchMenu (3+b))
        (Fin.last 4) G) ∧ ¬C3PhysicalHighSemisimpleOwner (3+b) G)
  intro s G
  exact and_congr
    (ordinaryRemainder_firstOwned_relabel_iff (3+b)
      (ownerOrResidualEligible c3PhysicalStructuralBranchMenu (3+b))
      (fun i t K => ownerOrResidualEligible_natural c3PhysicalStructuralBranchMenu
        c3PhysicalStructuralBranchMenu_natural rfl t i K) (Fin.last 4) s G)
    (not_congr (c3PhysicalHighSemisimpleOwner_relabel_iff rfl s G))

theorem not_c3TrivialHigh_actualFinalResidual
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b))) :
    ¬C3TrivialHighPredicate b (C3ActualFinalResidualPredicate b) H := by
  intro hHigh
  have hr : C3ActualFinalResidualPredicate b H := hHigh.1.2
  have hRejects := (firstOwned_ownerOrResidual_last_iff
    c3PhysicalStructuralBranchMenu _).mp hr.1.2
  rcases c3TrivialHigh_enters_structural_or_semisimple_without_catalogue
    hChief hWeight hgen hindex published8 h18 b (3+b) (c3ResidualPointEquiv b)
    (C3ActualFinalResidualPredicate b) H hHigh with hOld|hNew
  · obtain ⟨i,hi⟩ := c3PhysicalStructuralBranchMenu_cover_without_catalogue
      hChief hWeight hgen hindex published8 h18 hOld
    exact hRejects i hi
  · exact hr.2 hNew

theorem c3ActualFinalResidual_highFamily_eq_empty
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ) :
    FusionOrbitFamily ternaryRegularAction
      (C3TrivialHighPredicate b (C3ActualFinalResidualPredicate b))=∅ := by
  ext K
  constructor
  · intro hK
    obtain ⟨⟨e,⟨M,hM⟩⟩,rfl⟩ := hK
    obtain ⟨H,hHigh,rfl⟩ := hM
    exact False.elim (not_c3TrivialHigh_actualFinalResidual
      hChief hWeight hgen hindex published8 h18 b H.1 H.2)
  · intro hK
    exact False.elim hK

theorem c3ActualFinalResidual_physical_frontier
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) (b : ℕ) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3ActualFinalResidualPredicate b))) : ℝ)/exactBenchmark (b+3)≤
    (c3DirectAxisKernel b+c3TrivialLowKernel b)*
      ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have hh := c3Accepted_physical_frontier b (C3ActualFinalResidualPredicate b)
    (c3ActualFinalResidualPredicate_natural b)
  have hz : c3TrivialHighRatio b (C3ActualFinalResidualPredicate b)=0 := by
    unfold c3TrivialHighRatio
    rw [c3ActualFinalResidual_highFamily_eq_empty
      hChief hWeight hgen hindex published8 h18 b]
    simp
  rw [hz] at hh
  simpa only [add_zero] using hh

end SymmetricSubgroupAsymptotics
