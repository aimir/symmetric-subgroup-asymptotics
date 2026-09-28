import SymmetricSubgroupAsymptotics.C3PhysicalOwnerBranches
import SymmetricSubgroupAsymptotics.C3PhysicalFrontier

/-!
# Closing the residual regular-C3 physical branch

The complete physical high-C3 owner is placed first in a singleton owner
menu and followed by the canonical residual branch.  On that residual
predicate the high trivial-axis family is empty.  The complete regular-C3
family therefore consists only of the already checked direct and low rows.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The fixed complete physical labels used by the residual C3 row. -/
def c3ResidualPointEquiv (b : ℕ) :
    TernaryCyclic ⊕ Fin b ≃ Fin (3+b) :=
  (Equiv.sumCongr RepeatedMarkerOwnerBound.ternaryFinEquiv
    (Equiv.refl _)).trans finSumFinEquiv

/-- The exact noncritical residual predicate after the high-C3 structural
owner.  It is tested on the reconstructed complete physical subgroup. -/
def C3FinalResidualPredicate (b : ℕ)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) : Prop :=
  ¬ IsCriticalSubgroup (3+b)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (H.map (fusionOrbitAction ternaryRegularAction))) ∧
    FirstOwned
      (ownerOrResidualEligible c3PhysicalStructuralBranchMenu (3+b))
      (Fin.last 4)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (H.map (fusionOrbitAction ternaryRegularAction)))

theorem c3FinalResidualPredicate_natural (b : ℕ) :
    FusionOrbitNatural ternaryRegularAction
      (C3FinalResidualPredicate b) := by
  apply fusionOrbitNatural_of_relabel_invariant ternaryRegularAction
    (c3ResidualPointEquiv b)
    (fun G => ¬ IsCriticalSubgroup (3+b) G ∧
      FirstOwned
        (ownerOrResidualEligible c3PhysicalStructuralBranchMenu (3+b))
        (Fin.last 4) G)
  intro s G
  exact ordinaryRemainder_firstOwned_relabel_iff (3+b)
    (ownerOrResidualEligible c3PhysicalStructuralBranchMenu (3+b))
    (fun i t K => ownerOrResidualEligible_natural
      c3PhysicalStructuralBranchMenu
      c3PhysicalStructuralBranchMenu_natural rfl t i K)
    (Fin.last 4) s G

/-- The sole formerly open high trivial-axis branch cannot survive the
physical residual owner predicate. -/
theorem not_c3TrivialHigh_finalResidual
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) :
    ¬ C3TrivialHighPredicate b (C3FinalResidualPredicate b) H := by
  intro hHigh
  have hResidual := hHigh.1.2.2
  have hRejects : ∀ i : Fin 4,
      ¬ c3PhysicalStructuralBranchMenu (3+b) i
        (relabelSubgroup (c3ResidualPointEquiv b)
          (H.map (fusionOrbitAction ternaryRegularAction))) :=
    (firstOwned_ownerOrResidual_last_iff
      c3PhysicalStructuralBranchMenu _).mp hResidual
  obtain ⟨i, hi⟩ := c3TrivialHigh_enters_physicalStructuralBranchMenu
    hChief hWeight hPrimitive h18 b (3+b) (c3ResidualPointEquiv b)
    (C3FinalResidualPredicate b) H hHigh
  exact hRejects i hi

theorem c3FinalResidual_highFamily_eq_empty
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ) :
    FusionOrbitFamily ternaryRegularAction
      (C3TrivialHighPredicate b (C3FinalResidualPredicate b)) = ∅ := by
  ext K
  constructor
  · intro hK
    obtain ⟨⟨e, ⟨M, hM⟩⟩, rfl⟩ := hK
    obtain ⟨H, hHigh, rfl⟩ := hM
    exact False.elim
      (not_c3TrivialHigh_finalResidual
        hChief hWeight hPrimitive h18 b H.1 H.2)
  · intro hK
    exact False.elim hK

theorem c3FinalResidual_highRatio_eq_zero
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ) :
    c3TrivialHighRatio b (C3FinalResidualPredicate b) = 0 := by
  unfold c3TrivialHighRatio
  rw [c3FinalResidual_highFamily_eq_empty
    hChief hWeight hPrimitive h18 b]
  simp

/-- Complete c=1 audit: the appended residual owner has only the two checked
contracting rows.  The high term vanishes identically before any numerical
estimate is applied. -/
theorem c3FinalResidual_physical_frontier
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3FinalResidualPredicate b))) : ℝ) /
        exactBenchmark (b+3) ≤
      (c3DirectAxisKernel b + c3TrivialLowKernel b) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  have h := c3Accepted_physical_frontier b (C3FinalResidualPredicate b)
    (c3FinalResidualPredicate_natural b)
  rw [c3FinalResidual_highRatio_eq_zero
    hChief hWeight hPrimitive h18 b] at h
  simpa only [add_zero] using h

end SymmetricSubgroupAsymptotics

end
