import SymmetricSubgroupAsymptotics.C3CompletePhysicalContinuation
import SymmetricSubgroupAsymptotics.C3ActualResidualForwardEstimate
import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedExhaustionWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3HighSemisimpleForwardEstimate

/-! The complete original c=1 family splits into the unchanged old physical
owner sector, the new actual semisimple sector, and the direct/low residual
sector. All three forward estimates are proved, with the complete subgroup,
normal axes, original complement degree and benchmark weights retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

def C3ActualFinalResidualPhysicalSet (b : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin (3+b)))) :=
  FusionRelabelledFamily (c3ResidualPointEquiv b)
    (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction (C3ActualFinalResidualPredicate b)))

/-- Every complete noncritical regular-C3 subgroup is accepted by the
invariant structural owner or by the appended residual owner. The split is
performed after all physical relabellings, so it does not depend on a chosen
local chart. -/
theorem c3CompleteOrdinaryPhysical_three_sector_cover
    (b : ℕ) (G : Subgroup (Equiv.Perm (Fin (3+b))))
    (hG : G ∈ C3CompleteOrdinaryPhysicalSet b) :
    G ∈ C3PhysicalStructuralOwnerSet (3+b) ∨
      G ∈ C3HighSemisimpleForward.sector (3+b) ∨
        G ∈ C3ActualFinalResidualPhysicalSet b := by
  obtain ⟨⟨K, hK⟩, rfl⟩ := hG
  obtain ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩ := hK
  obtain ⟨H, hAccepted, rfl⟩ := hM
  let K₀ := H.1.map (fusionOrbitAction ternaryRegularAction)
  let t : Equiv.Perm (Fin (3+b)) :=
    (c3ResidualPointEquiv b).symm.trans
      (s.trans (c3ResidualPointEquiv b))
  have ht : (c3ResidualPointEquiv b).trans t =
      s.trans (c3ResidualPointEquiv b) := by
    ext x
    simp only [t, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hphysical :
      relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀) =
        relabelSubgroup t
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
    simp only [relabelSubgroup_trans, ht]
  have hnoncritical₀ :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b) K₀) := H.2.2.1
  have hpattern₀ : C1DegreeNineSourcePattern
      (relabelSubgroup (c3ResidualPointEquiv b) K₀) := H.2.2.2
  have hpattern : C1DegreeNineSourcePattern
      (relabelSubgroup (c3ResidualPointEquiv b)
        (relabelSubgroup s K₀)) := by
    rw [hphysical]
    exact hpattern₀.relabel t
  have hnoncritical :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀)) := by
    rw [hphysical]
    exact (ordinaryRemainder_relabel_iff (3+b) t _).mpr hnoncritical₀
  by_cases hOwner : C3PhysicalStructuralOwner (3+b)
      (relabelSubgroup (c3ResidualPointEquiv b)
        (relabelSubgroup s K₀))
  · exact Or.inl ⟨hnoncritical, hOwner, hpattern⟩
  · by_cases hNew : C3PhysicalHighSemisimpleOwner (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b) (relabelSubgroup s K₀))
    · exact Or.inr (Or.inl hNew)
    · right
      right
      have hNew₀ : ¬C3PhysicalHighSemisimpleOwner (3+b)
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
        intro h
        apply hNew
        rw [hphysical]
        exact (c3PhysicalHighSemisimpleOwner_relabel_iff rfl t _).mpr h
      have hOwner₀ : ¬ C3PhysicalStructuralOwner (3+b)
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
        intro h
        apply hOwner
        rw [hphysical]
        exact (c3PhysicalStructuralOwner_relabel_iff rfl t _).mpr h
      have hRejects : ∀ i : Fin 4,
          ¬ c3PhysicalStructuralBranchMenu (3+b) i
            (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
        intro i hi
        apply hOwner₀
        exact c3PhysicalStructuralOwnerBranch_owner hi
      have hResidual : C3ActualFinalResidualPredicate b H.1 := by
        refine ⟨⟨hnoncritical₀,?_⟩,hNew₀⟩
        exact (firstOwned_ownerOrResidual_last_iff
          c3PhysicalStructuralBranchMenu _).mpr hRejects
      refine ⟨⟨relabelSubgroup s K₀, ?_⟩, rfl⟩
      refine ⟨⟨s, ⟨K₀, ?_⟩⟩, rfl⟩
      exact ⟨⟨H.1, ⟨H.2.1, hResidual⟩⟩, rfl⟩

def c3CompleteActualPhysicalBranchFamily (b : ℕ) :
    Fin 3 → Set (Subgroup (Equiv.Perm (Fin (3+b))))
  | 0 => C3PhysicalStructuralOwnerSet (3+b)
  | 1 => C3HighSemisimpleForward.sector (3+b)
  | 2 => C3ActualFinalResidualPhysicalSet b

theorem c3CompleteOrdinaryPhysical_three_sector_card_le (b : ℕ) :
    Nat.card (C3CompleteOrdinaryPhysicalSet b)≤
      Nat.card (C3PhysicalStructuralOwnerSet (3+b))+
      Nat.card (C3HighSemisimpleForward.sector (3+b))+
      Nat.card (C3ActualFinalResidualPhysicalSet b) := by
  have hh := fusionPhysicalUnion_card_le (C3CompleteOrdinaryPhysicalSet b)
    (c3CompleteActualPhysicalBranchFamily b) (by
      intro G hG
      rcases c3CompleteOrdinaryPhysical_three_sector_cover b G hG with h|h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩)
  simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,c3CompleteActualPhysicalBranchFamily,
    add_zero,add_assoc] using hh

theorem c3CompleteOrdinaryRatio_le_three_sectors (n : ℕ) (hn : 3≤n) :
    c3CompleteOrdinaryRatio n≤
      (c3PhysicalStructuralOwnerRatio n+C3HighSemisimpleForward.ratio n)+
        c3ActualFinalResidualRatio n := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 3+b-3=b := by omega
  have hh := c3CompleteOrdinaryPhysical_three_sector_card_le b
  have hhR : (Nat.card (C3CompleteOrdinaryPhysicalSet b) : ℝ)≤
      (Nat.card (C3PhysicalStructuralOwnerSet (3+b)) : ℝ)+
      (Nat.card (C3HighSemisimpleForward.sector (3+b)) : ℝ)+
      (Nat.card (C3ActualFinalResidualPhysicalSet b) : ℝ) := by exact_mod_cast hh
  have hcard : Nat.card (C3ActualFinalResidualPhysicalSet b)=
      Nat.card (FusionOrbitFamily ternaryRegularAction
        (FusionAcceptedOrbitPredicate ternaryRegularAction (C3ActualFinalResidualPredicate b))) :=
    fusionRelabelledFamily_card _ _
  rw [hcard] at hhR
  unfold c3CompleteOrdinaryRatio c3PhysicalStructuralOwnerRatio
    C3HighSemisimpleForward.ratio c3ActualFinalResidualRatio
  rw [if_pos (by omega),if_pos (by omega),hsub]
  exact (div_le_div_of_nonneg_right hhR (exactBenchmark_pos (3+b)).le).trans_eq (by ring)

/-- The unchanged complete regular-C3 family has a complete forward estimate
without C336 or an unproved strict-head/high-owner input. -/
def c3CompleteOrdinary_closedExponentialForwardEstimate_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : Non2UnipotentPrefixFiniteMenu.SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate c3CompleteOrdinaryRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
      (OrdinaryFrontierClosure.ExponentialForwardEstimate.add
        (c3PhysicalStructuralOwner_closedExponentialForwardEstimate_without_catalogue
          hChief hWeight hgen hindex published8 h18 hKP)
        (C3HighSemisimpleForward.forwardEstimate hindex published8 hOuter hcoarse))
      (c3ActualFinalResidual_exponentialForwardEstimate
        hChief hWeight hgen hindex published8 h18))
    3 c3CompleteOrdinaryRatio_le_three_sectors

end SymmetricSubgroupAsymptotics
