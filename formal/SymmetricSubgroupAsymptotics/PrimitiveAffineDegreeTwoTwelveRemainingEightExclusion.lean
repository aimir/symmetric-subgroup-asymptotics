import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow181GraphInstalledJoint
/-! Shared numeric exclusion for all eight candidates after checked275.
Only Fin8 and fresh additional sets are evaluated, never a301×old-union test. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRemainingEightExclusion

def index : Fin 8 → Fin 301 := ![21,26,48,60,61,66,186,271]
def candidates : Finset (Fin 301) := Finset.univ.image index
private theorem h0 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveAlternateInstalledJoint.installedIndices := by
  have he : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveFlexibleInstalledJoint.exactIndices := by decide +kernel
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveAlternateInstalledJoint.alternateIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveAlternateInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨he i,ha i⟩
private theorem h1 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRecoveredInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRecoveredInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRecoveredInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h0 i,ha i⟩
private theorem h2 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveStructuralInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveStructuralInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveStructuralInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h1 i,ha i⟩
private theorem h3 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveTernaryInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveTernaryInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveTernaryInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h2 i,ha i⟩
private theorem h4 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow182InstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow182InstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow182InstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h3 i,ha i⟩
private theorem h5 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow269InstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow269InstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow269InstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h4 i,ha i⟩
private theorem h6 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h5 i,ha i⟩
private theorem h7 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePrimitiveTwelveInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePrimitiveTwelveInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelvePrimitiveTwelveInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h6 i,ha i⟩
private theorem h8 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveNaturalOneSixPairInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveNaturalOneSixPairInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveNaturalOneSixPairInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h7 i,ha i⟩
private theorem h9 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow200InstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow200InstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow200InstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h8 i,ha i⟩
private theorem h10 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveJoinedHalfCycleInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveJoinedHalfCycleInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveJoinedHalfCycleInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h9 i,ha i⟩
private theorem h11 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow220InstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow220InstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow220InstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h10 i,ha i⟩
private theorem h12 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h11 i,ha i⟩
private theorem h13 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveOppositeSingerInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveOppositeSingerInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveOppositeSingerInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h12 i,ha i⟩
private theorem h14 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow57EdgeInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow57EdgeInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow57EdgeInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h13 i,ha i⟩
private theorem h15 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveEdgeFollowupInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveEdgeFollowupInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveEdgeFollowupInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h14 i,ha i⟩
private theorem h16 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDihedralFourInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDihedralFourInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveDihedralFourInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h15 i,ha i⟩
private theorem h17 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h16 i,ha i⟩
private theorem h18 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDoubleSymmetricFollowupInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveDoubleSymmetricFollowupInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveDoubleSymmetricFollowupInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h17 i,ha i⟩
private theorem h19 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveQuarterTurnTwoInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveQuarterTurnTwoInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveQuarterTurnTwoInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h18 i,ha i⟩
private theorem h20 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow163TwoAxisInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow163TwoAxisInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow163TwoAxisInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h19 i,ha i⟩
private theorem h21 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow202FullWreathInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow202FullWreathInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow202FullWreathInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h20 i,ha i⟩
private theorem h22 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow158SingleEvenInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow158SingleEvenInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow158SingleEvenInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h21 i,ha i⟩
private theorem h23 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow203FullWreathInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow203FullWreathInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow203FullWreathInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h22 i,ha i⟩
private theorem h24 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePureA4ThreeInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelvePureA4ThreeInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelvePureA4ThreeInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h23 i,ha i⟩
private theorem h25 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveThreeQuartetReuseInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveThreeQuartetReuseInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveThreeQuartetReuseInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h24 i,ha i⟩
private theorem h26 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h25 i,ha i⟩
private theorem h27 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow246SignedThirtyTwoInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow246SignedThirtyTwoInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow246SignedThirtyTwoInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h26 i,ha i⟩
private theorem h28 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow74FaithfulPrimitiveInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow74FaithfulPrimitiveInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow74FaithfulPrimitiveInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h27 i,ha i⟩
private theorem h29 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow295PrimitiveElevenInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow295PrimitiveElevenInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow295PrimitiveElevenInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h28 i,ha i⟩
private theorem h30 : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow59CutSpaceInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow59CutSpaceInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow59CutSpaceInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h29 i,ha i⟩
theorem not_mem_installed : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow181GraphInstalledJoint.installedIndices := by
  have ha : ∀ i : Fin 8,index i ∉ DegreeTwoTwelveRow181GraphInstalledJoint.additionalIndices := by decide +kernel
  intro i
  rw [DegreeTwoTwelveRow181GraphInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h30 i,ha i⟩

theorem not_mem_installed_of_mem (j : Fin 301) (hj : j∈candidates) :
    j∉DegreeTwoTwelveRow181GraphInstalledJoint.installedIndices := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact not_mem_installed i

theorem candidates_disjoint_installed :
    Disjoint candidates DegreeTwoTwelveRow181GraphInstalledJoint.installedIndices :=
  Finset.disjoint_left.mpr (fun j hj => not_mem_installed_of_mem j hj)

open DegreeTwoTwelvePairFiniteCatalogue

theorem candidates_card : candidates.card=8 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem index_branch : ∀ i : Fin 8,(catalogue.row (index i)).branch=.joint := by
  decide +kernel

theorem candidates_subset_remaining :
    candidates ⊆ DegreeTwoTwelveRow181GraphInstalledJoint.remainingIndices := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,not_mem_installed_of_mem j hj⟩
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact index_branch i

theorem remainingIndices_eq_candidates :
    DegreeTwoTwelveRow181GraphInstalledJoint.remainingIndices=candidates := by
  symm
  apply Finset.eq_of_subset_of_card_le candidates_subset_remaining
  simpa only [DegreeTwoTwelveRow181GraphInstalledJoint.remainingIndices_card,candidates_card]
    using (le_rfl : (8 : ℕ) ≤ 8)
end DegreeTwoTwelveRemainingEightExclusion
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
