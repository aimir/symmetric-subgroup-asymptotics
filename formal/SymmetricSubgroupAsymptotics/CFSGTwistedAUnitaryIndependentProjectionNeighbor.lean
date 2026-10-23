import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCommonNeighborOutside
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourProjection

/-! Independent actual half-projections exclude the middle-vector
obstruction, yielding a literal singular common neighbor outside W. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryRankFourMiddle_not_mem_pair_span (q : CFSG.PrimePower)
    (R S : Fin 5 → q.Extension 2)
    (hproj : LinearIndependent (q.Extension 2)
      ![unitaryRankFourProjection q R, unitaryRankFourProjection q S]) :
    unitaryRankFourMiddle q ∉ ((q.Extension 2) ∙ R) ⊔ (q.Extension 2) ∙ S := by
  intro hm
  obtain ⟨r, hr, s, hs, he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hr
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hh := congrArg (unitaryRankFourProjection q) he
  change unitaryRankFourProjection q (a • R + b • S) =
    unitaryRankFourProjection q (unitaryRankFourMiddle q) at hh
  rw [map_add, map_smul, map_smul, unitaryRankFourProjection_middle] at hh
  obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hproj a b hh
  simp only [ha, hb, zero_smul, zero_add] at he
  exact unitaryRankFourMiddle_ne_zero q he.symm

theorem exists_unitary_independent_projection_common_neighbor (q : CFSG.PrimePower)
    (R S : Fin 5 → q.Extension 2)
    (hR : unitaryNaturalPair q 4 R R = 0) (hSR : unitaryNaturalPair q 4 S R ≠ 0)
    (hproj : LinearIndependent (q.Extension 2)
      ![unitaryRankFourProjection q R, unitaryRankFourProjection q S]) :
    ∃ v : Fin 5 → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q 4 v v = 0 ∧
      v ∉ unitaryRankFourHalf q ∧ unitaryNaturalPair q 4 R v = 0 ∧ unitaryNaturalPair q 4 S v = 0 := by
  have hR0 : R ≠ 0 := by
    intro h
    have hp : unitaryRankFourProjection q R ≠ 0 := hproj.ne_zero 0
    exact hp (by rw [h, map_zero])
  apply exists_unitary_common_neighbor_outside q R S hR0 hR hSR (unitaryRankFourHalf q)
  intro hle
  exact unitaryRankFourMiddle_not_mem_pair_span q R S hproj (hle (unitaryRankFourMiddle_perp_half q))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
