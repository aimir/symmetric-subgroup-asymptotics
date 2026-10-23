import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIndependentProjectionNeighbor
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourProjectionNorm
import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoMixedSpace
import SymmetricSubgroupAsymptotics.CFSGHermitianAnisotropicBypass

/-! The actual odd-five outside graph has no proportional-projection
obstruction. A nonzero vector in the original standard-plane kernel gives
an adjacent outside singular vector with independent half-projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem exists_unitaryRankFour_outside_bypass (q : CFSG.PrimePower)
    (R S : Fin 5 → q.Extension 2)
    (hR : unitaryNaturalPair q 4 R R = 0) (hS : unitaryNaturalPair q 4 S S = 0)
    (hRW : R ∉ unitaryRankFourHalf q) (hSW : S ∉ unitaryRankFourHalf q)
    (hdep : ¬LinearIndependent (q.Extension 2)
      ![unitaryRankFourProjection q R,unitaryRankFourProjection q S]) :
    ∃ T : Fin 5 → q.Extension 2, unitaryNaturalPair q 4 T T = 0 ∧
      T ∉ unitaryRankFourHalf q ∧ unitaryNaturalPair q 4 R T = 0 ∧
      LinearIndependent (q.Extension 2) ![unitaryRankFourProjection q T,unitaryRankFourProjection q S] := by
  classical
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q 4,
    fun x hx y hy => unitaryStandardSingularSpace_pair_zero q 4 x hx y hy⟩
  have hdP : 2 ≤ Module.finrank (q.Extension 2) P.val := by
    change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q 4)
    simpa only [unitaryStandardSingularSpace_finrank] using (show 2 ≤ (4 + 1) / 2 by decide)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (restrictedHermitianKernel_nonzero_of_two_le sig H P hdP R)
  have huP : u ∈ unitaryStandardSingularSpace q 4 := hu.1
  have huW : u ∈ unitaryRankFourHalf q := (show unitaryStandardSingularSpace q 4 ≤
    unitaryRankFourHalf q from le_sup_left) huP
  have hRu : unitaryNaturalPair q 4 R u = 0 := hu.2
  have huR : unitaryNaturalPair q 4 u R = 0 := (unitaryNaturalPair_zero_swap q 4 R u).mp hRu
  have hun : unitaryNaturalPair q 4 u u = 0 := unitaryStandardSingularSpace_pair_zero q 4 u huP u huP
  have hnR : hermitianPair sig H R R = 0 := hR
  have hnu : hermitianPair sig H u u = 0 := hun
  have hru : hermitianPair sig H R u = 0 := hRu
  have hTn : unitaryNaturalPair q 4 (R + u) (R + u) = 0 := by
    have hh := hermitian_orthogonal_sum_self sig H R u 1 hRu huR
    change hermitianPair sig H (R + u) (R + u) = 0
    simpa only [one_smul, hnR, hnu, mul_zero, zero_add] using hh
  have hTW : R + u ∉ unitaryRankFourHalf q := by
    intro h
    exact hRW (by simpa only [add_sub_cancel_right] using (unitaryRankFourHalf q).sub_mem h huW)
  have hRT : unitaryNaturalPair q 4 R (R + u) = 0 := by
    change hermitianPair sig H R (R + u) = 0
    rw [hermitianPair_add_right, hnR, hru, zero_add]
  have hpR := unitaryRankFourProjection_ne_zero q R hRW hR
  have hpS := unitaryRankFourProjection_ne_zero q S hSW hS
  have hprop : ∃ c : q.Extension 2, c • unitaryRankFourProjection q R = unitaryRankFourProjection q S := by
    by_contra h
    apply hdep
    apply (LinearIndependent.pair_iff' hpR).mpr
    intro c hc
    exact h ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hprop
  have hc0 : c ≠ 0 := by
    intro h
    exact hpS (by simpa only [h, zero_smul] using hc.symm)
  have hxu : LinearIndependent (q.Extension 2) ![unitaryRankFourProjection q R,u] :=
    hermitian_anisotropic_singular_independent sig H _ _
      (unitaryRankFourProjection_norm_ne_zero q R hRW hR) hu0 hun
  have hpT : unitaryRankFourProjection q (R + u) = unitaryRankFourProjection q R + u := by
    rw [map_add, unitaryRankFourProjection_eq_self_of_mem q u huW]
  refine ⟨R + u,hTn,hTW,hRT,?_⟩
  rw [hpT, ←hc]
  exact independent_add_proportional _ _ hxu c hc0

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
