import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddIndependentProjectionNeighbor
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddProjectionNorm
import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoMixedSpace
import SymmetricSubgroupAsymptotics.CFSGHermitianAnisotropicBypass

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem exists_unitaryOdd_outside_bypass (q : CFSG.PrimePower) (m : ℕ)
    (R S : Fin (2*m+5) → q.Extension 2)
    (hR : unitaryNaturalPair q (2*m+4) R R = 0) (hS : unitaryNaturalPair q (2*m+4) S S = 0)
    (hRW : R ∉ unitaryOddHalf q m) (hSW : S ∉ unitaryOddHalf q m)
    (hdep : ¬LinearIndependent (q.Extension 2)
      ![unitaryOddProjection q m R,unitaryOddProjection q m S]) :
    ∃ T : Fin (2*m+5) → q.Extension 2, unitaryNaturalPair q (2*m+4) T T = 0 ∧
      T ∉ unitaryOddHalf q m ∧ unitaryNaturalPair q (2*m+4) R T = 0 ∧
      LinearIndependent (q.Extension 2) ![unitaryOddProjection q m T,unitaryOddProjection q m S] := by
  classical
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q (2*m+4),
    fun x hx y hy => unitaryStandardSingularSpace_pair_zero q (2*m+4) x hx y hy⟩
  have hdP : 2 ≤ Module.finrank (q.Extension 2) P.val := by
    change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (2*m+4))
    simpa only [unitaryStandardSingularSpace_finrank] using (show 2 ≤ (2*m+4 + 1) / 2 by omega)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (restrictedHermitianKernel_nonzero_of_two_le sig H P hdP R)
  have huP : u ∈ unitaryStandardSingularSpace q (2*m+4) := hu.1
  have huW : u ∈ unitaryOddHalf q m := (show unitaryStandardSingularSpace q (2*m+4) ≤
    unitaryOddHalf q m from le_sup_left) huP
  have hRu : unitaryNaturalPair q (2*m+4) R u = 0 := hu.2
  have huR : unitaryNaturalPair q (2*m+4) u R = 0 := (unitaryNaturalPair_zero_swap q (2*m+4) R u).mp hRu
  have hun : unitaryNaturalPair q (2*m+4) u u = 0 := unitaryStandardSingularSpace_pair_zero q (2*m+4) u huP u huP
  have hnR : hermitianPair sig H R R = 0 := hR
  have hnu : hermitianPair sig H u u = 0 := hun
  have hru : hermitianPair sig H R u = 0 := hRu
  have hTn : unitaryNaturalPair q (2*m+4) (R + u) (R + u) = 0 := by
    have hh := hermitian_orthogonal_sum_self sig H R u 1 hRu huR
    change hermitianPair sig H (R + u) (R + u) = 0
    simpa only [one_smul, hnR, hnu, mul_zero, zero_add] using hh
  have hTW : R + u ∉ unitaryOddHalf q m := by
    intro h
    exact hRW (by simpa only [add_sub_cancel_right] using (unitaryOddHalf q m).sub_mem h huW)
  have hRT : unitaryNaturalPair q (2*m+4) R (R + u) = 0 := by
    change hermitianPair sig H R (R + u) = 0
    rw [hermitianPair_add_right, hnR, hru, zero_add]
  have hpR := unitaryOddProjection_ne_zero q m R hRW hR
  have hpS := unitaryOddProjection_ne_zero q m S hSW hS
  have hprop : ∃ c : q.Extension 2, c • unitaryOddProjection q m R = unitaryOddProjection q m S := by
    by_contra h
    apply hdep
    apply (LinearIndependent.pair_iff' hpR).mpr
    intro c hc
    exact h ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hprop
  have hc0 : c ≠ 0 := by
    intro h
    exact hpS (by simpa only [h, zero_smul] using hc.symm)
  have hxu : LinearIndependent (q.Extension 2) ![unitaryOddProjection q m R,u] :=
    hermitian_anisotropic_singular_independent sig H _ _
      (unitaryOddProjection_norm_ne_zero q m R hRW hR) hu0 hun
  have hpT : unitaryOddProjection q m (R + u) = unitaryOddProjection q m R + u := by
    rw [map_add, unitaryOddProjection_eq_self_of_mem q m u huW]
  refine ⟨R + u,hTn,hTW,hRT,?_⟩
  rw [hpT, ←hc]
  exact independent_add_proportional _ _ hxu c hc0

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
