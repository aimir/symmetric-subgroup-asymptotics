import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCommonNeighborOutsideGeneral
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddProjection

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryOddMiddle_not_mem_pair_span (q : CFSG.PrimePower) (m : ℕ)
    (R S : Fin (2*m+5) → q.Extension 2)
    (hproj : LinearIndependent (q.Extension 2)
      ![unitaryOddProjection q m R, unitaryOddProjection q m S]) :
    unitaryOddMiddle q m ∉ ((q.Extension 2) ∙ R) ⊔ (q.Extension 2) ∙ S := by
  intro hm
  obtain ⟨r, hr, s, hs, he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hr
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hh := congrArg (unitaryOddProjection q m) he
  change unitaryOddProjection q m (a • R + b • S) =
    unitaryOddProjection q m (unitaryOddMiddle q m) at hh
  rw [map_add, map_smul, map_smul, unitaryOddProjection_middle] at hh
  obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hproj a b hh
  simp only [ha, hb, zero_smul, zero_add] at he
  exact unitaryOddMiddle_ne_zero q m he.symm

theorem exists_unitary_odd_independent_projection_common_neighbor (q : CFSG.PrimePower) (m : ℕ)
    (R S : Fin (2*m+5) → q.Extension 2)
    (hR : unitaryNaturalPair q (2*m+4) R R = 0) (hSR : unitaryNaturalPair q (2*m+4) S R ≠ 0)
    (hproj : LinearIndependent (q.Extension 2)
      ![unitaryOddProjection q m R, unitaryOddProjection q m S]) :
    ∃ v : Fin (2*m+5) → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q (2*m+4) v v = 0 ∧
      v ∉ unitaryOddHalf q m ∧ unitaryNaturalPair q (2*m+4) R v = 0 ∧ unitaryNaturalPair q (2*m+4) S v = 0 := by
  have hR0 : R ≠ 0 := by
    intro h
    have hp : unitaryOddProjection q m R ≠ 0 := hproj.ne_zero 0
    exact hp (by rw [h, map_zero])
  apply exists_unitary_common_neighbor_outside_general q (2*m) R S hR0 hR hSR (unitaryOddHalf q m)
  intro hle
  exact unitaryOddMiddle_not_mem_pair_span q m R S hproj (hle (unitaryOddMiddle_perp_half q m))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
