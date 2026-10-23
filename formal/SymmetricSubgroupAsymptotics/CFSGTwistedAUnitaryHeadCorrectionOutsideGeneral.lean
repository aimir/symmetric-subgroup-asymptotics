import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeadCorrectionGeneral
import SymmetricSubgroupAsymptotics.CFSGFiniteHermitianPerpLattice

/-! The actual joint-perpendicular correction is not trapped in a
subspace W unless W's perpendicular lies in the original two-point span.
This discharges range noncontainment by literal Hermitian duality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

private theorem pairKernel_eq_perp_span {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K) (e : I → K) :
    (pairRightLinear sigma H e).ker = rightPerp sigma H (K ∙ e) := by
  apply le_antisymm
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hx0 : hermitianPair sigma H e x = 0 := hx
    have hh := hermitianPair_smul sigma H a 1 e x
    simpa only [one_smul, mul_one, hx0, mul_zero] using hh
  · intro x hx
    exact hx e (Submodule.mem_span_singleton_self e)

theorem exists_unitary_head_common_neighbor_outside_general (q : CFSG.PrimePower) (n : ℕ)
    (w : Fin (n+5) → q.Extension 2)
    (hw : unitaryNaturalPair q (n+4) w (Pi.single (0 : Fin (n+5)) 1) ≠ 0)
    (W : Submodule (q.Extension 2) (Fin (n+5) → q.Extension 2))
    (hnot : ¬ rightPerp (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (n+4) : Mat (q.Extension 2) (n+4)) W ≤
        ((q.Extension 2) ∙ (Pi.single (0 : Fin (n+5)) 1)) ⊔ (q.Extension 2) ∙ w) :
    ∃ v : Fin (n+5) → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q (n+4) v v = 0 ∧ v ∉ W ∧
      unitaryNaturalPair q (n+4) (Pi.single (0 : Fin (n+5)) 1) v = 0 ∧ unitaryNaturalPair q (n+4) w v = 0 := by
  apply exists_unitaryHeadCorrectionGeneral_singular_outside q n w hw W
  intro hle
  apply hnot
  rw [unitaryHeadCorrectionGeneral_range q n w hw,
    pairKernel_eq_perp_span, pairKernel_eq_perp_span] at hle
  exact CFSGFiniteHermitianPerpLattice.perp_intersection_le_implies_perp_le_sup
    (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) (n+4))
    (unitaryNaturalPair_zero_swap q (n+4)) _ _ W hle

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
