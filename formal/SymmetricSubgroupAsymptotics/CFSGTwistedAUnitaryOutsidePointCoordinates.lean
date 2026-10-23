import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleImage

/-! Each literal singular point outside the half-sum has a unique vector
with middle coordinate one. This fixes the projective scaling without
assuming a linear action on the ambient five-space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

abbrev UnitaryRankFourOutsidePoint (q : CFSG.PrimePower) :=
  {Q : UnitaryRankFourPoint q // ¬Q.val ≤ unitaryRankFourHalf q}

theorem exists_unique_unitaryRankFour_outside_vector (q : CFSG.PrimePower)
    (Q : UnitaryRankFourOutsidePoint q) :
    ∃! x : Fin 5 → q.Extension 2, x ∈ Q.val.val ∧ x 2 = 1 := by
  classical
  obtain ⟨v,hv,hv0⟩ := singularPoint_nonzero (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) Q.val
  have hspan := singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) Q.val v hv hv0
  have hvW : v ∉ unitaryRankFourHalf q := by
    intro h
    apply Q.property
    rw [hspan]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr h
  have hv2 := unitaryRankFour_outside_middle_ne_zero q v hvW
  refine ⟨(v 2)⁻¹ • v, ⟨Q.val.val.smul_mem _ hv, ?_⟩, ?_⟩
  · change (v 2)⁻¹ * v 2 = 1
    exact inv_mul_cancel₀ hv2
  · intro x hx
    rw [hspan] at hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx.1
    have he : c * v 2 = 1 := hx.2
    have hc : c = (v 2)⁻¹ := mul_right_cancel₀ hv2 (he.trans (inv_mul_cancel₀ hv2).symm)
    rw [hc]

def unitaryRankFourOutsideVector (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    Fin 5 → q.Extension 2 := Classical.choose (exists_unique_unitaryRankFour_outside_vector q Q)

theorem unitaryRankFourOutsideVector_mem (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideVector q Q ∈ Q.val.val :=
  (Classical.choose_spec (exists_unique_unitaryRankFour_outside_vector q Q)).1.1

theorem unitaryRankFourOutsideVector_middle (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideVector q Q 2 = 1 :=
  (Classical.choose_spec (exists_unique_unitaryRankFour_outside_vector q Q)).1.2

theorem unitaryRankFourOutsideVector_ne_zero (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideVector q Q ≠ 0 := by
  intro h
  have hh := congrFun h (2 : Fin 5)
  change unitaryRankFourOutsideVector q Q 2 = 0 at hh
  rw [unitaryRankFourOutsideVector_middle] at hh
  exact (one_ne_zero : (1 : q.Extension 2) ≠ 0) hh

theorem unitaryRankFourOutsideVector_norm (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    unitaryNaturalPair q 4 (unitaryRankFourOutsideVector q Q) (unitaryRankFourOutsideVector q Q) = 0 :=
  Q.val.property.2 _ (unitaryRankFourOutsideVector_mem q Q)

theorem unitaryRankFourOutsideVector_outside (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideVector q Q ∉ unitaryRankFourHalf q := by
  intro h
  have hh := unitaryRankFourHalf_middle_zero q _ h
  rw [unitaryRankFourOutsideVector_middle] at hh
  exact (one_ne_zero : (1 : q.Extension 2) ≠ 0) hh

theorem unitaryRankFourOutsideVector_span (q : CFSG.PrimePower) (Q : UnitaryRankFourOutsidePoint q) :
    Q.val.val = (q.Extension 2) ∙ unitaryRankFourOutsideVector q Q :=
  singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) Q.val _
    (unitaryRankFourOutsideVector_mem q Q) (unitaryRankFourOutsideVector_ne_zero q Q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
