import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleImage

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

abbrev UnitaryOddOutsidePoint (q : CFSG.PrimePower) (m : ℕ) :=
  {Q : UnitaryOddPoint q m // ¬Q.val ≤ unitaryOddHalf q m}

theorem exists_unique_unitaryOdd_outside_vector (q : CFSG.PrimePower) (m : ℕ)
    (Q : UnitaryOddOutsidePoint q m) :
    ∃! x : Fin (2*m+5) → q.Extension 2, x ∈ Q.val.val ∧ x (unitaryOddMiddleIndex m) = 1 := by
  classical
  obtain ⟨v,hv,hv0⟩ := singularPoint_nonzero (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) Q.val
  have hspan := singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) Q.val v hv hv0
  have hvW : v ∉ unitaryOddHalf q m := by
    intro h
    apply Q.property
    rw [hspan]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr h
  have hv2 := unitaryOdd_outside_middle_ne_zero q m v hvW
  refine ⟨(v (unitaryOddMiddleIndex m))⁻¹ • v, ⟨Q.val.val.smul_mem _ hv, ?_⟩, ?_⟩
  · change (v (unitaryOddMiddleIndex m))⁻¹ * v (unitaryOddMiddleIndex m) = 1
    exact inv_mul_cancel₀ hv2
  · intro x hx
    rw [hspan] at hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx.1
    have he : c * v (unitaryOddMiddleIndex m) = 1 := hx.2
    have hc : c = (v (unitaryOddMiddleIndex m))⁻¹ := mul_right_cancel₀ hv2 (he.trans (inv_mul_cancel₀ hv2).symm)
    rw [hc]

def unitaryOddOutsideVector (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    Fin (2*m+5) → q.Extension 2 := Classical.choose (exists_unique_unitaryOdd_outside_vector q m Q)

theorem unitaryOddOutsideVector_mem (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideVector q m Q ∈ Q.val.val :=
  (Classical.choose_spec (exists_unique_unitaryOdd_outside_vector q m Q)).1.1

theorem unitaryOddOutsideVector_middle (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideVector q m Q (unitaryOddMiddleIndex m) = 1 :=
  (Classical.choose_spec (exists_unique_unitaryOdd_outside_vector q m Q)).1.2

theorem unitaryOddOutsideVector_ne_zero (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideVector q m Q ≠ 0 := by
  intro h
  have hh := congrFun h (unitaryOddMiddleIndex m)
  change unitaryOddOutsideVector q m Q (unitaryOddMiddleIndex m) = 0 at hh
  rw [unitaryOddOutsideVector_middle] at hh
  exact (one_ne_zero : (1 : q.Extension 2) ≠ 0) hh

theorem unitaryOddOutsideVector_norm (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    unitaryNaturalPair q (2*m+4) (unitaryOddOutsideVector q m Q) (unitaryOddOutsideVector q m Q) = 0 :=
  Q.val.property.2 _ (unitaryOddOutsideVector_mem q m Q)

theorem unitaryOddOutsideVector_outside (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideVector q m Q ∉ unitaryOddHalf q m := by
  intro h
  have hh := unitaryOddHalf_middle_zero q m _ h
  rw [unitaryOddOutsideVector_middle] at hh
  exact (one_ne_zero : (1 : q.Extension 2) ≠ 0) hh

theorem unitaryOddOutsideVector_span (q : CFSG.PrimePower) (m : ℕ) (Q : UnitaryOddOutsidePoint q m) :
    Q.val.val = (q.Extension 2) ∙ unitaryOddOutsideVector q m Q :=
  singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) Q.val _
    (unitaryOddOutsideVector_mem q m Q) (unitaryOddOutsideVector_ne_zero q m Q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
