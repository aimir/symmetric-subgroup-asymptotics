import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleEdge

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryOdd_middle_coefficients_constant (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixW : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOddHalf q m → f Q = Q)
    (c : UnitaryOddOutsidePoint q m → q.Extension 2)
    (hc : ∀ R, unitaryOddProjection q m (unitaryOddOutsideVector q m R) +
      c R • unitaryOddMiddle q m ∈ (f R.val).val)
    (R S : UnitaryOddOutsidePoint q m) : c R = c S := by
  have hp := unitaryOdd_outside_point_connected q m R S
  apply Relation.ReflTransGen.trans_induction_on (motive := fun {A B} _ => c A = c B) hp
  · intro A
    rfl
  · intro A B hAB
    exact unitaryOdd_middle_coefficients_eq_on_edge q m f hlinear hfixW A B hAB (c A) (c B) (hc A) (hc B)
  · intro A B C hAB hBC ihAB ihBC
    exact ihAB.trans ihBC

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
