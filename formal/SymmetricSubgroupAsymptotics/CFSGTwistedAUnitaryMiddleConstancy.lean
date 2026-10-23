import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleEdge

/-! The actual outside-point graph is connected, so its uniquely
normalized image middle coefficient is constant. Connectivity is the
checked original geometric theorem, not an additional input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryRankFour_middle_coefficients_constant (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryRankFourPoint q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixW : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryRankFourHalf q → f Q = Q)
    (c : UnitaryRankFourOutsidePoint q → q.Extension 2)
    (hc : ∀ R, unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) +
      c R • unitaryRankFourMiddle q ∈ (f R.val).val)
    (R S : UnitaryRankFourOutsidePoint q) : c R = c S := by
  have hp := unitaryRankFour_outside_point_connected q R S
  apply Relation.ReflTransGen.trans_induction_on (motive := fun {A B} _ => c A = c B) hp
  · intro A
    rfl
  · intro A B hAB
    exact unitaryRankFour_middle_coefficients_eq_on_edge q f hlinear hfixW A B hAB (c A) (c B) (hc A) (hc B)
  · intro A B C hAB hBC ihAB ihBC
    exact ihAB.trans ihBC

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
