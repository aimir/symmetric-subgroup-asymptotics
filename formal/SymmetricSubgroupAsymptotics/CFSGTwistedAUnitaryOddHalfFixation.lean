import SymmetricSubgroupAsymptotics.CFSGHermitianSingularSectionFixation
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedPencil
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointCommonRatio

/-! Actual odd-dimensional unitary half-sum determination in EVERY
rank at least three. A constructed finite-field trace pencil and
rank-free mixed test discharge every singular-section hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_odd_half_pointwise_fix_of_mixed (q : CFSG.PrimePower) (s : ℕ)
    (hr : Even (s+3)) (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) → f R=R)
    (hfixZ : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) → f R=R)
    (hfixMixed : ∀ (x y : Fin (s+4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 → unitaryNaturalPair q (s+3) y x=0 →
      ∀ R : UnitaryPoint q (s+3), R.val=(q.Extension 2) ∙ (x+y) → f R=R) :
    ∀ R : UnitaryPoint q (s+3),
      R.val ≤ unitaryStandardSingularSpace q (s+3) ⊔ unitaryOppositeSingularSpace q (s+3) → f R=R := by
  apply hermitian_fixes_singular_section (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))
    (unitaryStandardSingularSpace q (s+3)) (unitaryOppositeSingularSpace q (s+3))
    (unitaryStandardSingularSpace_pair_zero q (s+3))
    (fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q (s+3) x y hx hy) ?_
    (unitaryStandard_opposite_disjoint q (s+3))
    (unitaryStandard_pair_opposite_nondegenerate q (s+3))
    (unitaryNaturalPair_zero_swap q (s+3)) f hlinear hfixP hfixZ hfixMixed
    (exists_unitary_two_mixed_pencil_parameters q (s+3) hr)
  rw [unitaryStandardSingularSpace_finrank]
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
