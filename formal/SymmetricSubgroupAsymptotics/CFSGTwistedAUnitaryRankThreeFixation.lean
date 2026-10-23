import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoEvenFixation
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfDecomposition

/-! The literal rank-three unitary point action is determined after
fixing its opposed coordinate planes and orthogonal mixed rays. This is
the four-dimensional gluing determination step, not an Out count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_rankThree_pointwiseFix_of_mixed (q : CFSG.PrimePower)
    (f : MulAut (CFSG.Models.TwistedA 3 q))
    (hfixP : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3),
      R.val ≤ unitaryStandardSingularSpace q 3 → (unitaryOrthogonalityActionHom q 0 f).val R = R)
    (hfixZ : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3),
      R.val ≤ unitaryOppositeSingularSpace q 3 → (unitaryOrthogonalityActionHom q 0 f).val R = R)
    (hfixMixed : ∀ (x y : Fin 4 → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q 3 → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q 3 → y ≠ 0 → unitaryNaturalPair q 3 y x = 0 →
      ∀ R : SingularPoint (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3),
        R.val = (q.Extension 2) ∙ (x + y) → (unitaryOrthogonalityActionHom q 0 f).val R = R) :
    ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3),
      (unitaryOrthogonalityActionHom q 0 f).val R = R := by
  apply hermitian_rankTwo_even_fixes_all (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3)
    (unitaryNaturalPair_zero_swap q 3)
    (unitaryOrthogonalityActionHom q 0 f).val (unitaryOrthogonalityActionHom q 0 f).property
    (unitaryStandardIsotropicSpace q 3) (unitaryOppositeIsotropicSpace q 3)
    _ _ (unitaryStandard_opposite_disjoint q 3)
    (unitaryStandard_opposite_sup_eq_top_of_odd q 3 (by decide))
    (unitaryStandard_pair_opposite_nondegenerate q 3)
    (unitaryOpposite_pair_standard_nondegenerate q 3) hfixP hfixZ hfixMixed
  · change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q 3) = 2
    rw [unitaryStandardSingularSpace_finrank]
  · change Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q 3) = 2
    rw [unitaryOppositeSingularSpace_finrank]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
