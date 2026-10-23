import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedTracePencil
import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoSingularSection

/-! The actual rank-four five-space discharges the generic signed-trace
pencil and singular-section theorem. The middle action stays separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters

theorem unitary_rankFour_halfSum_pointwiseFix_of_mixed (q : CFSG.PrimePower)
    (f : MulAut (CFSG.Models.TwistedA 4 q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (unitaryLocalSemilinearPiece q 1 f ⟨M.val, M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      R.val ≤ unitaryStandardSingularSpace q 4 → (unitaryOrthogonalityActionHom q 1 f).val R = R)
    (hfixZ : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      R.val ≤ unitaryOppositeSingularSpace q 4 → (unitaryOrthogonalityActionHom q 1 f).val R = R)
    (hfixMixed : ∀ (x y : Fin 5 → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q 4 → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q 4 → y ≠ 0 → unitaryNaturalPair q 4 y x = 0 →
      ∀ R : SingularPoint (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
        R.val = (q.Extension 2) ∙ (x + y) → (unitaryOrthogonalityActionHom q 1 f).val R = R) :
    ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      R.val ≤ unitaryStandardSingularSpace q 4 ⊔ unitaryOppositeSingularSpace q 4 →
      (unitaryOrthogonalityActionHom q 1 f).val R = R := by
  apply hermitian_rankTwo_fixes_singular_section (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)
    (unitaryStandardSingularSpace q 4) (unitaryOppositeSingularSpace q 4)
    (unitaryStandardSingularSpace_pair_zero q 4)
    (fun a ha b hb => unitaryOppositeSingularSpace_pair_zero q 4 a b ha hb)
    (unitaryStandardSingularSpace_finrank q 4) (unitaryOppositeSingularSpace_finrank q 4)
    (unitaryStandard_opposite_disjoint q 4)
    (unitaryOpposite_pair_standard_nondegenerate q 4) (unitaryNaturalPair_zero_swap q 4)
    (unitaryOrthogonalityActionHom q 1 f).val hlinear hfixP hfixZ hfixMixed
  exact exists_unitaryRankFour_two_mixed_pencil_parameters q

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
