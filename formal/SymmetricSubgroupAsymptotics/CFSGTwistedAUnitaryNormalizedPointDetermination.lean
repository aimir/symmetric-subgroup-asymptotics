import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMixedNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourMiddleDetermination
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankThreeFixation

/-! The checked original even/odd determination arguments apply to the
literal normalized point permutation, without asserting that it comes
from a normalized original-group automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_rankThree_normalized_point_fix (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryPoint q 3))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3) f)
    (hfixP : ∀ R : UnitaryPoint q 3, R.val ≤ unitaryStandardSingularSpace q 3 → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q 3, R.val ≤ unitaryOppositeSingularSpace q 3 → f R = R)
    (hfixMixed : ∀ (x y : Fin 4 → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q 3 → x ≠ 0 → y ∈ unitaryOppositeSingularSpace q 3 → y ≠ 0 →
      unitaryNaturalPair q 3 y x = 0 → ∀ R : UnitaryPoint q 3,
      R.val = (q.Extension 2) ∙ (x+y) → f R = R) : ∀ R : UnitaryPoint q 3, f R = R := by
  apply hermitian_rankTwo_even_fixes_all (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 3 : Mat (q.Extension 2) 3)
    (unitaryNaturalPair_zero_swap q 3) f hf (unitaryStandardIsotropicSpace q 3) (unitaryOppositeIsotropicSpace q 3)
    _ _ (unitaryStandard_opposite_disjoint q 3)
    (unitaryStandard_opposite_sup_eq_top_of_odd q 3 (by decide))
    (unitaryStandard_pair_opposite_nondegenerate q 3) (unitaryOpposite_pair_standard_nondegenerate q 3)
    hfixP hfixZ hfixMixed
  · change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q 3) = 2
    rw [unitaryStandardSingularSpace_finrank]
  · change Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q 3) = 2
    rw [unitaryOppositeSingularSpace_finrank]

theorem unitary_rankFour_normalized_point_middle (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryPoint q 4))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : UnitaryPoint q 4, R.val ≤ unitaryStandardSingularSpace q 4 → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q 4, R.val ≤ unitaryOppositeSingularSpace q 4 → f R = R)
    (hfixMixed : ∀ (x y : Fin 5 → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q 4 → x ≠ 0 → y ∈ unitaryOppositeSingularSpace q 4 → y ≠ 0 →
      unitaryNaturalPair q 4 y x = 0 → ∀ R : UnitaryPoint q 4,
      R.val = (q.Extension 2) ∙ (x+y) → f R = R) :
    ∃ c : q.Extension 2, c ≠ 0 ∧ definingFieldAutomorphism q 2 c * c = 1 ∧
      ∀ R : UnitaryPoint q 4, (f R).val = R.val.map (unitaryRankFourMiddleScale q c) := by
  apply unitaryRankFour_point_action_middle_scale q f hf hlinear hfixP hfixZ hfixMixed
  apply hermitian_rankTwo_fixes_singular_section (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)
    (unitaryStandardSingularSpace q 4) (unitaryOppositeSingularSpace q 4)
    (unitaryStandardSingularSpace_pair_zero q 4)
    (fun a ha b hb => unitaryOppositeSingularSpace_pair_zero q 4 a b ha hb)
    (unitaryStandardSingularSpace_finrank q 4) (unitaryOppositeSingularSpace_finrank q 4)
    (unitaryStandard_opposite_disjoint q 4) (unitaryOpposite_pair_standard_nondegenerate q 4)
    (unitaryNaturalPair_zero_swap q 4) f hlinear hfixP hfixZ hfixMixed
  exact exists_unitaryRankFour_two_mixed_pencil_parameters q

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
