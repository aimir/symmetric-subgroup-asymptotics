import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankFixedRatio

/-! The checked original geometric ratio proof also applies to a literal
point permutation after constructed field/similitude normalization. No
normalized permutation is asserted to be an original group automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

abbrev UnitaryPoint (q : CFSG.PrimePower) (r : ℕ) :=
  SingularPoint (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)

theorem unitary_lowRank_point_opposed_common_fixed_ratio (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : Equiv.Perm (UnitaryPoint q (s+3)))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryStandardSingularSpace q (s+3) → f R = R)
    (hfixZ : ∀ R : UnitaryPoint q (s+3), R.val ≤ unitaryOppositeSingularSpace q (s+3) → f R = R) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ definingFieldAutomorphism q 2 t = t ∧
      ∀ (x y : Fin (s+4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 → unitaryNaturalPair q (s+3) y x = 0 →
      ∀ (hxy0 : x+y ≠ 0) (hn : unitaryNaturalPair q (s+3) (x+y) (x+y) = 0),
      (f (singularRay (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) (x+y) hxy0 hn)).val =
        (q.Extension 2) ∙ (x+t • y) := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (s+3) := signedReversalUnit (q.Extension 2) (s+3)
  let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q (s+3),
    fun x hx y hy => unitaryStandardSingularSpace_pair_zero q (s+3) x hx y hy⟩
  let Z : IsotropicSpace sig H := ⟨unitaryOppositeSingularSpace q (s+3),
    fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q (s+3) x y hx hy⟩
  have hdP : Module.finrank (q.Extension 2) P.val = 2 := by
    change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s+3)) = 2
    simpa only [unitaryStandardSingularSpace_finrank] using (show (s+3+1)/2 = 2 by omega)
  have hdZ : Module.finrank (q.Extension 2) Z.val = 2 := by
    change Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q (s+3)) = 2
    simpa only [unitaryOppositeSingularSpace_finrank] using (show (s+3+1)/2 = 2 by omega)
  have heps : (-1 : q.Extension 2)^(s+3) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨t,ht,hratio⟩ := hermitian_rankTwo_opposed_common_ratio sig H
    ((-1 : q.Extension 2)^(s+3)) heps (unitaryNaturalPair_signed_reciprocal q (s+3))
    (unitaryNaturalPair_zero_swap q (s+3)) f hf P Z hdP hdZ (unitaryStandard_opposite_disjoint q (s+3))
    (unitaryStandard_pair_opposite_nondegenerate q (s+3)) (unitaryOpposite_pair_standard_nondegenerate q (s+3))
    hlinear hfixP hfixZ
  refine ⟨t,ht,?_,hratio⟩
  exact hermitian_opposed_common_ratio_fixed sig H ((-1 : q.Extension 2)^(s+3)) heps
    (unitaryNaturalPair_signed_reciprocal q (s+3)) (unitaryNaturalPair_zero_swap q (s+3)) P Z hdP hdZ
    (unitaryStandard_opposite_disjoint q (s+3)) (unitaryStandard_pair_opposite_nondegenerate q (s+3))
    (fun x hx h => unitaryStandard_pair_opposite_nondegenerate q (s+3) x hx
      (fun y hy => (unitaryNaturalPair_zero_swap q (s+3) y x).mp (h y hy))) f hf t hratio

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
