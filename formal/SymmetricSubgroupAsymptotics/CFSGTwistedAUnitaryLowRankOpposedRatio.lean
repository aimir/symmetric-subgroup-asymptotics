import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoOpposedRatio
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity

/-! The opposed-plane scalar comparison on the SAME original unitary
point action in ranks three and four. All signed form, nondegeneracy,
dimension, and disjointness inputs are discharged by actual coordinate
spaces. Fixation and linearity are the explicit normalization conditions
for the separate ambient gluing step, not a claimed final Out theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_lowRank_opposed_common_ratio (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      Nonempty (unitaryLocalSemilinearPiece q s f ⟨M.val, M.property.1⟩
        (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      R.val ≤ unitaryStandardSingularSpace q (s + 3) →
      (unitaryOrthogonalityActionHom q s f).val R = R)
    (hfixZ : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)),
      R.val ≤ unitaryOppositeSingularSpace q (s + 3) →
      (unitaryOrthogonalityActionHom q s f).val R = R) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ ∀ (x y : Fin (s + 4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s + 3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s + 3) → y ≠ 0 →
      unitaryNaturalPair q (s + 3) y x = 0 → ∀ (hxy0 : x + y ≠ 0)
        (hz : unitaryNaturalPair q (s + 3) (x + y) (x + y) = 0),
      ((unitaryOrthogonalityActionHom q s f).val
        (singularRay (definingFieldAutomorphism q 2)
          (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
          (x + y) hxy0 hz)).val = (q.Extension 2) ∙ (x + t • y) := by
  apply hermitian_rankTwo_opposed_common_ratio (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    ((-1 : q.Extension 2)^(s + 3)) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (unitaryNaturalPair_signed_reciprocal q (s + 3)) (unitaryNaturalPair_zero_swap q (s + 3))
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property
    (unitaryStandardIsotropicSpace q (s + 3)) (unitaryOppositeIsotropicSpace q (s + 3))
    _ _ (unitaryStandard_opposite_disjoint q (s + 3))
    (unitaryStandard_pair_opposite_nondegenerate q (s + 3))
    (unitaryOpposite_pair_standard_nondegenerate q (s + 3)) hlinear hfixP hfixZ
  · change Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s + 3)) = 2
    rw [unitaryStandardSingularSpace_finrank]
    omega
  · change Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q (s + 3)) = 2
    rw [unitaryOppositeSingularSpace_finrank]
    omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
