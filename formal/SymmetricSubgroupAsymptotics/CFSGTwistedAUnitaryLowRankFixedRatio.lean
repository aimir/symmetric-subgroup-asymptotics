import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankOpposedRatio
import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedRatioFixed

/-! The common mixed ratio of the SAME original rank3/4 unitary action
lies in the actual involution-fixed field. This is proved from original
orthogonality, not supplied as a scalar or norm hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_lowRank_opposed_common_fixed_ratio (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s+3) q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      Nonempty (unitaryLocalSemilinearPiece q s f ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      R.val ≤ unitaryStandardSingularSpace q (s+3) → (unitaryOrthogonalityActionHom q s f).val R = R)
    (hfixZ : ∀ R : SingularPoint (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)),
      R.val ≤ unitaryOppositeSingularSpace q (s+3) → (unitaryOrthogonalityActionHom q s f).val R = R) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ definingFieldAutomorphism q 2 t = t ∧
      ∀ (x y : Fin (s+4) → q.Extension 2),
      x ∈ unitaryStandardSingularSpace q (s+3) → x ≠ 0 →
      y ∈ unitaryOppositeSingularSpace q (s+3) → y ≠ 0 → unitaryNaturalPair q (s+3) y x = 0 →
      ∀ (hxy0 : x+y ≠ 0) (hn : unitaryNaturalPair q (s+3) (x+y) (x+y) = 0),
      ((unitaryOrthogonalityActionHom q s f).val
        (singularRay (definingFieldAutomorphism q 2)
          (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) (x+y) hxy0 hn)).val =
        (q.Extension 2) ∙ (x+t • y) := by
  obtain ⟨t,ht,hratio⟩ := unitary_lowRank_opposed_common_ratio q s hs f hlinear hfixP hfixZ
  refine ⟨t,ht,?_,hratio⟩
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
  apply hermitian_opposed_common_ratio_fixed sig H ((-1 : q.Extension 2)^(s+3))
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (unitaryNaturalPair_signed_reciprocal q (s+3))
    (unitaryNaturalPair_zero_swap q (s+3)) P Z hdP hdZ (unitaryStandard_opposite_disjoint q (s+3))
    (unitaryStandard_pair_opposite_nondegenerate q (s+3))
    (fun x hx h => unitaryStandard_pair_opposite_nondegenerate q (s+3) x hx
      (fun y hy => (unitaryNaturalPair_zero_swap q (s+3) y x).mp (h y hy)))
    (unitaryOrthogonalityActionHom q s f).val (unitaryOrthogonalityActionHom q s f).property t
  exact hratio

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
