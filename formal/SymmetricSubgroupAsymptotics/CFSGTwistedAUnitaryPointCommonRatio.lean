import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPointRatioFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowRankPointFixedRatio
import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedScalarCoherence

/-! A single fixed-field mixed ratio works on the opposed halves in
EVERY original unitary rank at least three. The genuine rank-two and
higher-rank ratio engines are both discharged on the literal form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitary_point_opposed_common_fixed_ratio (q : CFSG.PrimePower) (s : ℕ)
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
  by_cases hs : s ≤ 1
  · exact unitary_lowRank_point_opposed_common_fixed_ratio q s hs f hf hlinear hfixP hfixZ
  · let sig := definingFieldAutomorphism q 2
    let H : Mat (q.Extension 2) (s+3) := signedReversalUnit (q.Extension 2) (s+3)
    let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q (s+3),
      fun x hx y hy => unitaryStandardSingularSpace_pair_zero q (s+3) x hx y hy⟩
    let Z : IsotropicSpace sig H := ⟨unitaryOppositeSingularSpace q (s+3),
      fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q (s+3) x y hx hy⟩
    have hdP : 3 ≤ Module.finrank (q.Extension 2) P.val := by
      change 3 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (s+3))
      rw [unitaryStandardSingularSpace_finrank]
      omega
    have hdZ : 3 ≤ Module.finrank (q.Extension 2) Z.val := by
      change 3 ≤ Module.finrank (q.Extension 2) (unitaryOppositeSingularSpace q (s+3))
      rw [unitaryOppositeSingularSpace_finrank]
      omega
    obtain ⟨t,ht,hratio⟩ := hermitian_opposed_common_ratio sig H
      (unitaryNaturalPair_zero_swap q (s+3)) f P Z hdP hdZ
      (unitaryStandard_opposite_disjoint q (s+3)) hlinear hfixP hfixZ
    exact ⟨t,ht,unitary_point_common_ratio_fixed q s f hf t hratio,hratio⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
