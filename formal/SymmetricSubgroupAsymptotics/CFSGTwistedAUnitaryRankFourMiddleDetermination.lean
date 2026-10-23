import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCommonMiddleCoefficient
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourHalfFixation

/-! Complete odd-five point determination at the normalization stage.
The middle action is derived from original point incidence, local pieces,
and actual outside connectivity. It is realized by a constructed literal
norm-one middle isometry; no middle-action hypothesis occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryRankFour_point_action_middle_scale (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryRankFourPoint q))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryStandardSingularSpace q 4 → f Q = Q)
    (hfixZ : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryOppositeSingularSpace q 4 → f Q = Q)
    (hfixMixed : ∀ (u z : Fin 5 → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q 4 → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q 4 → z ≠ 0 →
      unitaryNaturalPair q 4 z u = 0 → ∀ Q : UnitaryRankFourPoint q,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (hfixW : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryRankFourHalf q → f Q = Q) :
    ∃ c : q.Extension 2, c ≠ 0 ∧ definingFieldAutomorphism q 2 c * c = 1 ∧
      ∀ Q : UnitaryRankFourPoint q,
        (f Q).val = Q.val.map (unitaryRankFourMiddleScale q c) := by
  obtain ⟨c,hc,hcn,hchart⟩ := exists_unitaryRankFour_common_middle_coefficient q f hf hlinear hfixP hfixZ hfixMixed hfixW
  refine ⟨c,hc,hcn,?_⟩
  intro Q
  by_cases hQ : Q.val ≤ unitaryRankFourHalf q
  · rw [hfixW Q hQ]
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,unitaryRankFourMiddleScale_fix_half q c x (hQ hx)⟩
    · rintro x ⟨y,hy,rfl⟩
      simpa only [unitaryRankFourMiddleScale_fix_half q c y (hQ hy)] using hy
  · let R : UnitaryRankFourOutsidePoint q := ⟨Q,hQ⟩
    let v := unitaryRankFourOutsideVector q R
    have hv2 : v 2 = 1 := unitaryRankFourOutsideVector_middle q R
    have hLv : unitaryRankFourMiddleScale q c v = unitaryRankFourProjection q v + c • unitaryRankFourMiddle q := by
      rw [unitaryRankFourMiddleScale_apply,hv2,one_smul]
    have hL0 : unitaryRankFourMiddleScale q c v ≠ 0 := by
      intro h
      have hh : unitaryRankFourMiddleScaleEquiv q c hc v = unitaryRankFourMiddleScaleEquiv q c hc 0 :=
        h.trans (map_zero (unitaryRankFourMiddleScaleEquiv q c hc)).symm
      exact unitaryRankFourOutsideVector_ne_zero q R ((unitaryRankFourMiddleScaleEquiv q c hc).injective hh)
    have hmem : unitaryRankFourMiddleScale q c v ∈ (f Q).val := by
      rw [hLv]
      exact hchart R
    have he := singularPoint_span (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) (f Q) _ hmem hL0
    calc
      (f Q).val = (q.Extension 2) ∙ unitaryRankFourMiddleScale q c v := he
      _ = Q.val.map (unitaryRankFourMiddleScale q c) := by
        have hspan : Q.val = (q.Extension 2) ∙ v := unitaryRankFourOutsideVector_span q R
        rw [hspan,Submodule.map_span,Set.image_singleton]

theorem unitary_rankFour_middle_determination_of_mixed (q : CFSG.PrimePower)
    (f : MulAut (CFSG.Models.TwistedA 4 q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (unitaryLocalSemilinearPiece q 1 f ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryStandardSingularSpace q 4 →
      (unitaryOrthogonalityActionHom q 1 f).val Q = Q)
    (hfixZ : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryOppositeSingularSpace q 4 →
      (unitaryOrthogonalityActionHom q 1 f).val Q = Q)
    (hfixMixed : ∀ (u z : Fin 5 → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q 4 → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q 4 → z ≠ 0 →
      unitaryNaturalPair q 4 z u = 0 → ∀ Q : UnitaryRankFourPoint q,
      Q.val = (q.Extension 2) ∙ (u + z) → (unitaryOrthogonalityActionHom q 1 f).val Q = Q) :
    ∃ c : q.Extension 2, c ≠ 0 ∧ definingFieldAutomorphism q 2 c * c = 1 ∧
      ∀ Q : UnitaryRankFourPoint q,
        ((unitaryOrthogonalityActionHom q 1 f).val Q).val = Q.val.map (unitaryRankFourMiddleScale q c) := by
  apply unitaryRankFour_point_action_middle_scale q (unitaryOrthogonalityActionHom q 1 f).val
    (unitaryOrthogonalityActionHom q 1 f).property hlinear hfixP hfixZ hfixMixed
  exact unitary_rankFour_halfSum_pointwiseFix_of_mixed q f hlinear hfixP hfixZ hfixMixed

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
