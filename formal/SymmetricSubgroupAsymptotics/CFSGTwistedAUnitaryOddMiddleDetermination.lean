import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddCommonMiddleCoefficient
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddHalfFixation

/-! In every odd vector dimension at least five, original point incidence determines a single norm-one middle scale. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

theorem unitaryOdd_point_action_middle_scale (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f)
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixP : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryStandardSingularSpace q (2*m+4) → f Q = Q)
    (hfixZ : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOppositeSingularSpace q (2*m+4) → f Q = Q)
    (hfixMixed : ∀ (u z : Fin (2*m+5) → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q (2*m+4) → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q (2*m+4) → z ≠ 0 →
      unitaryNaturalPair q (2*m+4) z u = 0 → ∀ Q : UnitaryOddPoint q m,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (hfixW : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOddHalf q m → f Q = Q) :
    ∃ c : q.Extension 2, c ≠ 0 ∧ definingFieldAutomorphism q 2 c * c = 1 ∧
      ∀ Q : UnitaryOddPoint q m,
        (f Q).val = Q.val.map (unitaryOddMiddleScale q m c) := by
  obtain ⟨c,hc,hcn,hchart⟩ := exists_unitaryOdd_common_middle_coefficient q m f hf hlinear hfixP hfixZ hfixMixed hfixW
  refine ⟨c,hc,hcn,?_⟩
  intro Q
  by_cases hQ : Q.val ≤ unitaryOddHalf q m
  · rw [hfixW Q hQ]
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,unitaryOddMiddleScale_fix_half q m c x (hQ hx)⟩
    · rintro x ⟨y,hy,rfl⟩
      simpa only [unitaryOddMiddleScale_fix_half q m c y (hQ hy)] using hy
  · let R : UnitaryOddOutsidePoint q m := ⟨Q,hQ⟩
    let v := unitaryOddOutsideVector q m R
    have hv2 : v (unitaryOddMiddleIndex m) = 1 := unitaryOddOutsideVector_middle q m R
    have hLv : unitaryOddMiddleScale q m c v = unitaryOddProjection q m v + c • unitaryOddMiddle q m := by
      rw [unitaryOddMiddleScale_apply,hv2,one_smul]
    have hL0 : unitaryOddMiddleScale q m c v ≠ 0 := by
      intro h
      have hh : unitaryOddMiddleScaleEquiv q m c hc v = unitaryOddMiddleScaleEquiv q m c hc 0 :=
        h.trans (map_zero (unitaryOddMiddleScaleEquiv q m c hc)).symm
      exact unitaryOddOutsideVector_ne_zero q m R ((unitaryOddMiddleScaleEquiv q m c hc).injective hh)
    have hmem : unitaryOddMiddleScale q m c v ∈ (f Q).val := by
      rw [hLv]
      exact hchart R
    have he := singularPoint_span (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) (f Q) _ hmem hL0
    calc
      (f Q).val = (q.Extension 2) ∙ unitaryOddMiddleScale q m c v := he
      _ = Q.val.map (unitaryOddMiddleScale q m c) := by
        have hspan : Q.val = (q.Extension 2) ∙ v := unitaryOddOutsideVector_span q m R
        rw [hspan,Submodule.map_span,Set.image_singleton]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
