import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleConstancy
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleScale

/-! The coefficient is chosen from actual image-ray membership, made
constant by the proved original outside graph, and shown norm-one from
actual singularity. There is no supplied middle action or graph premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitaryRankFour_middle_chart_norm_one (q : CFSG.PrimePower)
    (R : UnitaryRankFourOutsidePoint q) (Q : UnitaryRankFourPoint q) (c : q.Extension 2)
    (hc : unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) +
      c • unitaryRankFourMiddle q ∈ Q.val) : definingFieldAutomorphism q 2 c * c = 1 := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let p := unitaryRankFourProjection q (unitaryRankFourOutsideVector q R)
  have hp : hermitianPair sig H p p = -1 := by
    have hh := unitaryRankFourProjection_norm q (unitaryRankFourOutsideVector q R)
    simpa only [unitaryRankFourOutsideVector_norm,unitaryRankFourOutsideVector_middle,
      map_one,mul_one,zero_sub] using hh
  have hn : hermitianPair sig H (p + c • unitaryRankFourMiddle q) (p + c • unitaryRankFourMiddle q) = 0 :=
    Q.property.2 _ hc
  have he := hermitian_orthogonal_sum_self sig H p (unitaryRankFourMiddle q) c
    (unitaryRankFourMiddle_perp_half q p (unitaryRankFourProjection_mem q _))
    (unitaryRankFourMiddle_pair_half q p (unitaryRankFourProjection_mem q _))
  have hmid : hermitianPair sig H (unitaryRankFourMiddle q) (unitaryRankFourMiddle q) = 1 :=
    unitaryRankFourMiddle_norm q
  rw [hp,hmid,mul_one,hn] at he
  change sig c * c = 1
  linear_combination -he

theorem exists_unitaryRankFour_common_middle_coefficient (q : CFSG.PrimePower)
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
      ∀ R : UnitaryRankFourOutsidePoint q,
        unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) + c • unitaryRankFourMiddle q ∈ (f R.val).val := by
  classical
  by_cases hn : Nonempty (UnitaryRankFourOutsidePoint q)
  · let R0 : UnitaryRankFourOutsidePoint q := Classical.choice hn
    have hEach (R : UnitaryRankFourOutsidePoint q) :=
      exists_unitaryRankFour_middle_image_coefficient q f hf hfixP hfixZ hfixMixed hfixW R
    choose c hcn hc using hEach
    refine ⟨c R0,hcn R0,unitaryRankFour_middle_chart_norm_one q R0 (f R0.val) (c R0) (hc R0),?_⟩
    intro R
    have he := unitaryRankFour_middle_coefficients_constant q f hlinear hfixW c hc R0 R
    rw [he]
    exact hc R
  · refine ⟨1,one_ne_zero,?_,?_⟩
    · rw [map_one,one_mul]
    · intro R
      exact False.elim (hn ⟨R⟩)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
