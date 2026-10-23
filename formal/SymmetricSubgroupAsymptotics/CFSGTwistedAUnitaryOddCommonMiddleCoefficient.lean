import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleConstancy
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleScale

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

theorem unitaryOdd_middle_chart_norm_one (q : CFSG.PrimePower) (m : ℕ)
    (R : UnitaryOddOutsidePoint q m) (Q : UnitaryOddPoint q m) (c : q.Extension 2)
    (hc : unitaryOddProjection q m (unitaryOddOutsideVector q m R) +
      c • unitaryOddMiddle q m ∈ Q.val) : definingFieldAutomorphism q 2 c * c = 1 := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  let p := unitaryOddProjection q m (unitaryOddOutsideVector q m R)
  let d := hermitianPair sig H (unitaryOddMiddle q m) (unitaryOddMiddle q m)
  have hp : hermitianPair sig H p p = -d := by
    have hh := unitaryOddProjection_norm q m (unitaryOddOutsideVector q m R)
    simpa only [unitaryOddOutsideVector_norm,unitaryOddOutsideVector_middle,
      map_one,mul_one,one_mul,zero_sub] using hh
  have hn : hermitianPair sig H (p + c • unitaryOddMiddle q m) (p + c • unitaryOddMiddle q m) = 0 :=
    Q.property.2 _ hc
  have he := hermitian_orthogonal_sum_self sig H p (unitaryOddMiddle q m) c
    (unitaryOddMiddle_perp_half q m p (unitaryOddProjection_mem q m _))
    (unitaryOddMiddle_pair_half q m p (unitaryOddProjection_mem q m _))
  have hmid : d ≠ 0 := unitaryOddMiddle_norm_ne_zero q m
  rw [hn] at he
  change 0 = hermitianPair sig H p p + sig c * c * d at he
  rw [hp] at he
  change sig c * c = 1
  apply mul_right_cancel₀ hmid
  change sig c * c * d = 1 * d
  linear_combination -he

theorem exists_unitaryOdd_common_middle_coefficient (q : CFSG.PrimePower) (m : ℕ)
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
      ∀ R : UnitaryOddOutsidePoint q m,
        unitaryOddProjection q m (unitaryOddOutsideVector q m R) + c • unitaryOddMiddle q m ∈ (f R.val).val := by
  classical
  by_cases hn : Nonempty (UnitaryOddOutsidePoint q m)
  · let R0 : UnitaryOddOutsidePoint q m := Classical.choice hn
    have hEach (R : UnitaryOddOutsidePoint q m) :=
      exists_unitaryOdd_middle_image_coefficient q m f hf hfixP hfixZ hfixMixed hfixW R
    choose c hcn hc using hEach
    refine ⟨c R0,hcn R0,unitaryOdd_middle_chart_norm_one q m R0 (f R0.val) (c R0) (hc R0),?_⟩
    intro R
    have he := unitaryOdd_middle_coefficients_constant q m f hlinear hfixW c hc R0 R
    rw [he]
    exact hc R
  · refine ⟨1,one_ne_zero,?_,?_⟩
    · rw [map_one,one_mul]
    · intro R
      exact False.elim (hn ⟨R⟩)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
