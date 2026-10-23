import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedMiddleProjectionGeneral
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddProjectionNorm

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

abbrev UnitaryOddPoint (q : CFSG.PrimePower) (m : ℕ) :=
  SingularPoint (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4))

theorem unitaryOdd_decomposition (q : CFSG.PrimePower) (m : ℕ) (x : Fin (2*m+5) → q.Extension 2) :
    x = unitaryStandardProjection q (2*m+4) x + unitaryOppositeProjection q (2*m+4) x +
      x (unitaryOddMiddleIndex m) • unitaryOddMiddle q m := by
  have hh := unitary_half_decomposition q (2*m+4) x
  rw [unitaryOddCentralProjection] at hh
  exact hh

theorem unitaryOddProjection_eq_halves (q : CFSG.PrimePower) (m : ℕ) (x : Fin (2*m+5) → q.Extension 2) :
    unitaryOddProjection q m x = unitaryStandardProjection q (2*m+4) x + unitaryOppositeProjection q (2*m+4) x := by
  rw [unitaryOddProjection_apply]
  exact sub_eq_iff_eq_add.mpr (unitaryOdd_decomposition q m x)

theorem unitaryOddMiddle_pair_half (q : CFSG.PrimePower) (m : ℕ)
    (w : Fin (2*m+5) → q.Extension 2) (hw : w ∈ unitaryOddHalf q m) :
    unitaryNaturalPair q (2*m+4) (unitaryOddMiddle q m) w = 0 :=
  (unitaryNaturalPair_zero_swap q (2*m+4) w _).mp (unitaryOddMiddle_perp_half q m w hw)

theorem unitaryOdd_half_projection_proportional (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f)
    (hfixP : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryStandardSingularSpace q (2*m+4) → f Q = Q)
    (hfixZ : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOppositeSingularSpace q (2*m+4) → f Q = Q)
    (hfixMixed : ∀ (u z : Fin (2*m+5) → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q (2*m+4) → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q (2*m+4) → z ≠ 0 →
      unitaryNaturalPair q (2*m+4) z u = 0 → ∀ Q : UnitaryOddPoint q m,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (Q : UnitaryOddPoint q m) (R R' : Fin (2*m+5) → q.Extension 2)
    (hR : R ∈ Q.val) (hR0 : R ≠ 0) (hRW : R ∉ unitaryOddHalf q m)
    (hR' : R' ∈ (f Q).val) (hR'0 : R' ≠ 0) :
    ∃ a : q.Extension 2, a ≠ 0 ∧ unitaryOddProjection q m R' = a • unitaryOddProjection q m R := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q (2*m+4),
    fun x hx y hy => unitaryStandardSingularSpace_pair_zero q (2*m+4) x hx y hy⟩
  let Z : IsotropicSpace sig H := ⟨unitaryOppositeSingularSpace q (2*m+4),
    fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q (2*m+4) x y hx hy⟩
  have hnorm : unitaryNaturalPair q (2*m+4) R R = 0 := Q.property.2 R hR
  have hWnorm : hermitianPair sig H
      (unitaryStandardProjection q (2*m+4) R + unitaryOppositeProjection q (2*m+4) R)
      (unitaryStandardProjection q (2*m+4) R + unitaryOppositeProjection q (2*m+4) R) ≠ 0 := by
    rw [←unitaryOddProjection_eq_halves]
    exact unitaryOddProjection_norm_ne_zero q m R hRW hnorm
  have hdP : 2 ≤ Module.finrank (q.Extension 2) P.val := by
    change 2 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q (2*m+4))
    rw [unitaryStandardSingularSpace_finrank]
    omega
  obtain ⟨a,ha,hax,hay⟩ := hermitian_opposed_middle_projection_of_two_le sig H (unitaryNaturalPair_zero_swap q (2*m+4))
    f hf P Z hdP
    (unitaryStandard_opposite_disjoint q (2*m+4)) (unitaryStandard_pair_opposite_nondegenerate q (2*m+4))
    (unitaryOpposite_pair_standard_nondegenerate q (2*m+4)) hfixP hfixZ hfixMixed
    (unitaryOddMiddle q m) (unitaryOddMiddle_pair_half q m) Q
    (unitaryStandardProjection q (2*m+4) R) (unitaryOppositeProjection q (2*m+4) R)
    (unitaryStandardProjection q (2*m+4) R') (unitaryOppositeProjection q (2*m+4) R') (R (unitaryOddMiddleIndex m)) (R' (unitaryOddMiddleIndex m))
    (unitaryStandardProjection_mem q (2*m+4) R) (unitaryOppositeProjection_mem q (2*m+4) R)
    (unitaryStandardProjection_mem q (2*m+4) R') (unitaryOppositeProjection_mem q (2*m+4) R') hWnorm
    (by rw [←unitaryOdd_decomposition]; exact hR)
    (by rw [←unitaryOdd_decomposition]; exact hR0)
    (by rw [←unitaryOdd_decomposition]; exact hR')
    (by rw [←unitaryOdd_decomposition]; exact hR'0)
  refine ⟨a,ha,?_⟩
  rw [unitaryOddProjection_eq_halves, unitaryOddProjection_eq_halves, hax, hay, smul_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
