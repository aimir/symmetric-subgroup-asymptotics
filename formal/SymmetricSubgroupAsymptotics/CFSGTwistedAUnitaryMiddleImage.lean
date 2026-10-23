import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedMiddleProjection
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankFourProjectionNorm

/-! Actual five-dimensional opposed coordinates install the common
component scalar theorem. The image half-projection is proportional to
the source half-projection; the middle coefficient remains unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

abbrev UnitaryRankFourPoint (q : CFSG.PrimePower) :=
  SingularPoint (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)

theorem unitaryRankFour_decomposition (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    x = unitaryStandardProjection q 4 x + unitaryOppositeProjection q 4 x +
      x 2 • unitaryRankFourMiddle q := by
  have hh := unitary_half_decomposition q 4 x
  rw [unitaryRankFourCentralProjection] at hh
  exact hh

theorem unitaryRankFourProjection_eq_halves (q : CFSG.PrimePower) (x : Fin 5 → q.Extension 2) :
    unitaryRankFourProjection q x = unitaryStandardProjection q 4 x + unitaryOppositeProjection q 4 x := by
  rw [unitaryRankFourProjection_apply]
  exact sub_eq_iff_eq_add.mpr (unitaryRankFour_decomposition q x)

theorem unitaryRankFourMiddle_pair_half (q : CFSG.PrimePower)
    (w : Fin 5 → q.Extension 2) (hw : w ∈ unitaryRankFourHalf q) :
    unitaryNaturalPair q 4 (unitaryRankFourMiddle q) w = 0 :=
  (unitaryNaturalPair_zero_swap q 4 w _).mp (unitaryRankFourMiddle_perp_half q w hw)

theorem unitaryRankFour_half_projection_proportional (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryRankFourPoint q))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f)
    (hfixP : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryStandardSingularSpace q 4 → f Q = Q)
    (hfixZ : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryOppositeSingularSpace q 4 → f Q = Q)
    (hfixMixed : ∀ (u z : Fin 5 → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q 4 → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q 4 → z ≠ 0 →
      unitaryNaturalPair q 4 z u = 0 → ∀ Q : UnitaryRankFourPoint q,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (Q : UnitaryRankFourPoint q) (R R' : Fin 5 → q.Extension 2)
    (hR : R ∈ Q.val) (hR0 : R ≠ 0) (hRW : R ∉ unitaryRankFourHalf q)
    (hR' : R' ∈ (f Q).val) (hR'0 : R' ≠ 0) :
    ∃ a : q.Extension 2, a ≠ 0 ∧ unitaryRankFourProjection q R' = a • unitaryRankFourProjection q R := by
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let P : IsotropicSpace sig H := ⟨unitaryStandardSingularSpace q 4,
    fun x hx y hy => unitaryStandardSingularSpace_pair_zero q 4 x hx y hy⟩
  let Z : IsotropicSpace sig H := ⟨unitaryOppositeSingularSpace q 4,
    fun x hx y hy => unitaryOppositeSingularSpace_pair_zero q 4 x y hx hy⟩
  have hnorm : unitaryNaturalPair q 4 R R = 0 := Q.property.2 R hR
  have hWnorm : hermitianPair sig H
      (unitaryStandardProjection q 4 R + unitaryOppositeProjection q 4 R)
      (unitaryStandardProjection q 4 R + unitaryOppositeProjection q 4 R) ≠ 0 := by
    rw [←unitaryRankFourProjection_eq_halves]
    exact unitaryRankFourProjection_norm_ne_zero q R hRW hnorm
  obtain ⟨a,ha,hax,hay⟩ := hermitian_opposed_middle_projection sig H (unitaryNaturalPair_zero_swap q 4)
    f hf P Z (unitaryStandardSingularSpace_finrank q 4) (unitaryOppositeSingularSpace_finrank q 4)
    (unitaryStandard_opposite_disjoint q 4) (unitaryStandard_pair_opposite_nondegenerate q 4)
    (unitaryOpposite_pair_standard_nondegenerate q 4) hfixP hfixZ hfixMixed
    (unitaryRankFourMiddle q) (unitaryRankFourMiddle_pair_half q) Q
    (unitaryStandardProjection q 4 R) (unitaryOppositeProjection q 4 R)
    (unitaryStandardProjection q 4 R') (unitaryOppositeProjection q 4 R') (R 2) (R' 2)
    (unitaryStandardProjection_mem q 4 R) (unitaryOppositeProjection_mem q 4 R)
    (unitaryStandardProjection_mem q 4 R') (unitaryOppositeProjection_mem q 4 R') hWnorm
    (by rw [←unitaryRankFour_decomposition]; exact hR)
    (by rw [←unitaryRankFour_decomposition]; exact hR0)
    (by rw [←unitaryRankFour_decomposition]; exact hR')
    (by rw [←unitaryRankFour_decomposition]; exact hR'0)
  refine ⟨a,ha,?_⟩
  rw [unitaryRankFourProjection_eq_halves, unitaryRankFourProjection_eq_halves, hax, hay, smul_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
