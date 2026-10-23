import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleCoefficient
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOutsidePointConnectivity
import SymmetricSubgroupAsymptotics.CFSGHermitianMiddleEdgeIndependence
import SymmetricSubgroupAsymptotics.CFSGHermitianLocalPairPiece
import SymmetricSubgroupAsymptotics.CFSGLinearMiddleRayComparison

/-! On each original outside generator line, its middle-zero difference
is a fixed singular point. ONE local linear representative therefore
forces its two normalized middle coefficients to agree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters

private theorem vector_decomposition (q : CFSG.PrimePower) (R : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideVector q R = unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) +
      unitaryRankFourMiddle q := by
  have hh := unitaryRankFourProjection_decomposition q (unitaryRankFourOutsideVector q R)
  simpa only [unitaryRankFourOutsideVector_middle, one_smul] using hh

private theorem chart_nonzero (q : CFSG.PrimePower) (R : UnitaryRankFourOutsidePoint q) (t : q.Extension 2) :
    unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) + t • unitaryRankFourMiddle q ≠ 0 := by
  intro h
  have hh := congrArg (unitaryRankFourProjection q) h
  rw [map_add,map_smul,unitaryRankFourProjection_middle,smul_zero,add_zero,
    unitaryRankFourProjection_eq_self_of_mem q _ (unitaryRankFourProjection_mem q _),map_zero] at hh
  exact unitaryRankFourProjection_ne_zero q _ (unitaryRankFourOutsideVector_outside q R)
    (unitaryRankFourOutsideVector_norm q R) hh

theorem unitaryRankFour_middle_coefficients_eq_on_edge (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryRankFourPoint q))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixW : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryRankFourHalf q → f Q = Q)
    (R S : UnitaryRankFourOutsidePoint q) (hRS : UnitaryRankFourOutsidePointAdjacent q R S)
    (r s : q.Extension 2)
    (hr : unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) + r • unitaryRankFourMiddle q ∈ (f R.val).val)
    (hs : unitaryRankFourProjection q (unitaryRankFourOutsideVector q S) + s • unitaryRankFourMiddle q ∈ (f S.val).val) : r = s := by
  classical
  by_cases heq : R = S
  · subst S
    exact unitaryRankFour_middle_coefficient_unique q R (f R.val) r s hr hs
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let v := unitaryRankFourOutsideVector q R
  let w := unitaryRankFourOutsideVector q S
  let p := unitaryRankFourProjection q v
  let z := unitaryRankFourProjection q w
  have hv : v = p + unitaryRankFourMiddle q := vector_decomposition q R
  have hw : w = z + unitaryRankFourMiddle q := vector_decomposition q S
  have hvw : hermitianPair sig H v w = 0 := hRS v (unitaryRankFourOutsideVector_mem q R)
    w (unitaryRankFourOutsideVector_mem q S)
  have hpz : p ≠ z := by
    intro h
    have hvwEq : v = w := hv.trans ((congrArg (fun x => x + unitaryRankFourMiddle q) h).trans hw.symm)
    apply heq
    apply Subtype.ext
    apply Subtype.ext
    exact (unitaryRankFourOutsideVector_span q R).trans
      ((congrArg (fun x => (q.Extension 2) ∙ x) hvwEq).trans (unitaryRankFourOutsideVector_span q S).symm)
  have hLI : LinearIndependent (q.Extension 2) ![p,z] := by
    apply hermitian_middle_edge_independent sig H p z (unitaryRankFourMiddle q)
      (unitaryRankFourProjection_norm_ne_zero q v (unitaryRankFourOutsideVector_outside q R)
        (unitaryRankFourOutsideVector_norm q R)) hpz
      (unitaryRankFourMiddle_perp_half q p (unitaryRankFourProjection_mem q v))
      (unitaryRankFourMiddle_pair_half q p (unitaryRankFourProjection_mem q v))
    · rw [←hv]
      exact unitaryRankFourOutsideVector_norm q R
    · rw [←hv,←hw]
      exact hvw
  obtain ⟨M,hvM,hwM⟩ := exists_hermitian_maximal_contains_pair sig H (unitaryNaturalPair_zero_swap q 4)
    v w (unitaryRankFourOutsideVector_norm q R) (unitaryRankFourOutsideVector_norm q S) hvw
  obtain ⟨F⟩ := hlinear M
  obtain ⟨a,ha,hFa⟩ := hermitian_piece_image_scalar sig H f ⟨M.val,M.property.1⟩
    (RingEquiv.refl (q.Extension 2)) F R.val v (p + r • unitaryRankFourMiddle q)
    hvM (unitaryRankFourOutsideVector_mem q R) (unitaryRankFourOutsideVector_ne_zero q R)
    hr (chart_nonzero q R r)
  obtain ⟨b,hb,hFb⟩ := hermitian_piece_image_scalar sig H f ⟨M.val,M.property.1⟩
    (RingEquiv.refl (q.Extension 2)) F S.val w (z + s • unitaryRankFourMiddle q)
    hwM (unitaryRankFourOutsideVector_mem q S) (unitaryRankFourOutsideVector_ne_zero q S)
    hs (chart_nonzero q S s)
  have hD0 : v - w ≠ 0 := by
    intro h
    exact hpz (congrArg (unitaryRankFourProjection q) (sub_eq_zero.mp h))
  have hDM : v - w ∈ M.val := M.val.sub_mem hvM hwM
  have hDn : hermitianPair sig H (v - w) (v - w) = 0 := M.property.1 _ hDM _ hDM
  have hDhalf : v - w = p - z := by rw [hv,hw]; module
  have hDW : v - w ∈ unitaryRankFourHalf q := by
    rw [hDhalf]
    exact (unitaryRankFourHalf q).sub_mem (unitaryRankFourProjection_mem q v) (unitaryRankFourProjection_mem q w)
  let D : UnitaryRankFourPoint q := singularRay sig H (v - w) hD0 hDn
  have hDfix : f D = D := hfixW D ((Submodule.span_singleton_le_iff_mem _ _).mpr hDW)
  have hDimage : v - w ∈ (f D).val := by
    rw [hDfix]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨k,hk,hFk⟩ := hermitian_piece_image_scalar sig H f ⟨M.val,M.property.1⟩
    (RingEquiv.refl (q.Extension 2)) F D (v - w) (v - w) hDM
    (Submodule.mem_span_singleton_self _) hD0 hDimage hD0
  have hsub := F.map.map_sub (⟨v,hvM⟩ : M.val) (⟨w,hwM⟩ : M.val)
  change F.map ⟨v-w,hDM⟩ = F.map ⟨v,hvM⟩ - F.map ⟨w,hwM⟩ at hsub
  have hfix : F.map ⟨v,hvM⟩ - F.map ⟨w,hwM⟩ = k • (p-z) :=
    hsub.symm.trans (hFk.trans (congrArg (fun x => k • x) hDhalf))
  exact CFSGLinearMiddleRayComparison.middle_ratios_eq (unitaryRankFourProjection q) (LinearMap.proj (2 : Fin 5))
    p z (unitaryRankFourMiddle q) (F.map ⟨v,hvM⟩) (F.map ⟨w,hwM⟩) hLI
    (unitaryRankFourProjection_eq_self_of_mem q p (unitaryRankFourProjection_mem q v))
    (unitaryRankFourProjection_eq_self_of_mem q z (unitaryRankFourProjection_mem q w))
    (unitaryRankFourProjection_middle q)
    (unitaryRankFourHalf_middle_zero q p (unitaryRankFourProjection_mem q v))
    (unitaryRankFourHalf_middle_zero q z (unitaryRankFourProjection_mem q w)) rfl
    a b r s k ha hFa hFb hfix

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
