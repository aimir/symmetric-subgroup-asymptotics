import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddMiddleCoefficient
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddOutsidePointConnectivity
import SymmetricSubgroupAsymptotics.CFSGHermitianMiddleEdgeIndependence
import SymmetricSubgroupAsymptotics.CFSGHermitianLocalPairPiece
import SymmetricSubgroupAsymptotics.CFSGLinearMiddleRayComparison

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters

private theorem vector_decomposition (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideVector q m R = unitaryOddProjection q m (unitaryOddOutsideVector q m R) +
      unitaryOddMiddle q m := by
  have hh := unitaryOddProjection_decomposition q m (unitaryOddOutsideVector q m R)
  simpa only [unitaryOddOutsideVector_middle, one_smul] using hh

private theorem chart_nonzero (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutsidePoint q m) (t : q.Extension 2) :
    unitaryOddProjection q m (unitaryOddOutsideVector q m R) + t • unitaryOddMiddle q m ≠ 0 := by
  intro h
  have hh := congrArg (unitaryOddProjection q m) h
  rw [map_add,map_smul,unitaryOddProjection_middle,smul_zero,add_zero,
    unitaryOddProjection_eq_self_of_mem q m _ (unitaryOddProjection_mem q m _),map_zero] at hh
  exact unitaryOddProjection_ne_zero q m _ (unitaryOddOutsideVector_outside q m R)
    (unitaryOddOutsideVector_norm q m R) hh

theorem unitaryOdd_middle_coefficients_eq_on_edge (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hlinear : ∀ M : MaximalSpace (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)),
      Nonempty (SemilinearPiece (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f
        ⟨M.val,M.property.1⟩ (RingEquiv.refl (q.Extension 2))))
    (hfixW : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOddHalf q m → f Q = Q)
    (R S : UnitaryOddOutsidePoint q m) (hRS : UnitaryOddOutsidePointAdjacent q m R S)
    (r s : q.Extension 2)
    (hr : unitaryOddProjection q m (unitaryOddOutsideVector q m R) + r • unitaryOddMiddle q m ∈ (f R.val).val)
    (hs : unitaryOddProjection q m (unitaryOddOutsideVector q m S) + s • unitaryOddMiddle q m ∈ (f S.val).val) : r = s := by
  classical
  by_cases heq : R = S
  · subst S
    exact unitaryOdd_middle_coefficient_unique q m R (f R.val) r s hr hs
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) (2*m+4) := signedReversalUnit (q.Extension 2) (2*m+4)
  let v := unitaryOddOutsideVector q m R
  let w := unitaryOddOutsideVector q m S
  let p := unitaryOddProjection q m v
  let z := unitaryOddProjection q m w
  have hv : v = p + unitaryOddMiddle q m := vector_decomposition q m R
  have hw : w = z + unitaryOddMiddle q m := vector_decomposition q m S
  have hvw : hermitianPair sig H v w = 0 := hRS v (unitaryOddOutsideVector_mem q m R)
    w (unitaryOddOutsideVector_mem q m S)
  have hpz : p ≠ z := by
    intro h
    have hvwEq : v = w := hv.trans ((congrArg (fun x => x + unitaryOddMiddle q m) h).trans hw.symm)
    apply heq
    apply Subtype.ext
    apply Subtype.ext
    exact (unitaryOddOutsideVector_span q m R).trans
      ((congrArg (fun x => (q.Extension 2) ∙ x) hvwEq).trans (unitaryOddOutsideVector_span q m S).symm)
  have hLI : LinearIndependent (q.Extension 2) ![p,z] := by
    apply hermitian_middle_edge_independent sig H p z (unitaryOddMiddle q m)
      (unitaryOddProjection_norm_ne_zero q m v (unitaryOddOutsideVector_outside q m R)
        (unitaryOddOutsideVector_norm q m R)) hpz
      (unitaryOddMiddle_perp_half q m p (unitaryOddProjection_mem q m v))
      (unitaryOddMiddle_pair_half q m p (unitaryOddProjection_mem q m v))
    · rw [←hv]
      exact unitaryOddOutsideVector_norm q m R
    · rw [←hv,←hw]
      exact hvw
  obtain ⟨M,hvM,hwM⟩ := exists_hermitian_maximal_contains_pair sig H (unitaryNaturalPair_zero_swap q (2*m+4))
    v w (unitaryOddOutsideVector_norm q m R) (unitaryOddOutsideVector_norm q m S) hvw
  obtain ⟨F⟩ := hlinear M
  obtain ⟨a,ha,hFa⟩ := hermitian_piece_image_scalar sig H f ⟨M.val,M.property.1⟩
    (RingEquiv.refl (q.Extension 2)) F R.val v (p + r • unitaryOddMiddle q m)
    hvM (unitaryOddOutsideVector_mem q m R) (unitaryOddOutsideVector_ne_zero q m R)
    hr (chart_nonzero q m R r)
  obtain ⟨b,hb,hFb⟩ := hermitian_piece_image_scalar sig H f ⟨M.val,M.property.1⟩
    (RingEquiv.refl (q.Extension 2)) F S.val w (z + s • unitaryOddMiddle q m)
    hwM (unitaryOddOutsideVector_mem q m S) (unitaryOddOutsideVector_ne_zero q m S)
    hs (chart_nonzero q m S s)
  have hD0 : v - w ≠ 0 := by
    intro h
    exact hpz (congrArg (unitaryOddProjection q m) (sub_eq_zero.mp h))
  have hDM : v - w ∈ M.val := M.val.sub_mem hvM hwM
  have hDn : hermitianPair sig H (v - w) (v - w) = 0 := M.property.1 _ hDM _ hDM
  have hDhalf : v - w = p - z := by rw [hv,hw]; module
  have hDW : v - w ∈ unitaryOddHalf q m := by
    rw [hDhalf]
    exact (unitaryOddHalf q m).sub_mem (unitaryOddProjection_mem q m v) (unitaryOddProjection_mem q m w)
  let D : UnitaryOddPoint q m := singularRay sig H (v - w) hD0 hDn
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
  exact CFSGLinearMiddleRayComparison.middle_ratios_eq (unitaryOddProjection q m) (LinearMap.proj (unitaryOddMiddleIndex m))
    p z (unitaryOddMiddle q m) (F.map ⟨v,hvM⟩) (F.map ⟨w,hwM⟩) hLI
    (unitaryOddProjection_eq_self_of_mem q m p (unitaryOddProjection_mem q m v))
    (unitaryOddProjection_eq_self_of_mem q m z (unitaryOddProjection_mem q m w))
    (unitaryOddProjection_middle q m)
    (unitaryOddHalf_middle_zero q m p (unitaryOddProjection_mem q m v))
    (unitaryOddHalf_middle_zero q m z (unitaryOddProjection_mem q m w))
    (by change unitaryOddMiddle q m (unitaryOddMiddleIndex m) = 1
        simp only [unitaryOddMiddle, Pi.single_eq_same])
    a b r s k ha hFa hFb hfix

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
