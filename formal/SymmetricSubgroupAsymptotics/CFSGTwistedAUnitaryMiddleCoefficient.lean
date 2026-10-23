import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOutsidePointCoordinates

/-! Existence and uniqueness of the actual image middle coefficient.
Only point fixation and original orthogonality tests determine the half
coordinates; no ambient linear action or chosen middle action is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

private theorem projection_middle_chart (q : CFSG.PrimePower) (R : UnitaryRankFourOutsidePoint q)
    (t : q.Extension 2) :
    unitaryRankFourProjection q (unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) +
      t • unitaryRankFourMiddle q) = unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) := by
  rw [map_add, map_smul, unitaryRankFourProjection_middle, smul_zero, add_zero,
    unitaryRankFourProjection_eq_self_of_mem q _ (unitaryRankFourProjection_mem q _)]

theorem unitaryRankFour_middle_coefficient_unique (q : CFSG.PrimePower)
    (R : UnitaryRankFourOutsidePoint q) (Q : UnitaryRankFourPoint q) (r s : q.Extension 2)
    (hr : unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) + r • unitaryRankFourMiddle q ∈ Q.val)
    (hs : unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) + s • unitaryRankFourMiddle q ∈ Q.val) : r = s := by
  let p := unitaryRankFourProjection q (unitaryRankFourOutsideVector q R)
  have hp0 : p ≠ 0 := unitaryRankFourProjection_ne_zero q _
    (unitaryRankFourOutsideVector_outside q R) (unitaryRankFourOutsideVector_norm q R)
  have hu0 : p + r • unitaryRankFourMiddle q ≠ 0 := by
    intro h
    have hh := congrArg (unitaryRankFourProjection q) h
    have he := projection_middle_chart q R r
    exact hp0 (he.symm.trans (hh.trans (map_zero _)))
  have hspan := singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) Q _ hr hu0
  rw [hspan] at hs
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hs
  have hproj := congrArg (unitaryRankFourProjection q) hc
  have hcr := projection_middle_chart q R r
  have hcs := projection_middle_chart q R s
  rw [map_smul, hcr, hcs] at hproj
  have hc1 : c = 1 := smul_left_injective (q.Extension 2) hp0 (by simpa only [one_smul] using hproj)
  have hp2 : p 2 = 0 := unitaryRankFourHalf_middle_zero q _ (unitaryRankFourProjection_mem q _)
  have hh2 : unitaryRankFourMiddle q (2 : Fin 5) = 1 := rfl
  have hmid := congrFun hc (2 : Fin 5)
  change (c • (p + r • unitaryRankFourMiddle q)) 2 = (p + s • unitaryRankFourMiddle q) 2 at hmid
  simpa only [hc1, one_smul, Pi.add_apply, Pi.smul_apply, hp2, hh2, smul_eq_mul, mul_one, one_mul, zero_add] using hmid

theorem exists_unitaryRankFour_middle_image_coefficient (q : CFSG.PrimePower)
    (f : Equiv.Perm (UnitaryRankFourPoint q))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) f)
    (hfixP : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryStandardSingularSpace q 4 → f Q = Q)
    (hfixZ : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryOppositeSingularSpace q 4 → f Q = Q)
    (hfixMixed : ∀ (u z : Fin 5 → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q 4 → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q 4 → z ≠ 0 →
      unitaryNaturalPair q 4 z u = 0 → ∀ Q : UnitaryRankFourPoint q,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (hfixW : ∀ Q : UnitaryRankFourPoint q, Q.val ≤ unitaryRankFourHalf q → f Q = Q)
    (R : UnitaryRankFourOutsidePoint q) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) +
      t • unitaryRankFourMiddle q ∈ (f R.val).val := by
  obtain ⟨v,hv,hv0⟩ := singularPoint_nonzero (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) (f R.val)
  obtain ⟨a,ha,hproj⟩ := unitaryRankFour_half_projection_proportional q f hf hfixP hfixZ hfixMixed
    R.val (unitaryRankFourOutsideVector q R) v (unitaryRankFourOutsideVector_mem q R)
    (unitaryRankFourOutsideVector_ne_zero q R) (unitaryRankFourOutsideVector_outside q R) hv hv0
  let y := a⁻¹ • v
  have hy : y ∈ (f R.val).val := (f R.val).val.smul_mem _ hv
  have hy0 : y ≠ 0 := smul_ne_zero (inv_ne_zero ha) hv0
  have hpy : unitaryRankFourProjection q y = unitaryRankFourProjection q (unitaryRankFourOutsideVector q R) := by
    change unitaryRankFourProjection q (a⁻¹ • v) = _
    rw [map_smul, hproj, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hyW : y ∉ unitaryRankFourHalf q := by
    intro h
    have hspan := singularPoint_span (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) (f R.val) y hy hy0
    have hle : (f R.val).val ≤ unitaryRankFourHalf q := by
      rw [hspan]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr h
    have he : f R.val = R.val := f.injective (hfixW (f R.val) hle)
    exact R.property (by rwa [he] at hle)
  refine ⟨y 2,unitaryRankFour_outside_middle_ne_zero q y hyW,?_⟩
  have he := unitaryRankFourProjection_decomposition q y
  rw [hpy] at he
  exact he ▸ hy

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
