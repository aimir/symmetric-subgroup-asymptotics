import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddOutsidePointCoordinates

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

private theorem projection_middle_chart (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutsidePoint q m)
    (t : q.Extension 2) :
    unitaryOddProjection q m (unitaryOddProjection q m (unitaryOddOutsideVector q m R) +
      t • unitaryOddMiddle q m) = unitaryOddProjection q m (unitaryOddOutsideVector q m R) := by
  rw [map_add, map_smul, unitaryOddProjection_middle, smul_zero, add_zero,
    unitaryOddProjection_eq_self_of_mem q m _ (unitaryOddProjection_mem q m _)]

theorem unitaryOdd_middle_coefficient_unique (q : CFSG.PrimePower) (m : ℕ)
    (R : UnitaryOddOutsidePoint q m) (Q : UnitaryOddPoint q m) (r s : q.Extension 2)
    (hr : unitaryOddProjection q m (unitaryOddOutsideVector q m R) + r • unitaryOddMiddle q m ∈ Q.val)
    (hs : unitaryOddProjection q m (unitaryOddOutsideVector q m R) + s • unitaryOddMiddle q m ∈ Q.val) : r = s := by
  let p := unitaryOddProjection q m (unitaryOddOutsideVector q m R)
  have hp0 : p ≠ 0 := unitaryOddProjection_ne_zero q m _
    (unitaryOddOutsideVector_outside q m R) (unitaryOddOutsideVector_norm q m R)
  have hu0 : p + r • unitaryOddMiddle q m ≠ 0 := by
    intro h
    have hh := congrArg (unitaryOddProjection q m) h
    have he := projection_middle_chart q m R r
    exact hp0 (he.symm.trans (hh.trans (map_zero _)))
  have hspan := singularPoint_span (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) Q _ hr hu0
  rw [hspan] at hs
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hs
  have hproj := congrArg (unitaryOddProjection q m) hc
  have hcr := projection_middle_chart q m R r
  have hcs := projection_middle_chart q m R s
  rw [map_smul, hcr, hcs] at hproj
  have hc1 : c = 1 := smul_left_injective (q.Extension 2) hp0 (by simpa only [one_smul] using hproj)
  have hp2 : p (unitaryOddMiddleIndex m) = 0 := unitaryOddHalf_middle_zero q m _ (unitaryOddProjection_mem q m _)
  have hh2 : unitaryOddMiddle q m (unitaryOddMiddleIndex m) = 1 := by
    simp only [unitaryOddMiddle, Pi.single_eq_same]
  have hmid := congrFun hc (unitaryOddMiddleIndex m)
  change (c • (p + r • unitaryOddMiddle q m)) (unitaryOddMiddleIndex m) =
    (p + s • unitaryOddMiddle q m) (unitaryOddMiddleIndex m) at hmid
  simpa only [hc1, one_smul, Pi.add_apply, Pi.smul_apply, hp2, hh2, smul_eq_mul, mul_one, one_mul, zero_add] using hmid

theorem exists_unitaryOdd_middle_image_coefficient (q : CFSG.PrimePower) (m : ℕ)
    (f : Equiv.Perm (UnitaryOddPoint q m))
    (hf : PreservesOrthogonality (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) f)
    (hfixP : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryStandardSingularSpace q (2*m+4) → f Q = Q)
    (hfixZ : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOppositeSingularSpace q (2*m+4) → f Q = Q)
    (hfixMixed : ∀ (u z : Fin (2*m+5) → q.Extension 2),
      u ∈ unitaryStandardSingularSpace q (2*m+4) → u ≠ 0 → z ∈ unitaryOppositeSingularSpace q (2*m+4) → z ≠ 0 →
      unitaryNaturalPair q (2*m+4) z u = 0 → ∀ Q : UnitaryOddPoint q m,
      Q.val = (q.Extension 2) ∙ (u + z) → f Q = Q)
    (hfixW : ∀ Q : UnitaryOddPoint q m, Q.val ≤ unitaryOddHalf q m → f Q = Q)
    (R : UnitaryOddOutsidePoint q m) :
    ∃ t : q.Extension 2, t ≠ 0 ∧ unitaryOddProjection q m (unitaryOddOutsideVector q m R) +
      t • unitaryOddMiddle q m ∈ (f R.val).val := by
  obtain ⟨v,hv,hv0⟩ := singularPoint_nonzero (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) (f R.val)
  obtain ⟨a,ha,hproj⟩ := unitaryOdd_half_projection_proportional q m f hf hfixP hfixZ hfixMixed
    R.val (unitaryOddOutsideVector q m R) v (unitaryOddOutsideVector_mem q m R)
    (unitaryOddOutsideVector_ne_zero q m R) (unitaryOddOutsideVector_outside q m R) hv hv0
  let y := a⁻¹ • v
  have hy : y ∈ (f R.val).val := (f R.val).val.smul_mem _ hv
  have hy0 : y ≠ 0 := smul_ne_zero (inv_ne_zero ha) hv0
  have hpy : unitaryOddProjection q m y = unitaryOddProjection q m (unitaryOddOutsideVector q m R) := by
    change unitaryOddProjection q m (a⁻¹ • v) = _
    rw [map_smul, hproj, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hyW : y ∉ unitaryOddHalf q m := by
    intro h
    have hspan := singularPoint_span (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) (f R.val) y hy hy0
    have hle : (f R.val).val ≤ unitaryOddHalf q m := by
      rw [hspan]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr h
    have he : f R.val = R.val := f.injective (hfixW (f R.val) hle)
    exact R.property (by rwa [he] at hle)
  refine ⟨y (unitaryOddMiddleIndex m),unitaryOdd_outside_middle_ne_zero q m y hyW,?_⟩
  have he := unitaryOddProjection_decomposition q m y
  rw [hpy] at he
  exact he ▸ hy

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
