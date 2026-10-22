import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPullbackTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitIsometry
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSignedForm

/-! A literal unitriangular signed-form similitude is an isometry:
its genuine multiplier is forced to one by a single extreme form entry.
This applies to actual source pullbacks in all ranks and all fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem unitriangular_similitude_multiplier_one {K : Type*} [Field K]
    (r : ℕ) (f : K →+* K) (M H : Mat K r) (c : K)
    (hu : M.BlockTriangular id) (hd : ∀ i, M i i = 1)
    (hH : H 0 (Fin.last r) ≠ 0)
    (hrow : ∀ j, j ≠ Fin.last r → H 0 j = 0)
    (heq : (f.mapMatrix M).transpose * H * M = c • H) : c = 1 := by
  have hleft (j : Fin (r + 1)) : ((f.mapMatrix M).transpose * H) 0 j = H 0 j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        hd, map_one, one_mul]
    · intro i _ hi
      have hz : M i 0 = 0 := hu (Fin.pos_iff_ne_zero.mpr hi)
      simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        hz, map_zero, zero_mul]
    · simp
  have hsum : ∑ j, H 0 j * M j (Fin.last r) = H 0 (Fin.last r) := by
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hd, mul_one]
    · intro j _ hj
      rw [hrow j hj, zero_mul]
    · simp
  have he := congrArg (fun A : Mat K r => A 0 (Fin.last r)) heq
  change ((f.mapMatrix M).transpose * H * M) 0 (Fin.last r) = c * H 0 (Fin.last r) at he
  rw [Matrix.mul_apply] at he
  simp_rw [hleft] at he
  rw [hsum] at he
  exact (mul_left_eq_self₀.mp he.symm).resolve_right hH

theorem unitriangular_signed_similitude_fixed (K : Type) [Field K] (r : ℕ)
    (f : K →+* K) (M : (Mat K r)ˣ) (c : K)
    (hu : (M : Mat K r).BlockTriangular id) (hd : ∀ i, (M : Mat K r) i i = 1)
    (heq : (f.mapMatrix (M : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (M : Mat K r) =
      c • (↑((signedReversalUnit K r)⁻¹) : Mat K r)) :
    diagramFieldUnitHom K r f M = M := by
  have hrev : (0 : Fin (r + 1)).rev = Fin.last r := by
    apply Fin.ext
    simp [Fin.rev]
  have hrow (j : Fin (r + 1)) (hj : j ≠ Fin.last r) :
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) 0 j = 0 := by
    rw [signedReversalUnit_inv_parity]
    simp only [Matrix.smul_apply, signedReversalUnit_apply, hrev, if_neg (Ne.symm hj),
      smul_zero]
  have hH : (↑((signedReversalUnit K r)⁻¹) : Mat K r) 0 (Fin.last r) ≠ 0 := by
    rw [signedReversalUnit_inv_parity]
    simp only [Matrix.smul_apply, signedReversalUnit_apply, hrev, if_true,
      signWeight, Fin.val_zero, pow_zero, smul_eq_mul, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hc := unitriangular_similitude_multiplier_one r f (M : Mat K r) _ c hu hd hH hrow heq
  apply unit_fixed_of_isometric K r f M
  simpa only [hc, one_smul] using heq

theorem pullbackSource_mem_unipotent_of_unitriangular (q : CFSG.PrimePower)
    (r : ℕ) (hr : 1 ≤ r) (p : fixedNaturalPullback r q)
    (hu : (pullbackMatrix r q p : Mat (q.Extension 2) r).BlockTriangular id)
    (hd : ∀ i, (pullbackMatrix r q p : Mat (q.Extension 2) r) i i = 1) :
    pullbackSource r q p ∈ originalUnipotent r q := by
  obtain ⟨c, _, hc⟩ := pullbackMatrix_similitude r hr q p
  have hf := unitriangular_signed_similitude_fixed (q.Extension 2) r
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
    (pullbackMatrix r q p) c hu hd hc
  let u : naturalUnipotent r q := ⟨pullbackElementary r q p, ⟨hu, hd⟩, hf⟩
  refine ⟨u, ?_⟩
  apply twistedFixedAction_injective q r
  rw [unipotentToOriginalFixed_action, ← pullback_action_eq]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
