import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedLiftPullback
import SymmetricSubgroupAsymptotics.CFSGTwistedACentralDerivedLift

/-! The scalar ambiguity of every actual fixed natural lift is central.
Consequently it disappears on the SAME pullback commutator subgroup. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

theorem scalar_matrixUnit_mem_center (K : Type) [Field K] (r : ℕ)
    (u : (Mat K r)ˣ) (c : K) (hu : (u : Mat K r) = c • (1 : Mat K r)) :
    u ∈ Subgroup.center (Mat K r)ˣ := by
  apply Subgroup.mem_center_iff.mpr
  intro v
  apply Units.ext
  change (v : Mat K r) * (u : Mat K r) = (u : Mat K r) * (v : Mat K r)
  rw [hu]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem similitude_central_ratio (K : Type) [Field K] (r : ℕ)
    (f : K →+* K) (u : (Mat K r)ˣ) (c : K)
    (hc : (f.mapMatrix (u : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r) =
          c • (↑((signedReversalUnit K r)⁻¹) : Mat K r)) :
    diagramFieldUnitHom K r f u * u⁻¹ ∈ Subgroup.center (Mat K r)ˣ := by
  let v := diagramFieldUnitHom K r f u
  have hleft : (↑(v⁻¹ * u) : Mat K r) = c • (1 : Mat K r) := by
    have he := congrArg (fun X : Mat K r => (signedReversalUnit K r : Mat K r) * X) hc
    change (↑(v⁻¹) : Mat K r) * (u : Mat K r) = _
    dsimp only [v]
    rw [diagramFieldUnitHom_inv_val]
    simpa only [mul_assoc, mul_smul_comm, Units.mul_inv] using he
  have hz : v⁻¹ * u ∈ Subgroup.center (Mat K r)ˣ :=
    scalar_matrixUnit_mem_center K r _ c hleft
  have hzi := (Subgroup.center (Mat K r)ˣ).inv_mem hz
  have hh := (inferInstance : (Subgroup.center (Mat K r)ˣ).Normal).conj_mem
    (v⁻¹ * u)⁻¹ hzi u
  simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hh

theorem pullbackMatrix_central_ratio (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (p : fixedNaturalPullback r q) :
    diagramFieldUnitHom (q.Extension 2) r
        (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
        (pullbackMatrix r q p) * (pullbackMatrix r q p)⁻¹ ∈
      Subgroup.center (Mat (q.Extension 2) r)ˣ := by
  obtain ⟨c, _, hc⟩ := pullbackMatrix_similitude r hr q p
  exact similitude_central_ratio (q.Extension 2) r
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom _ c hc

theorem pullback_derived_twist_fixed (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (p : commutator (fixedNaturalPullback r q)) :
    diagramFieldUnitHom (q.Extension 2) r
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
      (pullbackMatrix r q p.val) = pullbackMatrix r q p.val :=
  CFSGTwistedACentralDerivedLift.twist_fixes_derived_lifts
    (diagramFieldUnitHom (q.Extension 2) r
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom)
    (pullbackMatrix r q) (pullbackMatrix_central_ratio r hr q) p

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
