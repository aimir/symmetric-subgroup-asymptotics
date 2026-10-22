import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusRecovery

/-! Every actual determinant-one signed-isometric natural elementary
matrix is a word in the two literal unipotent subgroups. This follows
by Gaussian elimination, not an assumed SU or Bruhat identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2DiagonalTorus

theorem upper_isometric_mem_rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) (u : NaturalElementary (q.Extension 2) 2)
    (hu : (u.val : Mat (q.Extension 2) 2).BlockTriangular id)
    (hform : ((definingFieldAutomorphism q 2).toRingHom.mapMatrix
        (u.val : Mat (q.Extension 2) 2)).transpose *
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2) *
        (u.val : Mat (q.Extension 2) 2) =
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2)) :
    u ∈ naturalRootGenerated q t := by
  let σ := definingFieldAutomorphism q 2
  obtain ⟨z, hz, a, b, hab, hfac⟩ := upper_isometric_factor (q.Extension 2) σ
    (fun x => extension_two_pow_twice q x) u.val hu (naturalElementary_det _ _ u) hform
  have he : u = torusNatural (q.Extension 2) σ z * upperNatural (q.Extension 2) σ a b := by
    apply Subtype.ext
    apply Units.ext
    change (u.val : Mat (q.Extension 2) 2) =
      ((torusNatural (q.Extension 2) σ z).val : Mat (q.Extension 2) 2) *
        ((upperNatural (q.Extension 2) σ a b).val : Mat (q.Extension 2) 2)
    rw [torusNatural_unit _ σ z hz, upperNatural_val]
    exact hfac
  rw [he]
  exact (naturalRootGenerated q t).mul_mem
    (torusNatural_mem_rootGenerated q t ht0 ht z hz)
    ((show naturalUnipotent q ≤ naturalRootGenerated q t from le_sup_left) ⟨a, b, hab, rfl⟩)

theorem isometric_mem_rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) (u : NaturalElementary (q.Extension 2) 2)
    (hform : ((definingFieldAutomorphism q 2).toRingHom.mapMatrix
        (u.val : Mat (q.Extension 2) 2)).transpose *
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2) *
        (u.val : Mat (q.Extension 2) 2) =
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2)) :
    u ∈ naturalRootGenerated q t := by
  let σ := definingFieldAutomorphism q 2
  let H := naturalRootGenerated q t
  by_cases h20 : (u.val : Mat (q.Extension 2) 2) 2 0 = 0
  · exact upper_isometric_mem_rootGenerated q t ht0 ht u
      (isometric_upper_of_lower_pivot_zero σ u.val hform h20) hform
  obtain ⟨a, b, hab, hc⟩ := upper_clear_column (q.Extension 2) σ
    (fun x => extension_two_pow_twice q x) (u.val : Mat (q.Extension 2) 2) hform h20
  let C := upperNatural (q.Extension 2) σ a b
  let N := weylNatural (q.Extension 2) t * C * u
  have hC : C ∈ H :=
    (show naturalUnipotent q ≤ H from le_sup_left) ⟨a, b, hab, rfl⟩
  have hNcol := weyl_after_column_clear (q.Extension 2) σ t ht0
    (u.val : Mat (q.Extension 2) 2) a b hc
  have hN20 : (N.val : Mat (q.Extension 2) 2) 2 0 = 0 := by
    have hh := congrArg (fun v : Fin 3 → q.Extension 2 => v 2) hNcol
    change (N.val : Mat (q.Extension 2) 2) 2 0 = _ at hh
    simpa [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] using hh
  have hufix := unit_fixed_of_isometric (q.Extension 2) 2 σ.toRingHom u.val hform
  have hNfix : diagramFieldUnitHom (q.Extension 2) 2 σ.toRingHom N.val = N.val := by
    change diagramFieldUnitHom (q.Extension 2) 2 σ.toRingHom
      ((weylNatural (q.Extension 2) t).val * C.val * u.val) = _
    rw [map_mul, map_mul, weylNatural_fixed q t ht,
      upperNatural_fixed (q.Extension 2) σ (fun x => extension_two_pow_twice q x) a b hab, hufix] <;> rfl
  have hNform := fixed_unit_isometric (q.Extension 2) 2 σ.toRingHom N.val hNfix
  have hN : N ∈ H := upper_isometric_mem_rootGenerated q t ht0 ht N
    (isometric_upper_of_lower_pivot_zero σ N.val hNform hN20) hNform
  have hpref : weylNatural (q.Extension 2) t * C ∈ H :=
    H.mul_mem (weylNatural_mem_rootGenerated q t ht0 ht) hC
  have hh := H.mul_mem (H.inv_mem hpref) hN
  change (weylNatural (q.Extension 2) t * C)⁻¹ *
    ((weylNatural (q.Extension 2) t * C) * u) ∈ H at hh
  simpa only [inv_mul_cancel_left] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
