import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCentralExtensionLayers
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex

/-! Actual torus orbit sizes on both characteristic layers, including
the gcd(3,q+1) loss on the vector layer. All finite quadratic fields and
both characteristics are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2UnipotentArrays
open CentralExtensionLayerOrbitIndex

theorem rankTwoFirstWeight_kernel_pow_norm (q : CFSG.PrimePower)
    (z : (q.Extension 2)ˣ) (hz : z ∈ (rankTwoFirstWeightHom q).ker) :
    z ^ (q.order + 1) = 1 := by
  have hcube : z ^ 3 = 1 := CFSGInvolutiveScalarWeights.kernel_cube
    (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) z hz
  have hw : (z : q.Extension 2) ^ 2 / definingFieldAutomorphism q 2 z = 1 := by
    have he := congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hz
    simpa only [rankTwoFirstWeightHom_val, CFSGTwistedA2DiagonalTorus.firstWeight,
      Units.val_one] using he
  have hs : definingFieldAutomorphism q 2 (z : q.Extension 2) = (z : q.Extension 2) ^ 2 :=
    ((div_eq_one_iff_eq ((map_ne_zero _).mpr (Units.ne_zero z))).mp hw).symm
  apply Units.ext
  change (z : q.Extension 2) ^ (q.order + 1) = 1
  calc
    _ = definingFieldAutomorphism q 2 (z : q.Extension 2) * (z : q.Extension 2) := by
      rw [pow_succ, definingFieldAutomorphism_apply]
    _ = (z : q.Extension 2) ^ 3 := by rw [hs]; ring
    _ = 1 := congrArg (fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) hcube

theorem rankTwoFirstWeight_kernel_card_le (q : CFSG.PrimePower) :
    Nat.card (rankTwoFirstWeightHom q).ker ≤ (q.order + 1).gcd 3 := by
  let g := (q.order + 1).gcd 3
  let f : (rankTwoFirstWeightHom q).ker →
      (powMonoidHom g : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker := fun z =>
    ⟨z.val, orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one (rankTwoFirstWeight_kernel_pow_norm q z.val z.property))
      (orderOf_dvd_of_pow_eq_one (CFSGInvolutiveScalarWeights.kernel_cube
        (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x)
          z.val z.property)))⟩
  have hf : Function.Injective f := by
    intro z w he
    exact Subtype.ext (congrArg (fun a :
      (powMonoidHom g : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker => a.val) he)
  calc
    _ ≤ Nat.card (powMonoidHom g : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker :=
      Nat.card_le_card_of_injective f hf
    _ = (Nat.card (q.Extension 2)ˣ).gcd g :=
      IsCyclic.card_powMonoidHom_ker (q.Extension 2)ˣ g
    _ ≤ g := Nat.gcd_le_right _ (Nat.gcd_pos_of_pos_left 3 (by omega))

theorem rankTwoFirstWeight_range_lower (q : CFSG.PrimePower) :
    q.order ^ 2 - 1 ≤ (q.order + 1).gcd 3 * Nat.card (rankTwoFirstWeightHom q).range := by
  have he : Nat.card (q.Extension 2)ˣ =
      Nat.card (rankTwoFirstWeightHom q).ker * Nat.card (rankTwoFirstWeightHom q).range := by
    rw [← (rankTwoFirstWeightHom q).ker.card_mul_index, Subgroup.index_ker]
  have hc := Nat.mul_le_mul_right (Nat.card (rankTwoFirstWeightHom q).range)
    (rankTwoFirstWeight_kernel_card_le q)
  rw [← he, Nat.card_units, extension_two_card] at hc
  exact hc

theorem rankTwoQuotientTorus_orbit_card (q : CFSG.PrimePower)
    (v : Multiplicative (q.Extension 2)) (hv : v ≠ 1) :
    Nat.card (layerOrbit (rankTwoQuotientTorusAutHom q) v) =
      Nat.card (rankTwoFirstWeightHom q).range := by
  have hv0 : v.toAdd ≠ 0 := by
    intro he
    exact hv (Multiplicative.toAdd.injective he)
  let f : (rankTwoFirstWeightHom q).range →
      layerOrbit (rankTwoQuotientTorusAutHom q) v := fun u =>
    ⟨Multiplicative.ofAdd ((u.val : q.Extension 2) * v.toAdd), by
      obtain ⟨z, hz⟩ := u.property
      refine ⟨(rankTwoSigmaUnits q).symm z, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [rankTwoQuotientTorus_scalar, ← rankTwoFirstWeight_sigma,
        MulEquiv.apply_symm_apply, hz]
      rfl⟩
  have hf : Function.Injective f := by
    intro u w he
    apply Subtype.ext
    apply Units.ext
    apply mul_right_cancel₀ hv0
    exact congrArg (fun a : layerOrbit (rankTwoQuotientTorusAutHom q) v => a.val.toAdd) he
  have hs : Function.Surjective f := by
    rintro ⟨w, z, hz⟩
    refine ⟨⟨rankTwoFirstWeightHom q (rankTwoSigmaUnits q z),
      ⟨rankTwoSigmaUnits q z, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change (rankTwoFirstWeightHom q (rankTwoSigmaUnits q z) : q.Extension 2) * v.toAdd = w.toAdd
    rw [rankTwoFirstWeight_sigma, ← rankTwoQuotientTorus_scalar, hz]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)).symm

theorem rankTwoCentralTorus_transitive (q : CFSG.PrimePower)
    (c d : Multiplicative (centralParameters q 0)) (hc : c ≠ 1) (hd : d ≠ 1) :
    ∃ z : (q.Extension 2)ˣ, rankTwoCentralTorusAutHom q z c = d := by
  have hc0 : c.toAdd.val ≠ 0 := by
    intro he
    exact hc (Multiplicative.toAdd.injective (Subtype.ext he))
  have hd0 : d.toAdd.val ≠ 0 := by
    intro he
    exact hd (Multiplicative.toAdd.injective (Subtype.ext he))
  have hratio : definingFieldAutomorphism q 2 (c.toAdd.val⁻¹ * d.toAdd.val) =
      c.toAdd.val⁻¹ * d.toAdd.val :=
    centralParameter_div_fixed q 0 c.toAdd.val hc0 c.toAdd.property d.toAdd
  obtain ⟨a, ha⟩ := exists_norm_eq_fixed q (c.toAdd.val⁻¹ * d.toAdd.val) hratio
  have ha0 : a ≠ 0 := by
    intro he
    apply mul_ne_zero (inv_ne_zero hc0) hd0
    rw [← ha, he, zero_mul]
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [rankTwoCentralTorus_scalar]
  change a * definingFieldAutomorphism q 2 a * c.toAdd.val = d.toAdd.val
  rw [ha]
  field_simp [hc0]

theorem rankTwoCentralTorus_orbit_card (q : CFSG.PrimePower)
    (c : Multiplicative (centralParameters q 0)) (hc : c ≠ 1) :
    Nat.card (layerOrbit (rankTwoCentralTorusAutHom q) c) = q.order - 1 := by
  have he : layerOrbit (rankTwoCentralTorusAutHom q) c = {d | d ≠ 1} := by
    ext d
    constructor
    · rintro ⟨z, rfl⟩ hd
      apply hc
      exact (rankTwoCentralTorusAutHom q z).injective
        (hd.trans (map_one (rankTwoCentralTorusAutHom q z)).symm)
    · intro hd
      exact rankTwoCentralTorus_transitive q c d hc hd
  rw [he]
  change Nat.card {d : Multiplicative (centralParameters q 0) // d ≠ 1} = _
  rw [nonone_card, Nat.card_congr Multiplicative.toAdd, centralParameters_card]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
