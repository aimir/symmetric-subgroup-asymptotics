import SymmetricSubgroupAsymptotics.CFSGUnitaryMiddleRadicalExtension
import SymmetricSubgroupAsymptotics.CFSGUnitaryNaturalNormOrbitCardinality
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex
import SymmetricSubgroupAsymptotics.CentralExtensionIsotropicOrbitNumerics

/-! The same subgroup of the actual unitary middle extension supplies
the central intersection, isotropic quotient image, and projected
middle subgroup. The quotient image is only an additive subgroup over
the prime field. No invariance of the radical intersection under the
naked projected subgroup is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CentralExtensionLayerOrbitIndex

local instance finiteMiddleSemidirect {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

theorem centralParameters_proper_card_mul_prime_le (q : CFSG.PrimePower) (t : ℕ)
    (C : Subgroup (Multiplicative (centralParameters q t))) (hC : C ≠ ⊤) :
    q.prime * Nat.card C ≤ q.order := by
  have hZ : Nat.card (Multiplicative (centralParameters q t)) = q.order :=
    (Nat.card_congr Multiplicative.toAdd).trans (centralParameters_card q t)
  have hd : C.index ∣ q.prime ^ q.exponent := by
    change C.index ∣ q.order
    rw [← hZ]
    exact C.index_dvd_card
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow q.prime_isPrime).mp hd
  have hkpos : 0 < k := by
    by_contra he
    have hk0 : k = 0 := by omega
    apply hC
    apply Subgroup.index_eq_one.mp
    simpa only [hk0, pow_zero] using hk
  have hp : q.prime ≤ C.index := by
    rw [hk]
    exact Nat.le_self_pow (Nat.ne_of_gt hkpos) q.prime
  calc
    _ ≤ C.index * Nat.card C := Nat.mul_le_mul_right (Nat.card C) hp
    _ = Nat.card (Multiplicative (centralParameters q t)) := by
      rw [Nat.mul_comm, C.card_mul_index]
    _ = _ := hZ

theorem radicalQuotientImage_card_le (q : CFSG.PrimePower) (t : ℕ)
    (J : Subgroup (fixedRadical q t)) (hJ : ¬ (centralRadicalHom q t).range ≤ J) :
    Nat.card (J.map (fixedRadicalParameterHom q t)) ≤ q.order ^ (t + 1) := by
  let e : J.map (fixedRadicalParameterHom q t) ≃ radicalVectorImage q t J := {
    toFun v := ⟨v.val.toAdd, v.property⟩
    invFun v := ⟨Multiplicative.ofAdd v.val, v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans_le (radicalVectorImage_card_le q t J hJ)

theorem higherUnitaryQuotient_orbit_card (q : CFSG.PrimePower) (s : ℕ)
    (v : Multiplicative (Fin (s + 3) → q.Extension 2)) :
    Nat.card (layerOrbit (naturalVectorMulAutHom q (s + 2)) v) =
      Nat.card (unitaryVectorOrbit q s v.toAdd) := by
  let e : layerOrbit (naturalVectorMulAutHom q (s + 2)) v ≃
      unitaryVectorOrbit q s v.toAdd := {
    toFun w := ⟨w.val.toAdd, by
      obtain ⟨g, hg⟩ := w.property
      refine ⟨g, ?_⟩
      exact congrArg Multiplicative.toAdd hg⟩
    invFun w := ⟨Multiplicative.ofAdd w.val, by
      obtain ⟨g, hg⟩ := w.property
      refine ⟨g, ?_⟩
      exact congrArg Multiplicative.ofAdd hg⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Nat.card_congr e

theorem higherUnitaryVector_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (Multiplicative (Fin (s + 3) → q.Extension 2)) =
      (q.order ^ (s + 3)) ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
    extension_two_card, ← pow_mul, ← pow_mul]
  congr 1
  omega

abbrev higherUnitaryPointParabolic (q : CFSG.PrimePower) (s : ℕ) :=
  fixedRadical q (s + 2) ⋊[radicalMiddleAutHom q (s + 2)] naturalFixed (s + 2) q

theorem higherUnitary_semidirect_coupled_index (q : CFSG.PrimePower) (s : ℕ)
    (M : Subgroup (higherUnitaryPointParabolic q s))
    (hM : ¬ (centralRadicalHom q (s + 2)).range ≤ M.comap SemidirectProduct.inl) :
    q.prime * ((q.order ^ 2 - 1) * q.order ^ (2 * s + 3)) ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let C := J.comap (centralRadicalHom q (s + 2))
  let W := J.map (fixedRadicalParameterHom q (s + 2))
  let L := M.map SemidirectProduct.rightHom
  have hC : C ≠ ⊤ := by
    intro he
    apply hM
    rintro g ⟨c, rfl⟩
    have hc : c ∈ C := by rw [he]; trivial
    exact hc
  have hc := centralParameters_proper_card_mul_prime_le q (s + 2) C hC
  have hw := radicalQuotientImage_card_le q (s + 2) J hM
  have hZ : Nat.card (Multiplicative (centralParameters q (s + 2))) = q.order :=
    (Nat.card_congr Multiplicative.toAdd).trans (centralParameters_card q (s + 2))
  have he : M.index * Nat.card C * Nat.card W =
      q.order * (q.order ^ (s + 3)) ^ 2 * L.index := by
    have hh := CentralExtensionSemidirectStabilizer.index_mul_layer_cards
      (radicalMiddleAutHom q (s + 2)) (fixedRadicalParameterHom q (s + 2))
      (fixedRadicalParameterHom_surjective q (s + 2)) (centralRadicalHom q (s + 2))
      (centralRadicalHom_range_eq_kernel q (s + 2)) M
    simpa only [hZ, higherUnitaryVector_card] using hh
  have hO : (q.order ^ 2 - 1) * q.order ^ (2 * s + 3) ≤
      (q.order ^ (s + 3)) ^ 2 := by
    let v : Fin (s + 3) → q.Extension 2 := Pi.single 0 1
    have hv : v ≠ 0 := by
      intro hh
      have hh0 := congrFun hh 0
      exact one_ne_zero (by simpa only [v, Pi.single_eq_same, Pi.zero_apply] using hh0)
    calc
      _ ≤ Nat.card (unitaryVectorOrbit q s v) := trace_slice_le_unitaryVectorOrbit q s v hv
      _ ≤ Nat.card (Fin (s + 3) → q.Extension 2) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = _ := (Nat.card_congr Multiplicative.toAdd).symm.trans
        (higherUnitaryVector_card q s)
  have horbit : 1 < Nat.card W →
      (q.order ^ 2 - 1) * q.order ^ (2 * s + 3) ≤ (Nat.card W - 1) * L.index := by
    intro hW
    letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW
    obtain ⟨v, hv⟩ := exists_ne (1 : W)
    have hv1 : v.val ≠ 1 := fun hh => hv (Subtype.ext hh)
    have hv0 : v.val.toAdd ≠ 0 := by
      intro hh
      exact hv1 (Multiplicative.toAdd.injective hh)
    have ho := quotient_orbit_card_le (radicalMiddleAutHom q (s + 2))
      (fixedRadicalParameterHom q (s + 2)) (naturalVectorMulAutHom q (s + 2))
      (radicalMiddleAut_parameter q (s + 2)) M v.val v.property hv1
    rw [higherUnitaryQuotient_orbit_card] at ho
    exact (trace_slice_le_unitaryVectorOrbit q s v.val.toAdd hv0).trans ho
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos q.exponent
  exact CentralExtensionIsotropicOrbitNumerics.prime_mul_orbit_le_index
    q.prime q.order (q.order ^ (s + 3)) M.index (Nat.card C) (Nat.card W) L.index
    ((q.order ^ 2 - 1) * q.order ^ (2 * s + 3))
    hq (pow_pos hq _) Nat.card_pos Nat.card_pos
    (Nat.card_pos (α := naturalFixed (s + 2) q ⧸ L)) hc hw he hO horbit

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
