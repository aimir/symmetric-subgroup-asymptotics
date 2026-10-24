import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoLayerOrbitCardinality
import SymmetricSubgroupAsymptotics.CentralExtensionRankTwoIndexNumerics
import Mathlib.Data.Finite.Card

/-! Correlated index alternatives for the actual rank-two unitary
Heisenberg radical and actual quadratic-field torus. The central and
vector images are arbitrary subgroups, not full-field subspaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CentralExtensionLayerOrbitIndex

theorem rankTwo_central_card_mul_prime_le (q : CFSG.PrimePower)
    (C : Subgroup (Multiplicative (centralParameters q 0))) (hC : C ≠ ⊤) :
    q.prime * Nat.card C ≤ q.order := by
  have hZ : Nat.card (Multiplicative (centralParameters q 0)) = q.order :=
    (Nat.card_congr Multiplicative.toAdd).trans (centralParameters_card q 0)
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
    _ = Nat.card (Multiplicative (centralParameters q 0)) := by
      rw [Nat.mul_comm, C.card_mul_index]
    _ = _ := hZ

theorem rankTwo_quotient_image_card_le (q : CFSG.PrimePower)
    (J : Subgroup (fixedRadical q 0)) (hJ : ¬ (centralRadicalHom q 0).range ≤ J) :
    Nat.card (J.map (rankTwoParameterHom q)) ≤ q.order := by
  let f : J.map (rankTwoParameterHom q) → radicalVectorImage q 0 J := fun v =>
    ⟨fun _ : Fin 1 => v.val.toAdd, by
      obtain ⟨g, hg, hgv⟩ := v.property
      change Multiplicative.ofAdd (fun _ : Fin 1 => v.val.toAdd) ∈
        J.map (fixedRadicalParameterHom q 0)
      refine ⟨g, hg, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact congrArg Multiplicative.toAdd hgv⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact congrArg (fun a : radicalVectorImage q 0 J => a.val 0) he
  calc
    _ ≤ Nat.card (radicalVectorImage q 0 J) := Nat.card_le_card_of_injective f hf
    _ ≤ q.order := by simpa only [zero_add, pow_one] using radicalVectorImage_card_le q 0 J hJ

theorem rankTwo_semidirect_index_trichotomy (q : CFSG.PrimePower)
    (M : Subgroup (fixedRadical q 0 ⋊[rankTwoRadicalTorusAutHom q] (q.Extension 2)ˣ))
    (hM : ¬ (centralRadicalHom q 0).range ≤ M.comap SemidirectProduct.inl) :
    q.order ^ 3 ≤ M.index ∨
      q.prime ^ 2 * q.order * (q.order - 1) ≤ M.index ∨
        q.prime * q.order * (q.order + 1) ≤ (q.order + 1).gcd 3 * M.index := by
  let J := M.comap SemidirectProduct.inl
  let C := J.comap (centralRadicalHom q 0)
  let W := J.map (rankTwoParameterHom q)
  let L := M.map SemidirectProduct.rightHom
  have hC : C ≠ ⊤ := by
    intro he
    apply hM
    rintro g ⟨c, rfl⟩
    have hc : c ∈ C := by rw [he]; trivial
    exact hc
  have hc := rankTwo_central_card_mul_prime_le q C hC
  have hw := rankTwo_quotient_image_card_le q J hM
  have he : M.index * Nat.card C * Nat.card W = q.order ^ 3 * L.index :=
    rankTwo_semidirect_index_mul_layer_cards q M
  have hvector : 1 < Nat.card W → q.order ^ 2 - 1 ≤
      (q.order + 1).gcd 3 * (Nat.card W - 1) * L.index := by
    intro hW
    letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW
    obtain ⟨v, hv⟩ := exists_ne (1 : W)
    have hv0 : v.val ≠ 1 := fun hh => hv (Subtype.ext hh)
    have ho := quotient_orbit_card_le (rankTwoRadicalTorusAutHom q)
      (rankTwoParameterHom q) (rankTwoQuotientTorusAutHom q)
      (rankTwoQuotientTorus_intertwine q) M v.val v.property hv0
    have hr := rankTwoFirstWeight_range_lower q
    rw [← rankTwoQuotientTorus_orbit_card q v.val hv0] at hr
    exact hr.trans (by simpa only [mul_assoc] using
      Nat.mul_le_mul_left ((q.order + 1).gcd 3) ho)
  have hcentre : 1 < Nat.card C → q.order - 1 ≤ (Nat.card C - 1) * L.index := by
    intro hCgt
    letI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp hCgt
    obtain ⟨c, hc⟩ := exists_ne (1 : C)
    have hc0 : c.val ≠ 1 := fun hh => hc (Subtype.ext hh)
    have ho := central_orbit_card_le (rankTwoRadicalTorusAutHom q)
      (centralRadicalHom q 0) (rankTwoCentralTorusAutHom q)
      (rankTwoCentralTorus_intertwine q) (centralRadicalHom_mem_center q 0)
      M c.val c.property hc0
    rw [rankTwoCentralTorus_orbit_card q c.val hc0] at ho
    exact ho
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact CentralExtensionRankTwoIndexNumerics.index_trichotomy
    q.prime q.order ((q.order + 1).gcd 3) M.index (Nat.card C) (Nat.card W) L.index
    hq Nat.card_pos Nat.card_pos (Nat.card_pos (α := (q.Extension 2)ˣ ⧸ L))
      hc hw he hvector hcentre

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
