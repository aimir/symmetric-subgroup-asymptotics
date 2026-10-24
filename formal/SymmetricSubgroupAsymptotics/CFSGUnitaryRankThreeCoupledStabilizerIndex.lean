import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeSmallVectorOrbits
import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalInvolutions
import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledStabilizerIndex
import SymmetricSubgroupAsymptotics.CentralExtensionBinarySingularIndexNumerics

/-! Both small rank-three bounds use the same subgroup M of the literal
radical-normalizer extension. Its central intersection, additive quotient
image, and projected subgroup remain correlated. In characteristic two,
trivial central intersection gives quadratic singularity, not merely
polar isotropy. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CentralExtensionLayerOrbitIndex

local instance finiteNormalizerSemidirect {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

abbrev rankThreeNormalizerExtension (q : CFSG.PrimePower) :=
  fixedRadical q 1 ⋊[unitaryRadicalNormalizerAutHom q 1] unitaryRadicalNormalizer q 1

private theorem rankThreeVector_card (q : CFSG.PrimePower) :
    Nat.card (Multiplicative (Fin 2 → q.Extension 2)) = (q.order ^ 2) ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, extension_two_card]

theorem rankThree_normalizer_index_mul_layer_cards (q : CFSG.PrimePower)
    (M : Subgroup (rankThreeNormalizerExtension q)) :
    M.index * Nat.card ((M.comap SemidirectProduct.inl).comap (centralRadicalHom q 1)) *
        Nat.card ((M.comap SemidirectProduct.inl).map (fixedRadicalParameterHom q 1)) =
      q.order * (q.order ^ 2) ^ 2 * (M.map SemidirectProduct.rightHom).index := by
  have hZ : Nat.card (Multiplicative (centralParameters q 1)) = q.order :=
    (Nat.card_congr Multiplicative.toAdd).trans (centralParameters_card q 1)
  have hh := CentralExtensionSemidirectStabilizer.index_mul_layer_cards
    (unitaryRadicalNormalizerAutHom q 1) (fixedRadicalParameterHom q 1)
    (fixedRadicalParameterHom_surjective q 1) (centralRadicalHom q 1)
    (centralRadicalHom_range_eq_kernel q 1) M
  have hV : Nat.card (Multiplicative (Fin (1 + 1) → q.Extension 2)) =
      (q.order ^ 2) ^ 2 := rankThreeVector_card q
  simpa only [hZ, hV] using hh

private theorem proper_central_preimage (q : CFSG.PrimePower)
    (M : Subgroup (rankThreeNormalizerExtension q))
    (hM : ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl) :
    (M.comap SemidirectProduct.inl).comap (centralRadicalHom q 1) ≠ ⊤ := by
  intro he
  apply hM
  rintro g ⟨c, rfl⟩
  have hc : c ∈ (M.comap SemidirectProduct.inl).comap (centralRadicalHom q 1) := by
    rw [he]
    trivial
  exact hc

private theorem prime_dvd_order (q : CFSG.PrimePower) : q.prime ∣ q.order := by
  change q.prime ∣ q.prime ^ q.exponent
  exact dvd_pow_self _ q.exponent_pos.ne'

theorem rankThree_binary_semidirect_coupled_index (q : CFSG.PrimePower)
    (hq : q.order = 2) (M : Subgroup (rankThreeNormalizerExtension q))
    (hM : ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl) :
    24 ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let C := J.comap (centralRadicalHom q 1)
  let W := J.map (fixedRadicalParameterHom q 1)
  let L := M.map SemidirectProduct.rightHom
  have hd := prime_dvd_order q
  rw [hq] at hd
  have hp : q.prime = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd
  have hc := centralParameters_proper_card_mul_prime_le q 1 C (proper_central_preimage q M hM)
  have hc1 : Nat.card C = 1 := by
    have hc2 : 2 * Nat.card C ≤ 2 := by
      calc
        _ = q.prime * Nat.card C := congrArg (fun p : ℕ => p * Nat.card C) hp.symm
        _ ≤ q.order := hc
        _ = 2 := hq
    have hpos : 0 < Nat.card C := Nat.card_pos
    omega
  have hCbot : C = ⊥ := by
    letI : Subsingleton C := Finite.card_le_one_iff_subsingleton.mp hc1.le
    apply bot_unique
    intro c hcC
    apply Subgroup.mem_bot.mpr
    exact congrArg (fun x : C => x.val) (Subsingleton.elim (⟨c, hcC⟩ : C) 1)
  have h2 : (2 : q.Extension 2) = 0 := by
    simpa only [hp] using (CharP.cast_eq_zero (q.Extension 2) q.prime)
  have hw := radicalQuotientImage_card_le q 1 J hM
  have hw4 : Nat.card W ≤ 4 := by simpa only [hq] using hw
  have hwd : Nat.card W ∣ 16 := by
    have hh := Subgroup.card_subgroup_dvd_card W
    rw [rankThreeVector_card, hq] at hh
    exact hh
  have he : M.index * Nat.card W = 32 * L.index := by
    have hh := rankThree_normalizer_index_mul_layer_cards q M
    change M.index * Nat.card C * Nat.card W =
      q.order * (q.order ^ 2) ^ 2 * L.index at hh
    simpa only [hc1, mul_one, hq] using hh
  have ho : 1 < Nat.card W → 9 ≤ (Nat.card W - 1) * L.index := by
    intro hW
    letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW
    obtain ⟨v, hv⟩ := exists_ne (1 : W)
    have hv1 : v.val ≠ 1 := fun hh => hv (Subtype.ext hh)
    have hv0 : v.val.toAdd ≠ 0 := fun hh => hv1 (Multiplicative.toAdd.injective hh)
    have hiso := radicalTrivialCentralIntersection_image_singular q 1 h2 J hCbot
      v.val v.property
    have horb := quotient_orbit_card_le (unitaryRadicalNormalizerAutHom q 1)
      (fixedRadicalParameterHom q 1) (unitaryRadicalNormalizerVectorAutHom q 1)
      (unitaryRadicalNormalizer_parameter q 1) M v.val v.property hv1
    have hsmall := rankThree_binary_singular_orbit_card q hq v.val.toAdd hv0 hiso
    simpa only [ofAdd_toAdd] using hsmall.trans horb
  exact CentralExtensionBinarySingularIndexNumerics.index_ge_twentyFour
    M.index (Nat.card W) L.index Nat.card_pos hw4 hwd
    (Nat.card_pos (α := unitaryRadicalNormalizer q 1 ⧸ L)) he ho

theorem rankThree_ternary_semidirect_coupled_index (q : CFSG.PrimePower)
    (hq : q.order = 3) (M : Subgroup (rankThreeNormalizerExtension q))
    (hM : ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl) :
    48 ≤ M.index := by
  let J := M.comap SemidirectProduct.inl
  let C := J.comap (centralRadicalHom q 1)
  let W := J.map (fixedRadicalParameterHom q 1)
  let L := M.map SemidirectProduct.rightHom
  have hd := prime_dvd_order q
  rw [hq] at hd
  have hp : q.prime = 3 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_three).mp hd
  have hc := centralParameters_proper_card_mul_prime_le q 1 C (proper_central_preimage q M hM)
  have hw := radicalQuotientImage_card_le q 1 J hM
  have he := rankThree_normalizer_index_mul_layer_cards q M
  have hO : 16 ≤ (q.order ^ 2) ^ 2 := by rw [hq]; decide
  have ho : 1 < Nat.card W → 16 ≤ (Nat.card W - 1) * L.index := by
    intro hW
    letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW
    obtain ⟨v, hv⟩ := exists_ne (1 : W)
    have hv1 : v.val ≠ 1 := fun hh => hv (Subtype.ext hh)
    have hv0 : v.val.toAdd ≠ 0 := fun hh => hv1 (Multiplicative.toAdd.injective hh)
    have horb := quotient_orbit_card_le (unitaryRadicalNormalizerAutHom q 1)
      (fixedRadicalParameterHom q 1) (unitaryRadicalNormalizerVectorAutHom q 1)
      (unitaryRadicalNormalizer_parameter q 1) M v.val v.property hv1
    have hsmall := rankThree_ternary_nonzero_orbit_card q hq v.val.toAdd hv0
    simpa only [ofAdd_toAdd] using hsmall.trans horb
  have hpos : 0 < q.order := by rw [hq]; decide
  have hh := CentralExtensionIsotropicOrbitNumerics.prime_mul_orbit_le_index
    q.prime q.order (q.order ^ 2) M.index (Nat.card C) (Nat.card W) L.index 16
    hpos (pow_pos hpos _) Nat.card_pos Nat.card_pos
    (Nat.card_pos (α := unitaryRadicalNormalizer q 1 ⧸ L)) hc hw he hO ho
  simpa only [hp] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
