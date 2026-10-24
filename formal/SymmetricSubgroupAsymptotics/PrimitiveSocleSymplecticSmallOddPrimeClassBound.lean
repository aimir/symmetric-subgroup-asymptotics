import SymmetricSubgroupAsymptotics.CFSGSymplecticPrimeFieldRankTwoIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOddRankTwoClassBound

/-! The two small odd C2 fields use the same prime-field index-cube
argument and exact field-exponent outer budget. Actual subnormality,
socle factors and both original degree forms are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpOrderUpper
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeC_small_odd_prime
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=3 ∨ q.order=5)
    (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C 2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hpar : q.order=q.prime ∧ q.exponent=1 := by
    rcases hq with h3 | h5
    · have hh := Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
        q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
        (show q.prime^q.exponent=3^1 from h3)
      exact ⟨h3.trans hh.1.symm, hh.2⟩
    · have hh := Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 5)
        q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
        (show q.prime^q.exponent=5^1 from h5)
      exact ⟨h5.trans hh.1.symm, hh.2⟩
  have hTwo : (2 : q.Field) ≠ 0 := by
    intro h
    have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
    · exact q.prime_isPrime.ne_one h1
    · omega
  have hindex := typeC_rankTwo_prime_cube_le_proper_index q hpar.1 hTwo
  have ho : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ 3 := by
    have h := typeC_outer_card_le 2 (by decide) q
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q, hpar.2, mul_one] using h
  have hcc : Nat.card (ConjClasses (CFSG.Models.C 2 q)) ≤ Nat.card (CFSG.Models.C 2 q) :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk (CFSG.Models.C 2 q) _) ConjClasses.mk_surjective
  have hb : 3 ≤ q.order^3 := by rcases hq with hq | hq <;> simp [hq]
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.C 2 q) e
    (q.order^3) hb hindex ?_ ?_ H hH
  · have hcard := typeC_order_le_quadratic_power 2 (by decide) q
    have hc : Nat.card (ConjClasses (CFSG.Models.C 2 q)) ≤ q.order^10 := by
      simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] using hcc.trans hcard
    refine (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans ?_
    rcases hq with h3 | h5
    · rw [h3]; decide
    · rw [h5]; decide
  · obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hi : q.order^3 ≤ ell := (hindex K hK).trans_eq he
    exact (Nat.pow_le_pow_left hi 2).trans
      (typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell).le

theorem NonaffineData.subnormal_class_cube_le_of_typeC_odd_rank_two_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hp : q.prime ≠ 2)
    (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  by_cases hlarge : 7 ≤ q.order
  · exact D.subgroup_class_cube_le_of_typeC_odd_rank_two q hlarge hp e H
  · have hp3 : 3 ≤ q.prime := by have h := q.prime_isPrime.two_le; omega
    have he : q.exponent=1 := by
      by_contra hne
      have he2 : 2 ≤ q.exponent := by have h := q.exponent_pos; omega
      have h9 : 9 ≤ q.order :=
        (Nat.pow_le_pow_left hp3 2).trans
          (Nat.pow_le_pow_right (by omega : 0 < q.prime) he2)
      omega
    have horder : q.order=q.prime := by change q.prime^q.exponent=q.prime; rw [he, pow_one]
    have hsmall : q.order=3 ∨ q.order=5 := by
      obtain ⟨k, hk⟩ := q.prime_isPrime.odd_of_ne_two hp
      omega
    exact D.subnormal_class_cube_le_of_typeC_small_odd_prime q hsmall e H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
