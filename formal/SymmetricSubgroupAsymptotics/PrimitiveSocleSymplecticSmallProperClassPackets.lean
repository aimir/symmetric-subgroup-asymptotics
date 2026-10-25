import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticSmallPrimaryClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticSmallOddPrimeClassBound

/-! The actual primary-class and prime-field coupled packets retain
one additional exponent for proper subnormal groups. All finite scalar
inequalities are the existing ordinary packet inequalities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSerreMatrices CFSGSymplecticSharpOrderUpper
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem quotient_class_card_le (K : Type) [Field K] [Finite K] (r : ℕ) :
    Nat.card (ConjClasses (elementaryProjective K r)) ≤
      Nat.card (ConjClasses (elementaryRootGroup K r)) := by
  let f := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K r))
  exact Nat.card_le_card_of_surjective (ConjClasses.map f)
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))

theorem NonaffineData.proper_subnormal_class_cube_le_of_binary_rank_three_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* elementaryProjective q.Field 3)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hpar : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)
  letI : CharP q.Field 2 := by rw [← hpar.1]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 3) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field 3) := Finite.of_equiv D.Simple e.toEquiv
  have hc : Nat.card (ConjClasses (elementaryProjective q.Field 3)) ≤ 96 :=
    (quotient_class_card_le q.Field 3).trans
      (CFSGSymplecticSmallClassBounds.binary_rankThree q.Field (q.card_field.trans hq))
  have ho : Nat.card (Outer (elementaryProjective q.Field 3)) ≤ 3 := by
    have h := CFSGSymplecticPointRootLabels.binary_outer_card_le (K:=q.Field) 2 (by decide)
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hpar.2,mul_one] using h
  have hi (K : Subgroup (elementaryProjective q.Field 3)) (hK : K ≠ ⊤) : 12 ≤ K.index := by
    have h := CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index
      q.Field (q.card_field.trans hq) 3 (by decide) K hK
    norm_num at h
    exact h
  have hsquare : 12^2 ≤ Nat.card (elementaryProjective q.Field 3) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (elementaryProjective q.Field 3)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 12 ≤ ell := (hi K hK).trans_eq he
    have hs := elementary_leastProperIndex_square_lt_card q.Field 2 (by decide)
      (by omega) ell hell
    exact (Nat.pow_le_pow_left hlo 2).trans hs.le
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity
    (elementaryProjective q.Field 3) e 12 (by decide) hi _ hsquare H hH hne
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans (by decide)

theorem NonaffineData.proper_subnormal_class_cube_le_of_four_rank_two_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=4)
    (e : D.Simple ≃* elementaryProjective q.Field 2)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hpar : q.prime=2 ∧ q.exponent=2 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (2 : ℕ)≠0)
      (show q.prime^q.exponent=2^2 from hq)
  letI : CharP q.Field 2 := by rw [← hpar.1]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field 2) := Finite.of_equiv D.Simple e.toEquiv
  have hc : Nat.card (ConjClasses (elementaryProjective q.Field 2)) ≤ 192 :=
    (quotient_class_card_le q.Field 2).trans
      (CFSGSymplecticSmallClassBounds.four_rankTwo q.Field (q.card_field.trans hq))
  have ho : Nat.card (Outer (elementaryProjective q.Field 2)) ≤ 6 := by
    have h := CFSGSymplecticPointRootLabels.binary_outer_card_le (K:=q.Field) 1 (by decide)
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hpar.2] using h
  have hi (K : Subgroup (elementaryProjective q.Field 2)) (hK : K ≠ ⊤) : 18 ≤ K.index := by
    have h := CFSGSymplecticBinaryRankTwoSharpIndex.projective_field_mul_square_sub_one_le_twice_proper_index
      q.Field K hK
    rw [q.card_field,hq] at h
    norm_num at h
    omega
  have hsquare : 18^2 ≤ Nat.card (elementaryProjective q.Field 2) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (elementaryProjective q.Field 2)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 18 ≤ ell := (hi K hK).trans_eq he
    have hs := elementary_leastProperIndex_square_lt_card q.Field 1 (by decide)
      (by rw [q.card_field,hq]; decide) ell hell
    exact (Nat.pow_le_pow_left hlo 2).trans hs.le
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity
    (elementaryProjective q.Field 2) e 18 (by decide) hi _ hsquare H hH hne
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans (by decide)

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_binary_rank_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.C 3 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 3 q) := e.symm.isSimpleGroup
  exact D.proper_subnormal_class_cube_le_of_binary_rank_three_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 2)) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_four_rank_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=4)
    (e : D.Simple ≃* CFSG.Models.C 2 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  exact D.proper_subnormal_class_cube_le_of_four_rank_two_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 1)) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_small_odd_prime
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=3 ∨ q.order=5)
    (e : D.Simple ≃* CFSG.Models.C 2 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C 2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hpar : q.order=q.prime ∧ q.exponent=1 := by
    rcases hq with h3 | h5
    · have hh := Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
        q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
        (show q.prime^q.exponent=3^1 from h3)
      exact ⟨h3.trans hh.1.symm,hh.2⟩
    · have hh := Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 5)
        q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
        (show q.prime^q.exponent=5^1 from h5)
      exact ⟨h5.trans hh.1.symm,hh.2⟩
  have hTwo : (2 : q.Field)≠0 := by
    intro h
    have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
    · exact q.prime_isPrime.ne_one h1
    · omega
  have hindex := typeC_rankTwo_prime_cube_le_proper_index q hpar.1 hTwo
  have ho : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ 3 := by
    have h := typeC_outer_card_le 2 (by decide) q
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hpar.2,mul_one] using h
  have hcc : Nat.card (ConjClasses (CFSG.Models.C 2 q)) ≤ Nat.card (CFSG.Models.C 2 q) :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk (CFSG.Models.C 2 q) _) ConjClasses.mk_surjective
  have hb : 3 ≤ q.order^3 := by rcases hq with hq | hq <;> simp [hq]
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.C 2 q) e (q.order^3) hb hindex ?_ ?_ H hH hne
  · have hcard := typeC_order_le_quadratic_power 2 (by decide) q
    have hc : Nat.card (ConjClasses (CFSG.Models.C 2 q)) ≤ q.order^10 := by
      simpa only [Nat.reducePow,Nat.reduceMul,Nat.reduceAdd] using hcc.trans hcard
    refine (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans ?_
    rcases hq with h3 | h5
    · rw [h3]; decide
    · rw [h5]; decide
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    obtain ⟨K,hK,he⟩ := hell.1
    have hi : q.order^3 ≤ ell := (hindex K hK).trans_eq he
    exact (Nat.pow_le_pow_left hi 2).trans
      (typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell).le

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
