import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalDPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBinaryRankFourClassBound

/-! Shared proper-subnormal consumers of the existing split/minus
orthogonal point-radical and binary isometry packets. No new numerical
range or model realization is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGOrthogonalBilinearComponentOrderCube
open OrthogonalPointRadicalOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_model_point_capacity
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b : ℕ) (hb : 32 ≤ b)
    (hi : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hbase : (Nat.card S*Nat.card (Outer S))^3 ≤ 5^(b-1))
    (hs : ∀ ell, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup S := e.symm.isSimpleGroup
  have hlarge : 1024 ≤ Nat.card S := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex S
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 32 ≤ ell := hb.trans ((hi K hK).trans_eq he)
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans
      (Nat.pow_le_pow_left hlo 2)).trans (hs ell hell).le
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    S e b (by omega) hi hbase hlarge H hH hne

private theorem minus_point_cube (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (hq : 2 ≤ q.order) (hwindow : 3 ≤ q.order ∨ 5 ≤ r) :
    q.order^(3*componentExponent r) ≤ 5^(minusIndex q.order r-1) := by
  by_cases hq3 : 3 ≤ q.order
  · exact minus_odd_order_cube q.order r hq3 hr
  · have hq2 : q.order=2 := by omega
    have hr5 : 5 ≤ r := hwindow.resolve_left hq3
    simpa only [hq2] using minus_binary_order_cube r hr5

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeD_point_radical
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hwindow : 3 ≤ q.order ∨ 5 ≤ r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv D.Simple e.toEquiv
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.D r q), K ≠ ⊤ →
      minusIndex q.order r ≤ K.index := by
    intro K hK
    exact (minusIndex_le_split q.order r hq hr).trans
      (typeD_point_radical_le_proper_index r hr q K hK)
  have hbase : (Nat.card (CFSG.Models.D r q)*Nat.card (Outer (CFSG.Models.D r q)))^3 ≤
      5^(minusIndex q.order r-1) := by
    have ho := typeD_component_le_field_power r hr q
    have he : 2*r^2+r+6 ≤ componentExponent r := by unfold componentExponent; omega
    have hp := Nat.pow_le_pow_left
      (ho.trans (Nat.pow_le_pow_right (by omega : 0<q.order) he)) 3
    rw [← pow_mul, Nat.mul_comm (componentExponent r) 3] at hp
    exact hp.trans (minus_point_cube r hr q hq hwindow)
  exact D.proper_subnormal_class_cube_le_of_model_point_capacity
    (CFSG.Models.D r q) e (minusIndex q.order r)
    (minusIndex_ge_thirtyTwo q.order r hq hr hwindow) hindex hbase
    (typeD_leastProperIndex_square_lt_card r q hr) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_twistedD_point_radical
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hwindow : 3 ≤ q.order ∨ 5 ≤ r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.TwistedD r q), K ≠ ⊤ →
      minusIndex q.order r ≤ K.index := by
    intro K hK
    exact typeTwistedD_point_radical_le_proper_index r hr q K hK
  have hbase : (Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q)))^3 ≤
      5^(minusIndex q.order r-1) := by
    have ho := typeTwistedD_component_le_field_power r hr q hnc
    have he : 2*r^2+r+4 ≤ componentExponent r := by unfold componentExponent; omega
    have hp := Nat.pow_le_pow_left
      (ho.trans (Nat.pow_le_pow_right (by omega : 0<q.order) he)) 3
    rw [← pow_mul, Nat.mul_comm (componentExponent r) 3] at hp
    exact hp.trans (minus_point_cube r hr q hq hwindow)
  exact D.proper_subnormal_class_cube_le_of_model_point_capacity
    (CFSG.Models.TwistedD r q) e (minusIndex q.order r)
    (minusIndex_ge_thirtyTwo q.order r hq hr hwindow) hindex hbase
    (typeTwistedD_leastProperIndex_square_lt_card r q hr) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeD_binary_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.D 4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hp : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)
  letI : IsSimpleGroup (CFSG.Models.D 4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D 4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : CharP q.Field 2 := Eq.mp (congrArg (fun p : ℕ => CharP q.Field p) hp.1)
    (inferInstance : CharP q.Field q.prime)
  let eM := CFSGOrthogonalDSerreMatrices.serreProjectiveEquivElementaryProjective q.Field 0
  letI : Finite (CFSGOrthogonalDSerreMatrices.elementaryProjective q.Field 4) :=
    Finite.of_equiv (CFSG.Models.D 4 q) eM.toEquiv
  have hc : Nat.card (ConjClasses (CFSG.Models.D 4 q)) ≤ 1536 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map eM.symm.toMonoidHom)
      (ConjClasses.map_surjective eM.symm.surjective)).trans
        (CFSGOrthogonalDBinaryIsometryClassBound.projective_class_card_le q.Field
          (q.card_field.trans hq))
  have ho : Nat.card (Outer (CFSG.Models.D 4 q)) ≤ 6 := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hp.2,mul_one] using
      typeD_four_binary_outer_card_le q hp.1
  have hi (K : Subgroup (CFSG.Models.D 4 q)) (hK : K ≠ ⊤) : 24 ≤ K.index := by
    have h := typeD_point_radical_le_proper_index 4 (by decide) q K hK
    norm_num [hq] at h
    exact (by decide : 24 ≤ 28).trans h
  have hsquare : 24^2 ≤ Nat.card (CFSG.Models.D 4 q) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.D 4 q)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 24 ≤ ell := (hi K hK).trans_eq he
    exact (Nat.pow_le_pow_left hlo 2).trans
      (typeD_leastProperIndex_square_lt_card 4 q (by decide) ell hell).le
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.D 4 q) e 24 (by decide) hi _ hsquare H hH hne
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
    (by decide : (1536*6)^3 ≤ 5^(24-1))

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeTwistedD_binary_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.TwistedD 4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hp : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)
  letI : IsSimpleGroup (CFSG.Models.TwistedD 4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD 4 q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedD 4 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hc : Nat.card (ConjClasses (CFSG.Models.TwistedD 4 q)) ≤ 3072 :=
    CFSGTwistedDBinaryIsometryClassBound.original_class_card_le q hq
  have ho : Nat.card (Outer (CFSG.Models.TwistedD 4 q)) ≤ 8 := by
    simpa only [hp.2,mul_one] using
      CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent 0 q hnc
  have hi (K : Subgroup (CFSG.Models.TwistedD 4 q)) (hK : K ≠ ⊤) : 24 ≤ K.index := by
    have h := typeTwistedD_point_radical_le_proper_index 4 (by decide) q K hK
    norm_num [hq] at h
    exact h
  have hsquare : 24^2 ≤ Nat.card (CFSG.Models.TwistedD 4 q) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.TwistedD 4 q)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 24 ≤ ell := (hi K hK).trans_eq he
    exact (Nat.pow_le_pow_left hlo 2).trans
      (typeTwistedD_leastProperIndex_square_lt_card 4 q (by decide) ell hell).le
  apply D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.TwistedD 4 q) e 24 (by decide) hi _ hsquare H hH hne
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
    (by decide : (3072*8)^3 ≤ 5^(24-1))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
