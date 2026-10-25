import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOddHigherRankClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryRankTwoClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOddRankTwoClassBound

/-! Existing coupled symplectic order capacities pay the same proper
subnormal reserve. The original C model and actual index remain fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_odd_higher_rank
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hp : q.prime≠2) (e : D.Simple ≃* CFSG.Models.C r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C r q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hp3 : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  have hq3 : 3 ≤ q.order := hp3.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hTwo : (2 : q.Field)≠0 := by
    intro h
    have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
    · exact q.prime_isPrime.ne_one h1
    · exact hp h2
  have hindex : ∀ K : Subgroup (CFSG.Models.C r q), K ≠ ⊤ →
      3*q.order^(2*r-2) ≤ K.index := by
    intro K hK
    exact (Nat.mul_le_mul_right _ hp3).trans
      (typeC_odd_prime_mul_field_power_le_proper_index r hr q hTwo K hK)
  have hb32 := SymplecticHigherCoupledIndexNumerics.coupled_index_ge_thirtyTwo q.order r hq3 hr
  have hbase : (Nat.card (CFSG.Models.C r q)*Nat.card (Outer (CFSG.Models.C r q)))^3 ≤
      5^(3*q.order^(2*r-2)-1) := by
    have h := Nat.pow_le_pow_left (component_le_field_power r (by omega) q) 3
    rw [← pow_mul, Nat.mul_comm (2*r^2+r+3) 3] at h
    exact h.trans (SymplecticHigherCoupledIndexNumerics.component_order_cube q.order r hq3 hr)
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.C r q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C r q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hlo : 32 ≤ ell := hb32.trans ((hindex K hK).trans_eq he)
    have hs := typeC_leastProperIndex_square_lt_card r q (by omega)
      (by omega : r=2 → q.order≠2) ell hell
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans (Nat.pow_le_pow_left hlo 2)).trans hs.le
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.C r q) e (3*q.order^(2*r-2)) (by omega) hindex hbase hlarge H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_rank_two_order_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (hfield : (q.prime≠2 ∧ 7 ≤ q.order) ∨ (q.prime=2 ∧ 8 ≤ q.order))
    (e : D.Simple ≃* CFSG.Models.C 2 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C 2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hq : 7 ≤ q.order := by rcases hfield with h | h <;> omega
  have hindex : ∀ K : Subgroup (CFSG.Models.C 2 q), K ≠ ⊤ → q.order^2 ≤ K.index := by
    rcases hfield with ⟨hp, hlo⟩ | ⟨hp, hlo⟩
    · have hTwo : (2 : q.Field)≠0 := by
        intro h
        have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
        · exact q.prime_isPrime.ne_one h1
        · exact hp h2
      exact typeC_rankTwo_field_square_le_proper_index q hTwo
    · exact typeC_rankTwo_binary_field_square_le_proper_index q hp hlo
  have hb : 3 ≤ q.order^2 := (by decide : 3 ≤ 7^2).trans (Nat.pow_le_pow_left hq 2)
  have hbase : (Nat.card (CFSG.Models.C 2 q)*Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤
      5^(q.order^2-1) := by
    have h := Nat.pow_le_pow_left (component_le_field_power 2 (by decide) q) 3
    have he : (q.order^(2*2^2+2+3))^3=q.order^39 := by rw [← pow_mul]; norm_num
    exact (h.trans_eq he).trans (CFSGSymplecticRankTwoSquareNumerics.order_cube_budget q.order hq)
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.C 2 q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hi : q.order^2 ≤ ell := (hindex K hK).trans_eq he
    have hs := typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell
    exact ((by decide : 1024 ≤ (7^2)^2).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left hq 2) 2)).trans
        ((Nat.pow_le_pow_left hi 2).trans hs.le)
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.C 2 q) e (q.order^2) hb hindex hbase hlarge H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
