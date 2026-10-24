import SymmetricSubgroupAsymptotics.CFSGSymplecticOddHigherRankIndex
import SymmetricSubgroupAsymptotics.SymplecticHigherCoupledIndexNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! Uniform closure of the original odd-characteristic higher-rank C
component capacity. The actual coupled Heisenberg/Sp index bound pays
one shared numerical template. The original socle, all its factors,
both degree forms and the literal subgroup are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_typeC_odd_higher_rank
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hp : q.prime ≠ 2) (e : D.Simple ≃* CFSG.Models.C r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hp3 : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  have hq3 : 3 ≤ q.order := hp3.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hTwo : (2 : q.Field) ≠ 0 := by
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
  have hb32 := SymplecticHigherCoupledIndexNumerics.coupled_index_ge_thirtyTwo
    q.order r hq3 hr
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
      (by omega : r = 2 → q.order ≠ 2) ell hell
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans (Nat.pow_le_pow_left hlo 2)).trans hs.le
  refine D.subgroup_class_cube_le_of_component_order_cube (3*q.order^(2*r-2))
    (by omega) ?_ ?_ ?_ H
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    exact (hindex (K.map e.toMonoidHom) hmap).trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact hbase
  · rw [Nat.card_congr e.toEquiv]
    exact hlarge

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
