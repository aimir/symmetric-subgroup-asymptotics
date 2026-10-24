import SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSquareNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! The original odd-characteristic C2 branch is closed uniformly from
field order seven. The actual coupled Heisenberg/SL2 index theorem pays
the checked component order cube, retaining every original socle factor
and both degree forms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_typeC_odd_rank_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 7 ≤ q.order)
    (hp : q.prime ≠ 2) (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hTwo : (2 : q.Field) ≠ 0 := by
    intro h
    have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
    · exact q.prime_isPrime.ne_one h1
    · exact hp h2
  have hindex := typeC_rankTwo_field_square_le_proper_index q hTwo
  have hb : 3 ≤ q.order^2 := (by decide : 3 ≤ 7^2).trans (Nat.pow_le_pow_left hq 2)
  have hbase : (Nat.card (CFSG.Models.C 2 q)*Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤
      5^(q.order^2-1) := by
    have h := Nat.pow_le_pow_left (component_le_field_power 2 (by decide) q) 3
    have he : (q.order^(2*2^2+2+3))^3 = q.order^39 := by rw [← pow_mul]; norm_num
    exact (h.trans_eq he).trans (CFSGSymplecticRankTwoSquareNumerics.order_cube_budget q.order hq)
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.C 2 q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    have hi := typeC_rankTwo_order_square_le_leastProperIndex q hTwo ell hell
    have hs := typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell
    exact ((by decide : 1024 ≤ (7^2)^2).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left hq 2) 2)).trans
        ((Nat.pow_le_pow_left hi 2).trans hs.le)
  refine D.subgroup_class_cube_le_of_component_order_cube (q.order^2) hb ?_ ?_ ?_ H
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    exact (hindex (K.map e.toMonoidHom) hmap).trans_eq hi
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact hbase
  · rw [Nat.card_congr e.toEquiv]
    exact hlarge

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
