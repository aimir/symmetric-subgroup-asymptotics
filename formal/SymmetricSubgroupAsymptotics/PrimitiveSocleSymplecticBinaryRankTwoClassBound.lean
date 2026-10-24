import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSquareNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! The original characteristic-two C2 branch is closed uniformly from
field order eight. The actual Siegel/GL2 annihilator-orbit index theorem
pays the checked component order cube, retaining every original socle
factor, original subgroup, and both degree forms. q=4 remains outside. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_typeC_binary_rank_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 8 ≤ q.order)
    (hp : q.prime = 2) (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  have hindex := typeC_rankTwo_binary_field_square_le_proper_index q hp hq
  have hb : 3 ≤ q.order^2 := (by decide : 3 ≤ 8^2).trans (Nat.pow_le_pow_left hq 2)
  have hbase : (Nat.card (CFSG.Models.C 2 q)*Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤
      5^(q.order^2-1) := by
    have h := Nat.pow_le_pow_left (component_le_field_power 2 (by decide) q) 3
    have he : (q.order^(2*2^2+2+3))^3 = q.order^39 := by rw [← pow_mul]; norm_num
    exact (h.trans_eq he).trans (CFSGSymplecticRankTwoSquareNumerics.order_cube_budget q.order (by omega))
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.C 2 q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    have hi := typeC_rankTwo_binary_order_square_le_leastProperIndex q hp hq ell hell
    have hs := typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell
    exact ((by decide : 1024 ≤ (8^2)^2).trans
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
