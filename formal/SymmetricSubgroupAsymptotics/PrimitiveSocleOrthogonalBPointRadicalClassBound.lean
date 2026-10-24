import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalOrderCubeNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! The actual odd-characteristic type-B point radical supplies the
same proper-index budget for every original socle factor and both degree
forms. No extra characteristic-prime multiplier or subnormality premise
is used. The binary models are handled separately. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGOrthogonalBilinearComponentOrderCube
open OrthogonalPointRadicalOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_typeB_point_radical
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hodd : q.prime ≠ 2) (e : D.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  have hp : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  have hq : 3 ≤ q.order := hp.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.B r q), K ≠ ⊤ →
      oddIndex q.order r ≤ K.index := by
    intro K hK
    exact typeB_point_radical_le_proper_index r hr q hodd K hK
  have hb : 32 ≤ oddIndex q.order r := by
    have ht : 9 ≤ q.order^(r-1) := (by decide : 9 ≤ (3 : ℕ)^2).trans
      ((Nat.pow_le_pow_left hq 2).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
    unfold oddIndex
    have hs : 8 ≤ q.order^(r-1)-1 := by omega
    exact (by decide : 32 ≤ 8*9).trans (Nat.mul_le_mul hs ht)
  have hcube : q.order^(3*componentExponent r) ≤ 5^(oddIndex q.order r-1) :=
    odd_order_cube q.order r hq hr
  have hbase : (Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q)))^3 ≤
      5^(oddIndex q.order r-1) := by
    have ho := typeB_component_le_field_power r hr q
    have he : 2*r^2+3*r+4 ≤ componentExponent r := by unfold componentExponent; omega
    have hpow := Nat.pow_le_pow_left
      (ho.trans (Nat.pow_le_pow_right (by omega : 0 < q.order) he)) 3
    rw [← pow_mul, Nat.mul_comm (componentExponent r) 3] at hpow
    exact hpow.trans hcube
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.B r q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.B r q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hlo : 32 ≤ ell := hb.trans ((hindex K hK).trans_eq he)
    have hs := (typeB_simpleIndexBounds r hr q ell hell).1
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans
      (Nat.pow_le_pow_left hlo 2)).trans hs.le
  refine D.subgroup_class_cube_le_of_component_order_cube (oddIndex q.order r)
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
