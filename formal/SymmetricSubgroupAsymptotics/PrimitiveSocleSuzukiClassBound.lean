import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSuzukiProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual Suzuki simple type satisfies the GM cube for every
subgroup of the ORIGINAL primitive group at degree at least1024,
all factor counts and both actual raw degree forms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.suzuki_simple_order_outer_budget
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^(4*Nat.log 2 K.index+23) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGSuzukiProperIndexOrderBudget.suzuki_order_mul_outer_le_proper_index_seventeen
    m hm (K.map e.toMonoidHom) hmap
  have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hi] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb.trans (Nat.pow_le_pow_right (by have := K.one_lt_index_of_ne_top hK; omega)
    (by omega))

theorem NonaffineData.subgroup_class_cube_le_of_suzuki
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_index_order_budget K hK hdegree
      (D.suzuki_simple_order_outer_budget m hm e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
