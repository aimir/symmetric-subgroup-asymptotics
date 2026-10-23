import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! The actual type-D simple socle gives the large-degree all-subgroup
class cube bound. Both index and power degree forms use the SAME full
socle/quotient embedding of the original primitive group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.orthogonalD_simple_order_outer_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.D r q) (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^(4*Nat.log 2 K.index+23) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGOrthogonalDProperIndexOrderBudget.typeD_order_mul_outer_le_proper_index_log_power
    r hr q (K.map e.toMonoidHom) hmap
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_orthogonalD
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.D r q) (hn : 1024≤Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_index_order_budget K hK hdegree
      (D.orthogonalD_simple_order_outer_budget r hr q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
