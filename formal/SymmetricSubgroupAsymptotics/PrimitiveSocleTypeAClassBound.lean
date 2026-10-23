import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! All original subgroups satisfy the GM cube at large primitive
degree when the actual simple socle type is the ORIGINAL A model.
Literal proper subgroup images, exact indices, the actual full socle
and its quotient-wreath embedding are retained throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.typeA_simple_order_outer_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^(4*Nat.log 2 K.index+23) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply top_unique
    intro x _
    have hx : e x∈K.map e.toMonoidHom := by rw [ht]; trivial
    obtain ⟨y,hy,he⟩ := hx
    exact (e.injective he) ▸ hy
  have hb := CFSGTypeAProperIndexOrderBudget.typeA_order_mul_outer_le_proper_index_log_power
    r hr q (K.map e.toMonoidHom) hmap
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_typeA
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_index_order_budget K hK hdegree
      (D.typeA_simple_order_outer_budget r hr q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
