import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every subgroup of the original large-degree primitive group obeys
the class cube bound for an actual triality simple component. The
component estimate uses the proved finite Bruhat upper cover. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGTrialityGeckProperIndexOrderBudget
variable {G X:Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_proper {A B:Type} [Group A] [Group B] (e:A≃*B)
    (K:Subgroup A) (hK:K≠⊤) : K.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

theorem NonaffineData.triality_simple_order_outer_budget
    (D:NonaffineData G X) (q:CFSG.PrimePower)
    (e:D.Simple≃*CFSG.Models.TrialityD4 q) (K:Subgroup D.Simple) (hK:K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TrialityD4 q) :=
    fun h=>D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hb := original_order_mul_outer_le_proper_index_power q hn
    (K.map e.toMonoidHom) (map_proper e K hK)
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_triality
    (D:NonaffineData G X) (q:CFSG.PrimePower)
    (e:D.Simple≃*CFSG.Models.TrialityD4 q) (hn:1024≤Nat.card X) (H:Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.triality_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
