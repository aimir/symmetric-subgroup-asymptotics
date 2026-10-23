import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! Every subgroup of the ORIGINAL large-degree primitive group obeys
the class cube bound when its simple component is an actual twisted-D
model. Rank four uses the checked bounded-component tail; higher ranks
use the logarithmic index budget, with the power form handled directly. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGTwistedDProperIndexOrderBudget
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_proper {A B : Type} [Group A] [Group B] (e : A≃*B)
    (K : Subgroup A) (hK : K≠⊤) : K.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

theorem NonaffineData.twistedD_high_simple_order_outer_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 5≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.TwistedD r q) (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^(4*Nat.log 2 K.index+23) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h=>D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hb := typeTwistedD_high_order_mul_outer_le_proper_index_log_power r hr q hn
    (K.map e.toMonoidHom) (map_proper e K hK)
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.twistedD_four_simple_order_outer_budget
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.TwistedD 4 q) (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^34 := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD 4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedD 4 q) :=
    fun h=>D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hb := typeTwistedD_four_order_mul_outer_le_proper_index_power q hn
    (K.map e.toMonoidHom) (map_proper e K hK)
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_twistedD
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.TwistedD r q) (hn : 1024≤Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · by_cases hfour : r=4
    · subst r
      have hc : Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 :=
        (D.twistedD_four_simple_order_outer_budget q e K hK).trans
          (Nat.pow_le_pow_right (by have := K.one_lt_index_of_ne_top hK; omega) (by decide : 34≤66))
      exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree hc hn H
    · exact D.subgroup_class_cube_le_of_index_order_budget K hK hdegree
        (D.twistedD_high_simple_order_outer_budget r (by omega) q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
