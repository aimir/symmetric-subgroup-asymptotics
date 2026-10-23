import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
import SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarIndex
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual E6/E7/E8 simple components satisfy the large primitive
class cube bound for every original subgroup and both raw degree forms.
All original order, outer-order and proper-index inputs are proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGExceptionalOriginalComponentUpper CFSGReduction
variable {G X:Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem mapped_proper {A B:Type} [Group A] [Group B] (e:A≃*B)
    (K:Subgroup A) (hK:K≠⊤) : K.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

private theorem component_budget {T:Type} [Group T] (D:NonaffineData G X)
    (e:D.Simple≃*T) (K:Subgroup D.Simple) (hK:K≠⊤) (q:CFSG.PrimePower)
    (d a:ℕ) (ha:a≤d*66)
    (hindex:q.order^d≤(K.map e.toMonoidHom).index)
    (horder:Nat.card T*Nat.card (Outer T)≤q.order^a) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 := by
  have hq:1≤q.order:=q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime) |>.trans' (by omega)
  have hi:(K.map e.toMonoidHom).index=K.index:=K.index_map_equiv e
  rw [hi] at hindex
  rw [Nat.card_congr e.toEquiv,outer_card_congr e]
  exact horder.trans ((Nat.pow_le_pow_right hq ha).trans
    ((pow_mul q.order d 66).trans_le (Nat.pow_le_pow_left hindex 66)))

theorem NonaffineData.e6_simple_order_outer_budget
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E6 q)
    (K:Subgroup D.Simple) (hK:K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 := by
  letI : IsSimpleGroup (CFSG.Models.E6 q):=e.symm.isSimpleGroup
  have hn:¬IsMulCommutative (CFSG.Models.E6 q):=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  exact component_budget D e K hK q 2 129 (by decide)
    (typeE6_field_square_le_index q (K.map e.toMonoidHom) (mapped_proper e K hK))
    (E6_order_mul_outer_le q hn)

theorem NonaffineData.subgroup_class_cube_le_of_typeE6
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E6 q)
    (hn:1024≤Nat.card X) (H:Subgroup G) : Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.e6_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

theorem NonaffineData.e7_simple_order_outer_budget
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E7 q)
    (K:Subgroup D.Simple) (hK:K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 := by
  letI : IsSimpleGroup (CFSG.Models.E7 q):=e.symm.isSimpleGroup
  have hn:¬IsMulCommutative (CFSG.Models.E7 q):=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  exact component_budget D e K hK q 3 192 (by decide)
    (typeE7_field_cube_le_index q (K.map e.toMonoidHom) (mapped_proper e K hK))
    (E7_order_mul_outer_le q hn)

theorem NonaffineData.subgroup_class_cube_le_of_typeE7
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E7 q)
    (hn:1024≤Nat.card X) (H:Subgroup G) : Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.e7_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

theorem NonaffineData.e8_simple_order_outer_budget
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E8 q)
    (K:Subgroup D.Simple) (hK:K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple)≤K.index^66 := by
  letI : IsSimpleGroup (CFSG.Models.E8 q):=e.symm.isSimpleGroup
  have hn:¬IsMulCommutative (CFSG.Models.E8 q):=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  exact component_budget D e K hK q 5 323 (by decide)
    (typeE8_field_fifth_le_index q (K.map e.toMonoidHom) (mapped_proper e K hK))
    (E8_order_mul_outer_le q hn)

theorem NonaffineData.subgroup_class_cube_le_of_typeE8
    (D:NonaffineData G X) (q:CFSG.PrimePower) (e:D.Simple≃*CFSG.Models.E8 q)
    (hn:1024≤Nat.card X) (H:Subgroup G) : Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.e8_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
