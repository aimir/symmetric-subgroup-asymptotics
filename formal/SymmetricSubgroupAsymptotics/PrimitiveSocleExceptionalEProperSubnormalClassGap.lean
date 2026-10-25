import SymmetricSubgroupAsymptotics.PrimitiveSocleLargeIndexOrderProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalAllDegreesClassBound

/-! The actual E6/E7/E8 index lower bounds and order-at-index packets
discharge the shared proper-subnormal reserve. All factor counts and
both primitive degree forms are preserved, at every field parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem index_lower_transfer {T : Type} [Group T]
    (D : NonaffineData G X) (e : D.Simple ≃* T) (n : ℕ)
    (hindex : ∀ L : Subgroup T, L ≠ ⊤ → n ≤ L.index)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤) : n ≤ K.index := by
  have hmap : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hh := hindex (K.map e.toMonoidHom) hmap
  have hi : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  rwa [hi] at hh

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeE6
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E6 q)
    (hdegree : 2 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_large_index_order_budget hdegree _
    (D.e6_simple_order_outer_budget q e) H hH hne
  intro K hK
  exact (by decide : 1024 ≤ 2048).trans
    (index_lower_transfer D e 2048 (typeE6_2048_le_index q) K hK)

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeE7
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E7 q)
    (hdegree : 2 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_large_index_order_budget hdegree _
    (D.e7_simple_order_outer_budget q e) H hH hne
  intro K hK
  exact (by decide : 1024 ≤ 2048).trans
    (index_lower_transfer D e 2048 (typeE7_2048_le_index q) K hK)

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeE8
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E8 q)
    (hdegree : 2 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_large_index_order_budget hdegree _
    (D.e8_simple_order_outer_budget q e) H hH hne
  intro K hK
  exact (by decide : 1024 ≤ 2048).trans
    (index_lower_transfer D e 2048 (typeE8_2048_le_index q) K hK)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
