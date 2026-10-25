import SymmetricSubgroupAsymptotics.PrimitiveSocleAllFactorProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! Reusable proper-subnormal consumers for literal model order cubes
and class-equation capacities. Both retain the same actual subgroup,
all socle factors and both original degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_model_order_capacity
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hbase : (Nat.card S*Nat.card (Outer S))^3 ≤ 5^(b-1))
    (hlarge : 1024 ≤ Nat.card S)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hi : ∀ K : Subgroup D.Simple, K ≠ ⊤ → b ≤ K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hindex (K.map e.toMonoidHom) hmap
    have he : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rwa [he] at hh
  have hn := D.degree_lower_of_proper_index_lower b hi
  refine D.proper_subnormal_class_cube_le_of_order_index_budget (by omega) ?_ ?_ H hH hne
  · rw [Nat.card_congr e.toEquiv]
    exact hlarge
  · intro K hK
    rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact hbase.trans (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right (hi K hK) 1))

theorem NonaffineData.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b N O : ℕ) (hb : 3 ≤ b)
    (hi : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hc : Nat.card S ≤ N) (ho : Nat.card (Outer S) ≤ O)
    (hs : ∀ ell, LeastProperIndex S ell → ell^2 < Nat.card S)
    (hbudget : ((N/b+1)*O)^3 ≤ 5^(b-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup S := e.symm.isSimpleGroup
  have hcenterless := (isCenterless_congr e).mp
    (centerless_of_nonabelian_simple D.Simple D.noncommutative)
  have hz : Subgroup.center S=⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (hcenterless x (fun y => (Subgroup.mem_center_iff.mp hx y).symm))
  have hclass : Nat.card (ConjClasses S) ≤ N/b+1 :=
    (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one b (by omega) hz hi).trans
      (Nat.add_le_add_right (Nat.div_le_div_right hc) 1)
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity S e b hb hi
    ((Nat.pow_le_pow_left (Nat.mul_le_mul hclass ho) 3).trans hbudget) ?_ H hH hne
  obtain ⟨ell, hell⟩ := exists_leastProperIndex S
  obtain ⟨K, hK, he⟩ := hell.1
  exact (Nat.pow_le_pow_left ((hi K hK).trans_eq he) 2).trans (hs ell hell).le

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
