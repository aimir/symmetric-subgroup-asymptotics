import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A reusable same-model consumer. Concrete class, outer and index
budgets are transported along the original displayed simple-model
equivalence; both raw degree forms and subnormality remain literal. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_model_capacity
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup S, K≠⊤ → b ≤ K.index)
    (hbase : (Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 5^(b-1))
    (hsquare : b^2 ≤ Nat.card S) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  refine D.subnormal_class_cube_le_of_component_class_cube_square b hb ?_ ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have h := hindex (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at h
    exact h
  · have hc : Nat.card (ConjClasses D.Simple) ≤ Nat.card (ConjClasses S) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    rw [outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) 3).trans hbase
  · rw [Nat.card_congr e.toEquiv]
    exact hsquare

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
