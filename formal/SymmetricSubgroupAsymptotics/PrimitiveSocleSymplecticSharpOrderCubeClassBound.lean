import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual-C sharp order tails for every original subgroup and both raw
socle degree forms. Residual parameter rows are explicit and smaller
than the shared matrix-space route; no subgroup/action census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics

def SmallParameters (q t : ℕ) : Prop :=
  (t=2 ∧ q≤10) ∨ (t=3 ∧ q≤4) ∨ (t=4 ∧ q≤3) ∨ (5≤t ∧ t≤7 ∧ q=2)

theorem smallParameters_of_not_capacity (q t : ℕ) (hq : 2≤q) (ht : 2≤t)
    (hc : ¬Capacity q t) : SmallParameters q t := by
  unfold Capacity at hc
  unfold SmallParameters
  omega

end SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSharpComponentOrderCube SymplecticSharpOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem sharp_index {S : Type} [Group S]
    (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.C r q)]
    (e : S ≃* CFSG.Models.C r q) (K : Subgroup S) (hK : K≠⊤) :
    q.order^(r-1)≤K.index := by
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := typeC_field_power_le_proper_index r hr q (K.map e.toMonoidHom) hmap
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rwa [hidx] at hi

theorem NonaffineData.subgroup_class_cube_le_of_typeC_sharp_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.C r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hstar := root_power_ge_thirtyTwo q.order (r-1) hq (by omega) hc
  apply D.subgroup_class_cube_le_of_component_order_cube (q.order^(r-1)) (by omega)
    (fun K hK => sharp_index r (by omega) q e K hK) ?_ ?_ H
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact component_order_cube r hr q hc
  · rw [Nat.card_congr e.toEquiv]
    exact order_ge_1024_of_star r (by omega) q hstar

theorem NonaffineData.subgroup_class_cube_le_of_typeC_rank_two_sharp_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 128≤q.order)
    (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  have hi : ∀ K : Subgroup D.Simple,K≠⊤ → q.order≤K.index := by
    intro K hK
    simpa only [Nat.reduceSub,pow_one] using sharp_index 2 (by decide) q e K hK
  apply D.subgroup_class_cube_le_of_component_order_cube q.order (by omega) hi ?_ ?_ H
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact rank_two_component_order_cube q hq
  · rw [Nat.card_congr e.toEquiv]
    exact order_ge_1024_of_star 2 (by decide) q (by simpa only [Nat.reduceSub,pow_one] using (show 32≤q.order by omega))

theorem NonaffineData.subgroup_class_cube_or_typeC_sharp_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.C r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=2 ∧ q.order≤127) ∨ (3≤r ∧ SmallParameters q.order (r-1)) := by
  by_cases htwo : r=2
  · subst r
    by_cases hq : 128≤q.order
    · exact Or.inl (D.subgroup_class_cube_le_of_typeC_rank_two_sharp_capacity q hq e H)
    · exact Or.inr (Or.inl ⟨rfl,by omega⟩)
  · by_cases hc : Capacity q.order (r-1)
    · exact Or.inl (D.subgroup_class_cube_le_of_typeC_sharp_capacity r (by omega) q e hc H)
    · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
        (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
      exact Or.inr (Or.inr ⟨by omega,
        smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc⟩)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
