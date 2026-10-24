import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The improved actual orthogonal component cubes control EVERY
original subgroup H, all socle factor counts, and both raw degree forms.
The residual alternatives retain the same literal model and field/rank.
No subgroup-class monotonicity or new index bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGOrthogonalBilinearComponentOrderCube OrthogonalBilinearOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_ne_top {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (K : Subgroup S) (hK : K≠⊤) : K.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

private theorem native_bilinear_capacity_cube {T : Type} [Group T]
    (D : NonaffineData G X) (e : D.Simple ≃* T) (q t : ℕ) (hq : 2≤q) (ht : 2≤t)
    (hc : Capacity q t)
    (hi : ∀ K : Subgroup T, K≠⊤ → q^t≤K.index)
    (hb : (Nat.card T*Nat.card (Outer T))^3≤5^(q^t-1))
    (hlarge : 1024≤Nat.card T) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  have hindex : ∀ K : Subgroup D.Simple,K≠⊤ → q^t≤K.index := by
    intro K hK
    have hh := hi (K.map e.toMonoidHom) (map_ne_top e K hK)
    have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rwa [hidx] at hh
  have hpower := root_power_ge_thirtyTwo q t hq ht hc
  apply D.subgroup_class_cube_le_of_component_order_cube (q^t) (by omega) hindex ?_ ?_ H
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact hb
  · rwa [Nat.card_congr e.toEquiv]

theorem NonaffineData.subgroup_class_cube_le_of_typeB_bilinear_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_bilinear_capacity_cube D e q.order (r-1) hq (by omega) hc
    (fun K hK => CFSGOrthogonalBOriginalMatrixBounds.typeB_field_power_le_proper_index r (by omega) q K hK)
    (typeB_component_order_cube r hr q hc)
    (typeB_order_ge_1024_of_star r hr q (root_power_ge_thirtyTwo q.order (r-1) hq (by omega) hc)) H

theorem NonaffineData.subgroup_class_cube_le_of_typeD_bilinear_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_bilinear_capacity_cube D e q.order (r-1) hq (by omega) hc
    (fun K hK => CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r (by omega) q K hK)
    (typeD_component_order_cube r hr q hc)
    (typeD_order_ge_1024_of_star r hr q (root_power_ge_thirtyTwo q.order (r-1) hq (by omega) hc)) H

theorem NonaffineData.subgroup_class_cube_le_of_typeTwistedD_bilinear_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hc : Capacity q.order (r-2)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_bilinear_capacity_cube D e q.order (r-2) hq (by omega) hc
    (fun K hK => CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index r (by omega) q K hK)
    (typeTwistedD_component_order_cube r hr q hn hc)
    (typeTwistedD_order_ge_1024_of_star r hr q (root_power_ge_thirtyTwo q.order (r-2) hq (by omega) hc)) H

theorem NonaffineData.subgroup_class_cube_or_typeB_bilinear_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-1) := by
  by_cases hc : Capacity q.order (r-1)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeB_bilinear_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc)

theorem NonaffineData.subgroup_class_cube_or_typeD_bilinear_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-1) := by
  by_cases hc : Capacity q.order (r-1)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeD_bilinear_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-1) hq (by omega) hc)

theorem NonaffineData.subgroup_class_cube_or_typeTwistedD_bilinear_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨ SmallParameters q.order (r-2) := by
  by_cases hc : Capacity q.order (r-2)
  · exact Or.inl (D.subgroup_class_cube_le_of_typeTwistedD_bilinear_capacity r hr q e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (smallParameters_of_not_capacity q.order (r-2) hq (by omega) hc)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
