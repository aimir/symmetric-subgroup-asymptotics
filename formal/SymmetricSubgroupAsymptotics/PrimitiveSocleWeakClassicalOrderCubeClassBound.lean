import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGWeakClassicalComponentOrderCube
import SymmetricSubgroupAsymptotics.NoncommutativeProperIndexOrderLower
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Concrete B/C/D/twisted-D parameter tails for the original primitive
socle and original H. Actual component order controls every subgroup H;
the proof does not assert subgroup class monotonicity or strengthen a
root-star dimension. All factor counts and both degree forms are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGWeakClassicalComponentOrderCube WeakClassicalOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_ne_top {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (K : Subgroup S) (hK : K ≠ ⊤) : K.map e.toMonoidHom ≠ ⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

private theorem native_capacity_cube {T : Type} [Group T]
    (D : NonaffineData G X) (e : D.Simple ≃* T) (q t : ℕ) (hq : 2 ≤ q) (ht : 2 ≤ t)
    (hc : Capacity q t)
    (hi : ∀ K : Subgroup T, K ≠ ⊤ → q^t ≤ K.index)
    (hb : (Nat.card T * Nat.card (Outer T))^3 ≤ 5^(q^t-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → q^t ≤ K.index := by
    intro K hK
    have hh := hi (K.map e.toMonoidHom) (map_ne_top e K hK)
    have hidx : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rwa [hidx] at hh
  have hpower : 512 ≤ q^t := capacity_root_power_ge_512 q t hq ht hc
  have hlarge := NoncommutativeProperIndexOrderLower.twice_le_card D.noncommutative (q^t) hindex
  apply D.subgroup_class_cube_le_of_component_order_cube (q^t) (by omega) hindex ?_ (by omega) H
  rw [Nat.card_congr e.toEquiv, outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_typeC_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.C r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_capacity_cube D e q.order (r-1) hq (by omega) hc
    (fun K hK => CFSGReduction.typeC_field_power_le_proper_index r (by omega) q K hK)
    (typeC_component_order_cube r hr q hc) H

theorem NonaffineData.subgroup_class_cube_le_of_typeB_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_capacity_cube D e q.order (r-1) hq (by omega) hc
    (fun K hK => CFSGOrthogonalBOriginalMatrixBounds.typeB_field_power_le_proper_index r (by omega) q K hK)
    (typeB_component_order_cube r hr q hc) H

theorem NonaffineData.subgroup_class_cube_le_of_typeD_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hc : Capacity q.order (r-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_capacity_cube D e q.order (r-1) hq (by omega) hc
    (fun K hK => CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r (by omega) q K hK)
    (typeD_component_order_cube r hr q hc) H

theorem NonaffineData.subgroup_class_cube_le_of_typeTwistedD_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hc : Capacity q.order (r-2)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact native_capacity_cube D e q.order (r-2) hq (by omega) hc
    (fun K hK => CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index r (by omega) q K hK)
    (typeTwistedD_component_order_cube r hr q hn hc) H

theorem NonaffineData.subgroup_class_cube_le_of_typeC_rank_two_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 256 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  have hi : ∀ K : Subgroup D.Simple, K ≠ ⊤ → q.order ≤ K.index := by
    intro K hK
    have hh := typeC_field_power_le_proper_index 2 (by decide) q
      (K.map e.toMonoidHom) (map_ne_top e K hK)
    have hidx : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    simpa only [hidx, Nat.reduceSub, pow_one] using hh
  have hlarge : 1024 ≤ Nat.card D.Simple := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.C 2 q)
    have hlo := (typeC_order_power_le_leastProperIndex 2 (by decide) q ell hell)
    have hs := typeC_leastProperIndex_square_lt_card 2 q (by decide) (by omega) ell hell
    have hl : 256 ≤ ell := hq.trans (by simpa only [Nat.reduceSub, pow_one] using hlo)
    have hp := Nat.pow_le_pow_left hl 2
    norm_num only [Nat.reducePow] at hp
    rw [Nat.card_congr e.toEquiv]
    omega
  apply D.subgroup_class_cube_le_of_component_order_cube q.order (by omega) hi ?_ hlarge H
  rw [Nat.card_congr e.toEquiv, outer_card_congr e]
  exact typeC_rank_two_component_order_cube q hq

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
